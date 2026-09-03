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


/-- The head of an application spine (`Lean.Expr.getAppFn`).

Moved up from `Theory/Inductive/Restore.lean` (its lemmas stayed there): `VInductDecl'.uniformOcc?`
has to be nameable *here*, because `VIndField.WF.pos`'s `some` branch now mentions it. -/
def spineFn : VExpr → VExpr
  | .app f _ => f.spineFn
  | e => e

@[simp] theorem spineFn_app {f a : VExpr} : (VExpr.app f a).spineFn = f.spineFn := rfl
@[simp] theorem spineFn_const {c : Name} {ls : List VLevel} :
    (VExpr.const c ls).spineFn = .const c ls := rfl

/-- The argument spine of an application, left to right. -/
def spineArgs : VExpr → List VExpr
  | .app f a => f.spineArgs ++ [a]
  | _ => []

theorem spineArgs_mkApp : ∀ (as : List VExpr) (f : VExpr),
    (mkApp f as).spineArgs = f.spineArgs ++ as
  | [], f => by rw [mkApp, List.append_nil]
  | a :: as, f => by
    rw [mkApp, spineArgs_mkApp as, spineArgs, List.append_assoc]
    rfl

@[simp] theorem spineArgs_const {c : Name} {ls : List VLevel} :
    (VExpr.const c ls).spineArgs = [] := rfl
/-- Boolean twin of `NoConsts`, so that the occurrence check is a *decision*.

`VExpr.NoConsts` is `Prop`-valued by design, and until now it had no `Decidable` instance at all
-- which is why `Theory/Inductive/StoredIota.lean`'s `MRWit.mr_redex_noK` says "not `decide`".
The instance below is what lets F7's residual clause be discharged by `decide` at a concrete
block.

`MRedex.TQWit.hasConstB` (`Theory/Inductive/IndexedNested.lean` §8.6) is left alone: different
namespace, and it is quantified over an arbitrary `K` rather than over `D.blockNames`. -/
def hasConstB (S : List Name) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const c _ => decide (c ∈ S)
  | .app a b | .lam a b | .forallE a b => hasConstB S a || hasConstB S b

theorem hasConstB_eq_false_iff {S : List Name} :
    ∀ {e : VExpr}, hasConstB S e = false ↔ NoConsts S e
  | .bvar _ | .sort _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | .const c _ => by simp [hasConstB, NoConsts]
  | .app a b | .lam a b | .forallE a b => by
    show (hasConstB S a || hasConstB S b) = false ↔ (NoConsts S a ∧ NoConsts S b)
    rw [Bool.or_eq_false_iff]
    exact and_congr hasConstB_eq_false_iff hasConstB_eq_false_iff

instance decidableNoConsts (S : List Name) (e : VExpr) : Decidable (NoConsts S e) :=
  decidable_of_iff _ hasConstB_eq_false_iff

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

/-! ## The uniform-occurrence trigger (moved up from `Theory/Inductive/Restore.lean`)

`VIndField.WF.pos`'s `some` branch constrains the residual of a *stored* uniform occurrence
(F7's residual clause, `ResidualClean` below), so the trigger has to be nameable here.  Only
the four definitions are here; every lemma about them stayed in `Restore.lean`, which is where
their consumers are. -/

/-! The trigger is a *decision*, so `VExpr` needs decidable equality. -/
deriving instance DecidableEq for VLevel
deriving instance DecidableEq for VExpr

namespace VInductDecl'

/-- `memberIdxFrom ms n i`: the position of `n` in `ms`, offset by `i`. -/
def memberIdxFrom : List Name → Name → Nat → Option Nat
  | [], _, _ => none
  | m :: ms, n, i => if m = n then some i else memberIdxFrom ms n (i+1)

/-- Which member of the block the name `n` is, if any. -/
def memberIdx (D : VInductDecl') (n : Name) : Option Nat := memberIdxFrom D.blockNames n 0

/-- **The trigger.**  Is `e`, sitting `k` binders above the block's parameter telescope, a
*uniform* occurrence `I_j.{D.ownLvls} (bvars k D.np ++ π)` of a block member?  If so, its
member index and the residual arguments `π`. -/
def uniformOcc? (D : VInductDecl') (k : Nat) (e : VExpr) : Option (Nat × List VExpr) :=
  match e.spineFn with
  | .const n ls =>
    match D.memberIdx n with
    | some j =>
      if ls = D.ownLvls ∧ e.spineArgs.take D.np = bvars k D.np then
        some (j, e.spineArgs.drop D.np)
      else none
    | none => none
  | _ => none

/-- **F7's residual clause** (`docs/audit-f7-radius.md` §4).  If the *stored* expression `e`,
read at depth `k`, is itself a uniform occurrence of a block member, then the residual
arguments the trigger reports are block-free.

This is the abstract counterpart of `isValidIndAppIdx`'s residual scan
(`Lean4Lean/Inductive/Add.lean`:299-345), which applies `hasIndOcc` to each residual argument
**purely syntactically**; `checkPositivity`'s leading `whnf` is head-only, and at a firing
trigger the head is an `inductInfo` constant, which has no unfolding rules, so the `whnf` is the
identity there and the two scans coincide.

**Conditional on the trigger, deliberately.**  When `e` is `.lam`- or `.forallE`-headed the
trigger does not fire and the clause is *vacuous*, not merely satisfied.  That is what keeps it
strictly weaker than `CGMGuard.cgmSynPos` (`Verify/Inductive/CanonGapMeasure.lean` §3, which
deletes the head `whnf` and therefore rejects the auxiliary blocks `ElimNestedInductive.run`
builds for `Lean.Json` and `Lean.PrefixTreeNode`), and it is why the clause does *not* constrain
`r.binders` or a stored pi domain.  See `docs/handoff-iota-stored.md`. -/
def ResidualClean (D : VInductDecl') (k : Nat) (e : VExpr) : Prop :=
  ∀ j rest, D.uniformOcc? k e = some (j, rest) → ∀ a ∈ rest, D.NoBlock a

instance decidableNoBlock (D : VInductDecl') (e : VExpr) : Decidable (D.NoBlock e) :=
  VExpr.decidableNoConsts _ _

/-- The clause is vacuous where the trigger does not fire. -/
theorem residualClean_of_uniformOcc_none {D : VInductDecl'} {k : Nat} {e : VExpr}
    (h : D.uniformOcc? k e = none) : D.ResidualClean k e := by
  intro j rest h'; rw [h] at h'; exact absurd h' nofun

/-- …and it is exactly the residual condition where it does. -/
theorem residualClean_of_uniformOcc_some {D : VInductDecl'} {k : Nat} {e : VExpr}
    {j : Nat} {rest : List VExpr} (h : D.uniformOcc? k e = some (j, rest))
    (hr : ∀ a ∈ rest, D.NoBlock a) : D.ResidualClean k e := by
  intro j' rest' h'
  rw [h] at h'
  have : rest = rest' := congrArg Prod.snd (Option.some.inj h')
  exact this ▸ hr

/-- `ResidualClean` is a decision: at a concrete block every producer discharges it by
`decide`. -/
instance decidableResidualClean (D : VInductDecl') (k : Nat) (e : VExpr) :
    Decidable (D.ResidualClean k e) :=
  match h : D.uniformOcc? k e with
  | none => isTrue (residualClean_of_uniformOcc_none h)
  | some (_, rest) =>
    if hr : ∀ a ∈ rest, D.NoBlock a then
      isTrue (residualClean_of_uniformOcc_some h hr)
    else
      isFalse fun H => hr (H _ rest h)

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

/-- Move a `HasArgs` derivation along a definitional context conversion.

**Single home.** This was declared independently in `Theory/Typing/PatternRules.lean` and in
`Verify/Typing/DefEqCtx.lean` with byte-identical statements, which made those two modules
**un-importable together** — invisible to `lake build`, because nothing imported both, and it
broke `scripts/sorry-census.lean` and `scripts/dup-names.lean` outright when `Experimental/
ConeJoin.lean` finally pulled in both. Fourth occurrence of that class in one session. It lives
here, beside `HasArgs` itself, which every consumer already imports. -/
theorem VEnv.HasArgs.defeqDFC {env : VEnv} {U : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    (henv : env.Ordered) (W : VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    ∀ {As as : List VExpr}, env.HasArgs U Γ₁ As as → env.HasArgs U Γ₂ As as
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (h1.defeqDFC henv W) (h2.defeqDFC henv W)


/-- `IsDefEqU` refined to say the two sides are equal **as types**.

Stronger than `IsDefEqU`, and it is what the refinement naturally produces: the kernel
walks a pi-spine with `whnf` and `ensureSort`, and each step is a `forallEDF`/`sortDF`
congruence, all of which are typed at a sort.  Going back from `IsDefEqU` would need
`IsDefEqU.of_l`, which lives in `Typing/UniqueTyping.lean` -- downstream of the
injectivity stream and of `VEnv.WF`, hence of `addInduct_WF` itself.  Recording the sort
here keeps the inductive spec out of that cycle. -/
def VEnv.IsDefEqType (env : VEnv) (U : Nat) (Γ : List VExpr) (A B : VExpr) : Prop :=
  ∃ u, env.IsDefEq U Γ A B (.sort u)


/-- **A recursive field's binders `ξ` may not mention an earlier *recursive* field.**

`pre` is the fields before this one in declaration order (`C.fields.take i` at the only call
site, so `pre.length = i`).  The context of field `i` is
`(pre.map (·.type)).reverse ++ D.params.reverse`, so field `i'` sits at de Bruijn index `t`
where `i' + 1 + t = i`, and binder `k` of `ξ` lives `k` binders deeper — hence `k + t`.

The index is carried as `t` *plus the equation*, not as `i - 1 - i'`, per note 0b of
`Theory/Inductive/Lemmas.lean`: this way a caller meets an `omega` goal rather than a
truncated-subtraction normal form.

## Why the model needs it

The set model's `Pos q a` is the disjoint union, over the constructor's recursive fields, of
`⟦r.binders⟧` — and it is what *types* the recursive filler `f`, so it is a function of
`(q, a)` alone and structurally cannot receive `f`.  Evaluating `⟦r.binders⟧` therefore has
the parameters and the *non-recursive* earlier fields available and nothing else.

Both alternatives were measured and both fail.  Putting the recursive fillers into `a`
breaks `fld_det`, which `Ind_subsingleton` uses to pin `a` from the result index before
pinning `f` by the rank induction; the family that kills is **`Acc`**, a large-eliminating
subsingleton with a recursive field, whose eliminator is not optional.  And weakening `Pos`
to a superset computable without `f` injects junk positions, because the dependence is on
the *values* rather than on an approximation.

## What it does not restrict

Only `binders`.  `r.args` are evaluated where `f` is in scope, so they are untouched — and
`VIndField.WF.pos`'s `none` branch stays exactly as it was, which `docs/model-interface.md`
§2 requires.

The clause is **vacuous for `Acc`**: its recursive field's `ξ = [α, r y x]` mentions only
`x`, the earlier *non*-recursive field.  It is vacuous for every constructor with at most
one recursive field, which is every witness in `DeclExamples.lean`. -/
def VIndRecArg.BindersIndep (r : VIndRecArg) (pre : List VIndField) (i : Nat) : Prop :=
  ∀ (i' t : Nat) (F' : VIndField), pre[i']? = some F' → F'.recArg.isSome →
    i' + 1 + t = i → ∀ (k : Nat) (B : VExpr), r.binders[k]? = some B → B.Skips 1 (k + t)

/-- Well-formedness of one constructor field.  `Γ` is
`((C.fields.take i).map (·.type)).reverse ++ D.params.reverse`, the context of field `i`, and
`pre` is `C.fields.take i` — the fields that context is built from.  `pre` carries what `Γ`
erases: which of the earlier fields are *recursive*, which `binders_indep` needs. -/
structure VIndField.WF (env : VEnv) (D : VInductDecl') (pre : List VIndField)
    (Γ : List VExpr) (i : Nat) (F : VIndField) : Prop where
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
      env.IsDefEqType D.uvars Γ F.type (r.canonType D i) ∧
      -- **F7's residual clause** (ruling 159e; `docs/audit-f7-radius.md` §4).  The conjuncts
      -- above constrain `r.binders` and `r.args` — the *canonical* data — and the last one ties
      -- `F.type` to `r.canonType D i` only *definitionally*.  So without this clause the spec
      -- admits a **stored** type that is itself a uniform occurrence `I_j params π` whose
      -- residual `π` mentions the block, provided `π` is defeq to a block-free `r.args`
      -- (`MRedex.TQWit.tqHostile`, `Theory/Inductive/IndexedNested.lean` §8).  Lean's kernel
      -- rejects exactly that: `isValidIndAppIdx` (`Lean4Lean/Inductive/Add.lean`:299-345) scans
      -- the residual arguments with `hasIndOcc` **syntactically**, and `checkPositivity`'s
      -- leading `whnf` is head-only, hence the identity at a firing trigger.
      --
      -- The depth is `r.binders.length + i`, the depth `VIndRecArg.canonResult` itself uses, so
      -- the clause compares the stored expression against the canonical *result* at the same
      -- de Bruijn offset.  It is conditional on the trigger, hence **vacuous** whenever the
      -- stored type is `.lam`- or `.forallE`-headed — which is what keeps it strictly weaker
      -- than `CGMGuard.cgmSynPos` and why it constrains neither `r.binders` nor a stored pi
      -- domain (`VIndRecArg.exists_indep` needs that freedom; see `docs/handoff-iota-stored.md`).
      D.ResidualClean (r.binders.length + i) F.type
  /-- **The recorded `ξ` is independent of the earlier recursive fields**
  (`VIndRecArg.BindersIndep`).

  *Recorded, not derived*, in the same style as `pos`'s index clause and
  `VIndCtor.WF.args_ty`: the kernel performs no such check, so nothing in the refinement
  hands this over for free.  What discharges it is that `ξ` is only required to be
  *definitionally* the stored binder — see `VIndRecArg.exists_indep` below, which is stated
  and open. -/
  binders_indep : ∀ r, F.recArg = some r → r.BindersIndep pre i

/-- **Discharge obligation for `VIndField.WF.binders_indep` — stated, not proved.**

The clause is not something the kernel checks, so it must be *arranged* by whoever builds the
`VIndRecArg`.  That is possible because `binders` is only required to be definitionally the
stored binder telescope (`pos`'s last conjunct is an `IsDefEqType`, not an equation), so a
binder that mentions an earlier recursive field may be replaced by a defeq one that does not.

**What the conclusion has to carry, and why the first version of it did not**
(`docs/handoff-recargup.md`; `Theory/Inductive/RecArgIndep.lean` §6).  The obligation exists to
license exactly one substitution: replace `r` by `r'` inside `pos`'s `some` branch.  Three of
that branch's nine conjuncts — `OnCtx (ξ.reverse ++ Γ)`, the typing of `canonResult`, and the
`HasArgs` derivation for the index arguments — are stated *in the binder telescope's own
context*, so they have to be re-derived in the **new** telescope's context.  A bare
`IsDefEqType Γ F.type (r'.canonType D i)` does not do that: extracting an entrywise relation
between `ξ` and `ξ'` from a conversion between two `mkPi`s is `IsDefEqU.forallE_inv`, the very
statement this hole is waiting on, so the weaker conclusion left its consumer where it started.
The **last conjunct is the repair**: `env.TeleDefEq D.uvars Γ r.binders r'.binders`, the two
binder telescopes related *entrywise, each entry in the context it lives in*
(`VEnv.TeleDefEq`, `Theory/Typing/Lemmas.lean`).  That is what a proof which actually moves a
binder builds anyway, and it is what the three context-relative clauses can be transported
along without any pi-injectivity:

* `VEnv.IsDefEqCtx env D.uvars Γ (ξ.reverse ++ Γ) (ξ'.reverse ++ Γ)`, which moves all three
  of them (`IsDefEq.defeqDFC` and friends), is `RecArgIndep.teleDefEq_isDefEqCtx` applied to
  this conjunct and `hOn`;
* `IsDefEqType Γ (r.canonType D i) (r'.canonType D i)`, the telescope congruence, is
  `VEnv.IsDefEq.mkPi_congrU` applied to it, `hOn`, and `pos`'s own `canonResult` typing.

Both of those were *separate conjuncts* of this statement between 2026-09-03 morning and this
edit, for a layering reason that no longer holds: `VEnv.TeleDefEq` used to live in
`Theory/Typing/ConstSubstNested.lean`, which transitively imports this file, so it could not be
named here.  It now lives in `Theory/Typing/Lemmas.lean`, which this file imports
(`docs/handoff-telemove.md`), and `RecArgIndep.indepGoalPair_of_indepGoal` machine-checks that
the pair is recovered — so replacing them by the `TeleDefEq` loses nothing and is strictly
stronger.

The `F.type` conversion `IsDefEqType Γ F.type (r'.canonType D i)` is kept as its own conjunct
rather than left to be composed out of `hdefeq` and the telescope congruence, because composing
two `IsDefEqType`s is sort uniqueness (`VEnv.SortUniq`) — this hole's **second** price, which
its first docstring did not name.  `Theory/Inductive/Lemmas.lean`'s `IsDefEqType` section has no
`trans` for that reason; `RecArgIndep.isDefEqType_trans_of_sortUniq` is the composition and
where the charge is spent.  Keeping it separate is what makes the *consumer* free of it:
`RecArgIndep.posSome_transport_of_indepGoal` takes no `SortUniq` hypothesis at all (the
unused-variable linter is the witness), so the whole sort-uniqueness charge sits on whoever
discharges this `sorry`, and none of it on whoever uses it.

The first six conjuncts are the original conclusion verbatim, so this statement is a **strict
strengthening**: a consumer of the old one needs nothing new, and needs no `SortUniq` to
recover it.

**Why the hypotheses are what they are.**  `hstage` says `env` is the environment
`addIndTypes` just produced — the environment `VIndCtor.WF`, hence this obligation, is checked
in (`VInductDecl'.WF.ctors`) — and it is *load-bearing*, not decoration: without it the
statement has a candidate counterexample at a hand-built `VEnv.WF` environment
(`RecArgIndep.rai_hyps` with `RecArgIndep.not_bindersIndep_raiRec1`), and what makes that
witness reachable is precisely a declared constant whose type mentions the block
(`RecArgIndep.raiCiP_type_hasBlock`).  A staged environment cannot hold one, because the
block's constants were added last.  `hpre` is the `VIndField.WF` of the *earlier* fields, which
the argument below uses to rule out an earlier field of type `(∀ ξ₀, I p π₀) → Sort u`; it makes
the obligation an **induction on the field index**, which is how `VIndCtor.WF.fields` has to be
proved anyway (there `pre = C.fields.take i`, so `hpre` is the induction hypothesis).  `hOn` is
`pos`'s own `OnCtx` conjunct, so a caller holds it before it calls, and it is what turns the
last conjunct into the two context-relative facts above.  The *degenerate* witness `r' = r`
costs nothing under this conclusion and does not even need `hOn`: the last conjunct is then
`VEnv.TeleDefEq.refl`, which carries no typing at all.  See
`RecArgIndep.exists_indep_of_pre_norec` and its two siblings, which are this statement proved
on the regime where `BindersIndep` already holds.

`henv₀` is `hstage`'s other half, and it is what makes `hstage` bite: `addIndTypes` is pure
data, so `hstage` *alone* is satisfied at §7.2's counterexample by a junk `env₀` that declares
the offending constant while the constant it mentions is undeclared.  `VEnv.Ordered env₀` rules
that out — `RecArgIndep.rai_not_staged` is the machine-checked form — and it is available
wherever `VInductDecl'.WF.ctors` is being proved.  `henv` is **not** derivable from `henv₀` and
`hstage`: that step needs `VIndType.WF` for the block, which is not a hypothesis here, so both
are listed.

`VEnv.WF env` is deliberately **not** a hypothesis, and not for want of it being the right one:
`VEnv.WF` is defined in `Theory/Typing/Env.lean`, which transitively imports *this file*, so
naming it here is an import cycle.  `VEnv.Ordered` (`Theory/Typing/Lemmas.lean`) is the
strongest environment hypothesis available at this layer, and is what `henv` is.

**Why it should be true.**  For a binder `B : Sort u` in `ξ` to depend on the *value* of an
earlier recursive field `a : ∀ ξ₀, I p π₀`, something in scope must eliminate an `I`.  At the
staged environment nothing can: `I`'s recursor does not exist yet, `I` has no ι-rules, the
parameters were typed before `I` was declared, and an earlier field of type
`(∀ ξ₀, I p π₀) → Sort u` is itself ill-formed — `pos`'s `none` branch needs it definitionally
block-free and its `some` branch needs the shape `∀ ξ, I p π`, and it is neither.

**Correction to the first version of this docstring** (`RecArgIndep.lean` §7.5).  It continued:
"so every occurrence of `a` in a well-formed `B` sits under a redex and disappears under `whnf`;
the `(fun _ : T => Nat) r` example in `pos`'s `none`-branch comment is the shape."  That shape
is **not an admissible binder** — its domain `T` mentions a block constant, so the redex does
too, and `hbind` demands binders be *syntactically* block-free
(`RecArgIndep.raiRedex_not_noBlock`).  Nor is "sits under a redex" exhaustive: `P a` for a
declared `P : (∀ ξ₀, I p π₀) → Sort 1` is block-free, well-typed and not a redex
(`RecArgIndep.raiB_betaHead`) — which is exactly what `hstage` is there to exclude.

**Why it is a `sorry` and not a proof.**  ~~It needs `IsDefEqU.forallE_inv`.~~  **CORRECTED
2026-09-03: `forallE_inv` is not on the path.**  `Theory/Inductive/RecArgIndepClose.lean`
enumerates where the earlier recursive field can sit inside a syntactically block-free `B`: the
`const` route is closed by staging (proved there), the *parameter* route is closed for free
because `tyApp` applies **all** parameters to `I_j`, so such a parameter would have to mention
itself — and everything remaining reduces to `VEnv.RigidConstPiDisj` and
`VEnv.RigidConstSortDisj`, both already-named predicates.

Two things that makes clearer.  Both of those are **false at `Ordered` environments**
(`VEnv.not_rigidConstPiDisj_rcPiEnv`), and this theorem deliberately assumes `Ordered` rather
than `VEnv.WF` — but those refutations work by aiming a two-δ-rule *hub* at a rule-free head, and
`RecArgIndepClose.defeq_noBlock_of_staged` shows no rule of a staged environment mentions the
block anywhere, by freshness alone.  So the residual is **pure confluence**, and plausibly does
not need `VEnv.WF` at all.

Do **not** discharge it via `RigidShapeUniqNS.constPiDisj`: measured, that would import a
529-transitive-user hole into this file's cone — currently 851 constants whose only hole is
`exists_indep` itself — and create an import cycle.  Rigidity should stay a hypothesis.

A missing statement is worse than an open one: an open one shows up in a `sorry` count, a
missing one is invisible until someone needs it.

`r'` keeps `idx`, `args` and the binder *count*, so only the binder *types* move; every
de Bruijn index in `args` and in the result therefore still points where it did. -/
theorem VIndRecArg.exists_indep {env₀ env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (henv₀ : VEnv.Ordered env₀)
    (henv : VEnv.Ordered env)
    (hstage : env₀.addIndTypes D = some env)
    (hlen : pre.length = i)
    (hΓ : Γ = (pre.map (·.type)).reverse ++ D.params.reverse)
    (hpre : ∀ (i' : Nat) (F' : VIndField), pre[i']? = some F' →
      F'.WF env D (pre.take i') (((pre.take i').map (·.type)).reverse ++ D.params.reverse) i')
    (hty : env.HasType D.uvars Γ F.type (.sort F.lvl))
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hOn : OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars))
    (hdefeq : env.IsDefEqType D.uvars Γ F.type (r.canonType D i)) :
    ∃ r' : VIndRecArg,
      r'.idx = r.idx ∧ r'.args = r.args ∧ r'.binders.length = r.binders.length ∧
      (∀ B ∈ r'.binders, D.NoBlock B) ∧
      env.IsDefEqType D.uvars Γ F.type (r'.canonType D i) ∧
      r'.BindersIndep pre i ∧
      env.TeleDefEq D.uvars Γ r.binders r'.binders := by
  sorry

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
    F.WF env D (C.fields.take i)
      (((C.fields.take i).map (·.type)).reverse ++ D.params.reverse) i
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
is six fields: `pat_simple`, `pat_uniq`, `pat_wf`, `extra_pat`, `pat_app_l_uniq` and
`pat_app_uniq`.  The design's four `pat_major_*` fields never existed; `pat_app_l` did, had
no consumer, and has been deleted.  **`pat_app_l_uniq` and `pat_app_uniq` do have
consumers** (`Typing/HeadReduction.lean:158` and `:160`) -- an earlier version of this note
claimed all three `pat_app_*` were dead, which was wrong.

Of the six, `pat_simple` holds by construction of `SimplePattern.iota`, `extra_pat`'s
λ-peeled form matches this `rhs` definitionally, and the three orthogonality fields reduce
to arithmetic on `Pattern.varN` depths plus one global side condition — **no recursor name
equals any constructor name**, which within a block follows from `addInduct'`'s freshness
but across blocks must be assumed.  State that side condition explicitly wherever it is
used; do not leave it implicit in a proof.  So the shape chosen here is what leaves
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

/-- **A block that really was declared below `env`.**

The declaration *history* is not part of `VEnv`, and threading it into every statement that
needs "this block was checked and added earlier" is what forced `ds : List VDecl` through
`VIndRestore.Faithful`, `VNestedOcc.Occurs`, `VInductDecl'.Built` and `VEnv.AddNested{,B}` —
and, through them, into a would-be `VDecl.WF.induct` premise, which is where it could not go
(`VDecl.WF env d env'` carries no history; only `VEnv.WF'` does).

This is the same fact stated over environments alone: the block was well formed at *some*
`env₀`, `addInduct'` succeeded there, and the result sits below `env`.  It is exactly the
conclusion of `VEnv.WF'.exists_addInduct'` (`Theory/Inductive/Nested.lean`), so a history
discharges it (`VEnv.WF'.declared`) — but it never has to be carried.

It is not weaker than membership in the history where it is used.  `env₁ ≤ env` pins the
block's *recursor* type as `env` stores it, and a recursor type has one minor premise per
constructor (`VInductDecl'.minors`), so a `D` with a truncated constructor list cannot satisfy
it against an `env` holding the real block — which is the `fooComp_inconsistent` failure mode
(`Theory/Inductive/Companion.lean`) that `ctors_complete` exists to exclude. -/
def VInductDecl'.Declared (D : VInductDecl') (env : VEnv) : Prop :=
  ∃ env₀ env₁ : VEnv, env₀.addInduct' D = some env₁ ∧ env₁ ≤ env

theorem VInductDecl'.Declared.mono {D : VInductDecl'} {env env' : VEnv}
    (h : D.Declared env) (hle : env ≤ env') : D.Declared env' :=
  let ⟨e₀, e₁, hadd, hb⟩ := h; ⟨e₀, e₁, hadd, hb.trans hle⟩


/-! ## K1's skeleton: what a constructor's *stored* type gives back

`addDecl.WF`'s `inductDecl` branch has to turn a `Lean.Declaration.inductDecl` into a
`VInductDecl'`, and **that is not a function**: `VInductDecl'` is a decomposed record carrying
data the kernel computes *while checking*.  `VIndType.indices`, `D.params`, `D.lvl`,
`VIndField.lvl`, `VIndField.recArg` and `D.isLE` are all unrecoverable from the declaration —
`T.type` is only *definitionally* a pi-telescope (F1), and `D.lvl` occurs in no stored type at
all (`Theory/Inductive/DeclExamples.lean`).  So the translation is a *relation*, with those
fields existential and tied by `IsDefEqU`.

What **is** recoverable is the constructor side, and for a sharp reason: by F2 the kernel walks
a constructor's pi-spine *without* `whnf`, so `VIndCtor.type` is that telescope on the nose.
This section is that half — a pure function, with a round-trip theorem, and no `whnf` anywhere.

`splitPis` splits at an *exact* count rather than peeling maximally.  That is deliberate: a
field's type may itself be a `forallE` (`Iff.intro`'s `mp : a → b`), and a maximal peel would
walk into the last one's codomain.  Splitting at `np + |fields|` cannot.

**R3 is gated on injectivity, not on bookkeeping.**  Turning the checker's walk into
`VIndType.WF.canon` means chaining `n` steps of "this type is defeq to `∀ A, ty'`" into one
`mkPi` defeq.  Each step is a `forallEDF` congruence, which produces the sort
`imax uA v`; the step itself arrives at whatever sort the type was checked at.  Composing the
two needs those sorts to agree — i.e. sort uniqueness.  `VEnv.IsDefEqU.trans` and
`IsDefEq.uniq` (`Theory/Typing/UniqueTyping.lean`) both do this, and both are
**`sorryAx`-tainted** through `Injectivity.lean`'s open statements (machine-checked).  So R3 is
not ~90 lines of telescope arithmetic; it is downstream of the injectivity family, *unless* the
refinement layer's `whnf` specification delivers its defeq at a caller-chosen sort rather than
as an `IsDefEqU`.  That is a `Verify/` question and it should be answered before R3 is priced
again.

## R10's handover: `AddInduct`'s constructors

`AddInduct` (`Verify/Environment/Basic.lean`) has no constructors, so `TrEnv'.induct` cannot
fire and every environment containing an inductive is outside `TrEnv`.  The design, for
whoever holds that file:

*Three folds mirroring `VEnv.addInduct'_stages`, not one opaque relation.*  An `AddIndConst`
step — `TrConstant .safe`, freshness, `addConst` — folded over `D.typeConsts`, then
`D.ctorConsts`, then `D.recConsts`, with the ι-rules added last.  That is `AddQuot`/`AddQuot1`'s
shape, so `to_addInduct` composes exactly as `AddQuot.to_addQuot` does, and each stage's
freshness obligation is the one `addConstList_fresh` already supplies.

*`TrEnv'.induct` is gated to safe blocks*, as `unsafeDef` is gated to unsafe ones: positivity is
skipped when `isUnsafe`, so `VIndField.WF.pos` has no witness.

**An earlier version of this note added "and `TrEnv'.ignore` takes those declarations
instead".  That is false and is now machine-checked false**
(`TrEnv'.ignore_unavailable_at_unsafe`, `Verify/TypeChecker/Reduce.lean`): `ignore`'s premise
is `¬ safety ≤ ci.safety`, and `.unsafe` is the bottom of `DefinitionSafety`, so
`.unsafe ≤ ci.safety` holds for every `ci`.  At `safety = .unsafe` nothing is hidden, so every
declared constant needs a `VEnv` counterpart and `ignore` cannot supply one.  The honest
position is that **an unsafe inductive block is currently unhandled**, not handled by
ignoring: gating `induct` to safe blocks leaves `TrEnv' .unsafe` with no rule for an unsafe
inductive.  The gate does not *create* the gap — today `TrEnv' .unsafe` has no rule for a safe
inductive either — but it does not close it, and nothing below should be read as claiming it
does.

*What it breaks, deliberately.*  `TrEnv'.no_inductInfo` becomes false, and with it the
vacuous postconditions of `checkEqType.WF` and `addQuot.WF`.  **And `TrEnv'.find?_shape`
(`Verify/TypeChecker/Reduce.lean`) becomes false as stated** — its `induct` case is discharged
only because `AddInduct` is empty, and it has four live consumers matching on its five
disjuncts.  That file already records `no_inductInfo_false_at_safe`, a refutation of the
neighbouring lemma for the same reason, so this is the second theorem there that is true only
vacuously.

*Triage target.*  `eqIndDecl` — its ι-rule is checked against Lean's own stored rule in
`DeclExamples.lean`, and `fooDecl_WF` / `fooEnv_eq` are a worked `addInduct'` success from
`VEnv.empty` to copy.

**Where each field comes from.**  Read off `Lean4Lean/Inductive/Add.lean`, since the checker's
phases are what witness the relation.  `checkInductiveTypes` walks each *type*'s pi-spine with
`whnf` at every step (F1); `checkConstructors` walks each *constructor*'s **without** `whnf`
(F2).  That asymmetry is the whole reason one half is a function and the other is not.

| field | supplied by | how |
|---|---|---|
| `uvars` | declaration | `lparams.length` |
| `types[j].name`, `.type` | declaration | stored, verbatim |
| `ctors[q].params/fields.type/args` | declaration | `VIndCtor.skeleton` below, by F2 |
| `D.params` | **constructor side** | *not* the type's pi-spine (F1 blocks it) — tie to `C.params` via `VIndCtor.WF.params_eq`, where the fact already holds |
| `types[j].indices` | checker, *count only* | `stats.nindices` is a `Nat`; the index fvars are `withLocalDecl`-bound and dropped.  Existential, tied by `VIndType.WF.canon` |
| `D.lvl` | checker | `stats.resultLevel`, after `ensureSort`.  It occurs in **no stored type** (`DeclExamples`), so `canon` / `VIndCtor.WF.result` is the only tie — do not look for a syntactic route |
| `fields[i].lvl` | checker | `ensureType dom` in `checkConstructors` |
| `fields[i].recArg` | checker | `checkPositivity`/`isRecArg` — **skipped when `isUnsafe`**, which is why `TrIndDecl` is stated for safe blocks only |
| `D.isLE` | checker | `isLargeEliminator` |
-/

namespace VExpr

/-- Split off exactly `n` leading `forallE` binders. -/
def splitPis : Nat → VExpr → List VExpr × VExpr
  | 0, e => ([], e)
  | n+1, .forallE A B => let (As, b) := splitPis n B; (A :: As, b)
  | _+1, e => ([], e)

theorem splitPis_mkPi : ∀ {As : List VExpr} {B : VExpr},
    splitPis As.length (mkPi As B) = (As, B)
  | [], _ => rfl
  | A :: As, B => by
    rw [List.length_cons, mkPi, splitPis, splitPis_mkPi (As := As) (B := B)]
end VExpr

/-- **The constructor skeleton.**  From the number of parameters and a constructor's *stored*
type, read back the three syntactic components of `VIndCtor`: the parameter binders, the field
binder types, and the result's non-parameter arguments.

`VIndField.lvl` and `VIndField.recArg` are *not* here — they are `checkPositivity`/`isRecArg`
output, and the relation supplies them. -/
def VIndCtor.skeleton (np : Nat) (nf : Nat) (ty : VExpr) :
    List VExpr × List VExpr × List VExpr :=
  let (tele, body) := VExpr.splitPis (np + nf) ty
  (tele.take np, tele.drop np, body.spineArgs.drop np)

/-- **The round trip.**  `skeleton` inverts `VIndCtor.type` on the nose — no `whnf`, no
conversion, no side condition beyond the parameter count that `VIndCtor.WF.params_len`
records. -/
theorem VIndCtor.skeleton_type (C : VIndCtor) (D : VInductDecl') (j : Nat)
    (hp : C.params.length = D.np) :
    VIndCtor.skeleton D.np C.fields.length (C.type D j)
      = (C.params, C.fields.map (·.type), C.args) := by
  have hlen : (C.params ++ C.fields.map (·.type)).length = D.np + C.fields.length := by
    rw [List.length_append, List.length_map, hp]
  rw [VIndCtor.skeleton, VIndCtor.type, ← hlen, VExpr.splitPis_mkPi]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact List.take_left' hp
  · exact List.drop_left' hp
  · show (VIndCtor.canonResult C D j).spineArgs.drop D.np = C.args
    rw [VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.spineArgs_mkApp, VExpr.spineArgs_const,
      List.nil_append, List.drop_left' (by simp)]

/-- **R5: the skeleton gives `D.params` too — up to the tie that already holds.**

`D.params` is *not* syntactically recoverable: it is the `whnf`-normalised parameter telescope,
and F1 blocks reading it off `T.type`.  But `VIndCtor.params` **is** recoverable (F2), and
`VIndCtor.WF.params_eq` already says the two are definitionally equal as contexts.  So the
translation should not try to recover `D.params` at all — it should take the constructor's copy,
which the skeleton hands back, and carry the tie.

This is the transport discipline, and it has now paid seven times across this tree, so it is
worth stating as the first thing to try rather than the last:

> **When a field is not syntactically recoverable, do not look for a cleverer way to recover
> it.  Look for a place where a well-formedness judgement already asserts it, and tie there.**

`D.params` is the clean case — `VIndCtor.WF.params_eq` asserts exactly the needed equality, and
it is in scope wherever the constructor is well-formed.  The same reading disposed of the
`Params` arity obligations (read the arity off the stored constant, where two patterns sharing
a leaf must agree), of `extra_pat`'s context weakening (take a preimage rather than transport),
and of the `.indTy` role question (`VDefEq.key` already names the roles to exclude). -/
theorem ctor_params_skeleton {env : VEnv} {D : VInductDecl'} {j : Nat} {T : VIndType}
    {C : VIndCtor} (henv : VEnv.Ordered env) (h : VIndCtor.WF env D j T C) :
    VEnv.IsDefEqCtx env D.uvars []
      (VIndCtor.skeleton D.np C.fields.length (C.type D j)).1.reverse D.params.reverse := by
  rw [VIndCtor.skeleton_type C D j h.params_len]
  exact h.params_eq

end Lean4Lean
