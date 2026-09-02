import Lean4Lean.Theory.Inductive.ParamRedex

/-!
# An **indexed** nested block, and `restore_ownHeads` exercised at non-empty residuals

`VIndRestore.restore_ownOcc` / `restore_ownHeads` (`Theory/Inductive/Restore.lean`) say the
restoration is the identity at a *uniform* occurrence of a member the step **declares**, with
**no condition on the residual arguments**.  §19.3 of `Theory/Inductive/ParamRedex.lean` records
that the extra generality was, at the time, **unexercised**: the three blocks of the witness cone
`restore_ownHeads` is confirmed at — `MRWit.MJ`, `MPWit.MP`, `ntreeAux` — have no indices on any
member (`tq_cone_unindexed`, `decide`), so `D.np` exhausts every uniform occurrence's argument list
there and `restore_noK` sufficed at all of them.

This file supplies the missing coordinate.  `TQ` is `MRWit.MJ` with **two** coordinates moved:

* a parameter, like `MPWit.MP` (`np = 1`, `tq_np_one`); and
* an **index** — `TQ : Type → Type → Type`, one parameter and one index (`tq_indices`) —
  nesting through a container `MI` that is **itself indexed**, so that *both* faces carry a
  non-empty residual argument list:
  - the companion constructor's stored redex head-β-contracts to `TQ α Prop`, an occurrence of
    the block's **own** member whose residual is `[Prop]` (`tq_uniformOcc_redexBody`), and
  - the user constructor's field is `_nested.MI_1 α Prop`, a **companion**-pointing occurrence
    whose residual is `[Prop]` as well (`tq_uniformOcc_objField`).

The two coordinates `MRWit`/`MPWit` fixed are still fixed here — it is still a redex block
(`tq_auxNodeB_not_canonical`) and still parameterised (`tq_np_one`) — so the indices are the only
coordinates that move.  Nothing else `MRWit`/`MPWit` measured is re-measured here: this file is
about `restore`, not about `WF`, `Faithful` or the ι-rules.

**The honest headline, stated before the details** (§5–§6): the strengthening is now exercised at
a *sort-correct* separating witness, but it is still **not load-bearing at a position the block
contains**, and that is a theorem about the specification rather than an accident of this witness.
`VIndField.WF.pos` (F7) requires a recursive field's index arguments to be **block-free**, and
`VIndCtor.WF.args_fresh` (F5) requires the same of a constructor's result indices; a companion
inside a uniform own occurrence's residual is the only shape at which `restore_noK` can fail while
`restore_ownHeads` succeeds, and those two clauses forbid it at every canonical occurrence of every
block (`tq_ownOcc_noConsts_of_WF`, §6).  Lean's own kernel rejects the same shape.  So the negative
result of the round is:

> at every *canonical* own-head occurrence of any block the specification accepts, the residual
> arguments are companion-free and `restore_noK` suffices; the stored-type case is left open in
> §6, precisely.

What the round *does* buy, and it is not nothing: `VInductDecl'.OwnHeads.own` is instantiated at a
non-empty `rest` **at a position the block contains** (§4) — a stored field, at a member that
genuinely takes the argument — where §19.3's non-empty instantiation `mp_ownComp_ownHeads` was a
hand-written over-application; and the separating witness `tqOwnComp` is now
**sort-correct** in the index slot (§5.1), where §19.3's `mpOwnComp` was a well-formed `VExpr`
that could not be typed at all.
-/

namespace Lean4Lean
namespace MRedex
namespace TQWit

open Lean (Name)

/-! ## §1 The block

`MI` is `MRWit.MDep` with an index; `TQ` is `MRWit.MJ` with a parameter and an index, nesting
through `MI` at that index.  Nothing else moves. -/

/-- The container, **indexed**: the index is what gives the companion member a residual. -/
inductive MI (α : Type) (β : α → Type) : Type → Type where
  | node : (k : α) → β k → MI α β Prop

/-- The user's block: parameterised *and* indexed, nesting through an indexed container.  Lean's
own kernel runs the nested elimination and stores `TQ.rec_1`, whose companion minor premise has
the field domain `(fun x => TQ α Prop) k` — the redex. -/
inductive TQ (α : Type) : Type → Type where
  | obj : MI Prop (fun _ => TQ α Prop) Prop → TQ α Prop

/-! ### §1.1 `MI`'s block, anchored on the environment -/

def miNode : VIndCtor where
  name := ``MI.node
  params := [.sort (.succ .zero), .forallE (.bvar 0) (.sort (.succ .zero))]
  fields :=
    [{ type := .bvar 1, lvl := .succ .zero, recArg := none },
     { type := .app (.bvar 1) (.bvar 0), lvl := .succ .zero, recArg := none }]
  args := [.sort .zero]

def miType : VIndType where
  name := ``MI
  type := .forallE (.sort (.succ .zero))
    (.forallE (.forallE (.bvar 0) (.sort (.succ .zero)))
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))))
  indices := [.sort (.succ .zero)]
  ctors := [miNode]

def miDecl : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero), .forallE (.bvar 0) (.sort (.succ .zero))]
  lvl := .succ .zero
  isLE := true
  types := [miType]

example : miType.type = (vconst(type_of% @MI)).type := rfl
example : miNode.type miDecl 0 = (vconst(type_of% @MI.node)).type := rfl
example : miDecl.recType 0 = (vconst(type_of% @MI.rec)).type := rfl

/-! ### §1.2 `TQ`'s auxiliary block -/

def tqNestedName : Name := `_nested.MI_1

/-- The field the elimination manufactures: `(fun x : Prop => TQ #2 Prop) #0`, in the context
`[field₀, α]`.  Its head-β contraction `TQ #2 Prop` is an own-member occurrence with the residual
`[Prop]` — the coordinate this file exists for. -/
def tqRedex : VExpr :=
  .app (.lam (.sort .zero) (.app (.app (.const ``TQ []) (.bvar 2)) (.sort .zero))) (.bvar 0)

/-- The companion constructor **as `VNestedOcc.field` computes it** (`tq_auxNodeB_built`). -/
def tqAuxNodeB : VIndCtor where
  name := `_nested.MI_1.node
  params := [.sort (.succ .zero)]
  fields :=
    [{ type := .sort .zero, lvl := .succ .zero, recArg := none },
     { type := tqRedex, lvl := .succ .zero,
       recArg := some { binders := [], idx := 0, args := [.sort .zero] } }]
  args := [.sort .zero]

/-- The user's constructor after `replaceAllNested`: the field is `_nested.MI_1 α Prop`, a
companion occurrence **with a residual index**. -/
def tqObj : VIndCtor where
  name := ``TQ.obj
  params := [.sort (.succ .zero)]
  fields := [{ type := .app (.app (.const tqNestedName []) (.bvar 0)) (.sort .zero),
               lvl := .succ .zero,
               recArg := some { binders := [], idx := 1, args := [.sort .zero] } }]
  args := [.sort .zero]

def tqAux (Cn : VIndCtor) : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero)]
  lvl := .succ .zero
  isLE := true
  types :=
    [{ name := ``TQ,
       type := .forallE (.sort (.succ .zero))
         (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))),
       indices := [.sort (.succ .zero)], ctors := [tqObj] },
     { name := tqNestedName,
       type := .forallE (.sort (.succ .zero))
         (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))),
       indices := [.sort (.succ .zero)], ctors := [Cn] }]

def tqK : List Name := [tqNestedName]

def tqRestore : VIndRestore where
  tyName j := if j = 1 then ``MI else ``TQ
  tyLvls _ := []
  tyArgs j := if j = 1 then
      [.sort .zero, .lam (.sort .zero) (.app (.app (.const ``TQ []) (.bvar 1)) (.sort .zero))]
    else [.bvar 0]
  ctorName n := if n = `_nested.MI_1.node then ``MI.node else n
  recName n := if n = `_nested.MI_1.rec then ``TQ.rec_1 else n

def tqOcc : VNestedOcc where
  decl := miDecl
  idx := 0
  lvls := []
  args := [.sort .zero,
    .lam (.sort .zero) (.app (.app (.const ``TQ []) (.bvar 1)) (.sort .zero))]
  auxName := tqNestedName
  ctorName n := if n = ``MI.node then `_nested.MI_1.node else n

/-! ### §1.3 The transcription, anchored three ways by `rfl`

The standard `MPWit` set: the member's type, the user constructor's type after `σ`, and the
recursor's universe count, all against `type_of%`; plus the two `Built` equations, which check
the transcription against the *construction* rather than against Lean. -/

example : ((tqAux tqAuxNodeB).types.getD 0 default).type = (vconst(type_of% @TQ)).type := rfl

theorem tq_obj_declared :
    (tqObj.typeR (tqAux tqAuxNodeB) tqRestore 0).substC
      (tqRestore.csubstTy (tqAux tqAuxNodeB) tqK) = (vconst(type_of% @TQ.obj)).type := rfl

example : (tqAux tqAuxNodeB).recUvars = (vconst(type_of% @TQ.rec)).uvars := rfl

theorem tq_auxNodeB_built :
    tqOcc.ctor (tqAux tqAuxNodeB).header tqRestore miNode = tqAuxNodeB := rfl

theorem tq_member_built :
    (tqAux tqAuxNodeB).types[1]? = some (tqOcc.member (tqAux tqAuxNodeB).header tqRestore) := rfl

/-! ## §2 The coordinate that moves: the block is INDEXED

`np = 1` as at `MPWit.MP`, and — new — one index on **each** member. -/

theorem tq_np_one : (tqAux tqAuxNodeB).np = 1 := rfl

theorem tq_params : (tqAux tqAuxNodeB).params = [.sort (.succ .zero)] := rfl

/-- The user's member is indexed. -/
theorem tq_indices : ((tqAux tqAuxNodeB).types.getD 0 default).indices
    = [.sort (.succ .zero)] := rfl

/-- …and so is the companion member, because the container `MI` is: this is what gives the
*companion*-pointing occurrences a residual too (§7). -/
theorem tq_aux_indices : ((tqAux tqAuxNodeB).types.getD 1 default).indices
    = [.sort (.succ .zero)] := rfl

theorem tq_indices_ne_nil : ((tqAux tqAuxNodeB).types.getD 0 default).indices ≠ [] := by decide

/-- **The gap this file fills, measured.**  Every member of every nested block in the witness cone
is *unindexed*, so `D.np` exhausts every uniform occurrence's argument list there and the residual
is always `[]`.  (`InductiveDeclExamples.ntreeAuxI` does carry an index telescope, but it is the
deliberately-wrong negative control of `ntreeAuxI_not_built` — no construction produces it.) -/
theorem tq_cone_unindexed :
    (∀ T ∈ (MRWit.mrAux MRWit.mrAuxNodeB).types, T.indices = [])
      ∧ (∀ T ∈ (MPWit.mpAux MPWit.mpAuxNodeB).types, T.indices = [])
      ∧ (∀ T ∈ InductiveDeclExamples.ntreeAux.types, T.indices = []) := by decide

/-- **It is still a redex block**: the companion's recursive field is stored `.app`-headed at a
`.lam`.  So the indices are the *only* coordinate that moves from `MPWit.MP`. -/
theorem tq_auxNodeB_not_canonical : ¬ tqAuxNodeB.Canonical (tqAux tqAuxNodeB) := by
  intro h
  exact absurd (h 1 _ _ rfl rfl) (by decide)

theorem tq_ctorsAll_eq : (tqAux tqAuxNodeB).ctorsAll = [(0, tqObj), (1, tqAuxNodeB)] := rfl

theorem tq_not_canonical : ¬ (tqAux tqAuxNodeB).Canonical := by
  intro h
  refine tq_auxNodeB_not_canonical (h 1 tqAuxNodeB ?_)
  rw [tq_ctorsAll_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-! ## §3 The side conditions the theorem needs -/

theorem tq_blockNames : (tqAux tqAuxNodeB).blockNames = [``TQ, tqNestedName] := rfl

theorem tq_blockNames_nodup : (tqAux tqAuxNodeB).blockNames.Nodup := by decide

theorem tq_allNames_nodup : (tqAux tqAuxNodeB).allNames.Nodup := by decide

/-- **`OwnId`** — `MPWit.mpRestore_ownId` at this block, verbatim in structure. -/
theorem tqRestore_ownId : tqRestore.OwnId (tqAux tqAuxNodeB) tqK where
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [tqAux] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [tqAux] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [tqAux] at hT
  recName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [tqAux] at hT
  ctorName := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [tqAux] at hT

theorem tq_types0 : (tqAux tqAuxNodeB).types[0]? = some
    { name := ``TQ,
      type := .forallE (.sort (.succ .zero))
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))),
      indices := [.sort (.succ .zero)], ctors := [tqObj] } := rfl

theorem tq_own_notK : ``TQ ∉ tqK := by decide

/-! ## §4 The strengthening EXERCISED: `own` at a non-empty residual

This is the point of the round.  The companion constructor's stored field is the redex
`(fun x : Prop => TQ #2 Prop) #0`; the trigger fires on its **body** at depth `2`, and what it
reports is the block's own member **together with a non-empty residual argument list**
`[Prop]`.  At `MRWit.MJ`, `MPWit.MP` and `ntreeAux` the same equation reports `rest = []`
(`tq_cone_unindexed`).

**Exactly what is new, stated narrowly.**  §19.3's `mp_ownComp_ownHeads` already instantiates
`VInductDecl'.OwnHeads.own` at a non-empty `rest` — so *that* is not the novelty.  What is new is
that the occurrence here is one the block **contains**: it is the head-β contraction of the
companion constructor's stored field, at a member that genuinely takes that argument (an index),
where `mpOwnComp` is a hand-written over-application of `MP` to an argument it has no slot for. -/

/-- The redex's body: an own-member occurrence at depth `2`, parameter run `[#2]`, residual
`[Prop]`. -/
def tqNt : VExpr := .app (.app (.const ``TQ []) (.bvar 2)) (.sort .zero)

/-- **The measurement.**  `decide`, not `rfl`: the trigger is a decision. -/
theorem tq_uniformOcc_redexBody :
    (tqAux tqAuxNodeB).uniformOcc? 2 tqNt = some (0, [.sort .zero]) := by decide

/-- …and the residual is **not** empty — the coordinate `MRWit`/`MPWit`/`ntreeAux` cannot supply. -/
theorem tq_redexBody_residual_ne_nil :
    ((tqAux tqAuxNodeB).uniformOcc? 2 tqNt).map (·.2) ≠ some [] := by decide

/-- **`restore_ownOcc` at a non-empty residual**, at one occurrence. -/
theorem tq_restore_redexBody_id : tqRestore.restore (tqAux tqAuxNodeB) 2 tqNt = tqNt :=
  VIndRestore.restore_ownOcc tqRestore_ownId tq_uniformOcc_redexBody tq_types0 tq_own_notK

/-- The same, closed under the two congruences the stored field adds. -/
theorem tq_ownHeads_redex : (tqAux tqAuxNodeB).OwnHeads tqK 1 tqRedex :=
  .app (by decide)
    (.lam (.sort 1 .zero)
      (.own (rest := [.sort .zero]) tq_uniformOcc_redexBody tq_types0 tq_own_notK))
    (.bvar 1 0)

theorem tq_restore_redex_id : tqRestore.restore (tqAux tqAuxNodeB) 1 tqRedex = tqRedex :=
  VIndRestore.restore_ownHeads tqRestore_ownId tq_ownHeads_redex

theorem tq_auxFieldTypesR_split :
    tqAuxNodeB.fieldTypesR (tqAux tqAuxNodeB) tqRestore
      = [.sort .zero, tqRestore.restore (tqAux tqAuxNodeB) 1 tqRedex] := rfl

/-- The stored companion field telescope is restored to itself — row 127f's conclusion at the
indexed block, through the rule rather than through companion-freeness. -/
theorem tq_auxFieldTypesR_eq_fields :
    tqAuxNodeB.fieldTypesR (tqAux tqAuxNodeB) tqRestore = tqAuxNodeB.fields.map (·.type) := by
  rw [tq_auxFieldTypesR_split, tq_restore_redex_id]; rfl

/-- **Negative result, half one, and it is the honest headline.**  At this *genuine* position
`restore_noK` still suffices: the residual `[Prop]` is a sort, so the whole stored field is
companion-free and `VExpr.NoConsts tqK` holds of it.  Making the residual non-empty is therefore
**not** enough to make the strengthening load-bearing; the residual has to contain a member of
`K`, and §6 shows Lean's kernel forbids that. -/
theorem tq_redex_noK : VExpr.NoConsts tqK tqRedex :=
  ⟨⟨trivial, ⟨⟨tq_own_notK, trivial⟩, trivial⟩⟩, trivial⟩

theorem tq_restore_redex_id_noK : tqRestore.restore (tqAux tqAuxNodeB) 1 tqRedex = tqRedex :=
  VIndRestore.restore_noK tqRestore_ownId 1 tqRedex tq_redex_noK

/-! ## §5 Where `restore_noK` FAILS and `restore_ownHeads` succeeds — exhibited

`tqOwnComp` is `TQ #0 (_nested.MI_1 #0 Prop)`: a uniform occurrence of the block's **own**
member whose residual argument is `tqObj`'s field type, i.e. the **companion** occurrence.
`OwnHeads` holds of it, `VExpr.NoConsts tqK` fails of it, and the restoration is the identity on
it — because `restore` hands the residual arguments to `tyAppR` unrestored.

What is new here relative to §19.3's `mpOwnComp`: at `MPWit.MP` the separating witness was
`MP #0 _nested.MDep_1`, an application of a member with **no** argument slot left to fill, so it
was a well-formed `VExpr` that no environment could type.  Here the residual occupies the block's
own **index** slot, and that slot is a `Type` (§5.1). -/

def tqOwnComp : VExpr := (tqAux tqAuxNodeB).tyApp 0 0
  [.app (.app (.const tqNestedName []) (.bvar 0)) (.sort .zero)]

theorem tq_ownComp_ownHeads : (tqAux tqAuxNodeB).OwnHeads tqK 0 tqOwnComp :=
  .own (VInductDecl'.uniformOcc?_tyApp tq_blockNames_nodup tq_types0 0 _) tq_types0 tq_own_notK

/-- `restore_noK`'s hypothesis is **false** here, so `restore_noK` does not apply. -/
theorem tq_ownComp_not_noConsts : ¬ VExpr.NoConsts tqK tqOwnComp :=
  fun h => h.2.1.1 (by decide)

/-- …and the conclusion nonetheless holds, by the rule. -/
theorem tq_ownComp_restore_id : tqRestore.restore (tqAux tqAuxNodeB) 0 tqOwnComp = tqOwnComp :=
  VIndRestore.restore_ownHeads tqRestore_ownId tq_ownComp_ownHeads

/-- The residual argument is not invented for the occasion: it is `tqObj`'s stored field type. -/
theorem tq_ownComp_residual_is_objField :
    tqOwnComp = (tqAux tqAuxNodeB).tyApp 0 0 [(tqObj.fields.getD 0 default).type] := rfl

/-! ### §5.1 The index slot the residual fills, and what is *not* claimed

Two `rfl`s: the own member's index telescope is `[Type]`, and the companion member's canonical
type is `Type → Type → Type`, i.e. one parameter and one index, both `Type`, landing in `Type`.
So `_nested.MI_1 #0 Prop` is sort-correct in `TQ`'s index slot, where `MPWit.mpOwnComp`'s residual
had no slot to fill.

**Not claimed**: a typing derivation.  This is arity-and-sort agreement computed by `rfl`, not
`env.HasType`; no environment in this file holds `_nested.MI_1` (the auxiliary constants exist
only inside `ElimNestedInductive`, which is why `tqRestore` presents them away). -/

theorem tq_index_slot :
    ((tqAux tqAuxNodeB).types.getD 0 default).indices = [.sort (.succ .zero)]
      ∧ ((tqAux tqAuxNodeB).types.getD 1 default).canonType (tqAux tqAuxNodeB)
        = .forallE (.sort (.succ .zero))
            (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := ⟨rfl, rfl⟩

/-! ### §5.2 The side condition is sharp at the indexed block too

`tqOwnNonUnif` is `TQ #5 (_nested.MI_1 #0 Prop)`: the **same two constants** as `tqOwnComp` and
the same own head, but the parameter run is `#5` instead of `#0`, so the occurrence is not
*uniform*, the trigger returns `none`, `restore` descends, and the companion occurrence inside
**moves**.  (This is `MPWit`'s `mp_ownNonUnif_*` at the indexed block; at `np = 0` the condition
is vacuous, so a parameter is needed to state it at all.) -/

def tqOwnNonUnif : VExpr :=
  .app (.app (.const ``TQ []) (.bvar 5))
    (.app (.app (.const tqNestedName []) (.bvar 0)) (.sort .zero))

theorem tq_ownNonUnif_not_uniform :
    (tqAux tqAuxNodeB).uniformOcc? 0 tqOwnNonUnif = none := by decide

theorem tq_ownNonUnif_restore_ne :
    tqRestore.restore (tqAux tqAuxNodeB) 0 tqOwnNonUnif ≠ tqOwnNonUnif := by decide

theorem tq_not_ownHeads_ownNonUnif : ¬ (tqAux tqAuxNodeB).OwnHeads tqK 0 tqOwnNonUnif :=
  fun h => tq_ownNonUnif_restore_ne (VIndRestore.restore_ownHeads tqRestore_ownId h)

/-! ## §6 …and why that witness cannot be a position the block CONTAINS

`tqOwnComp` is the shape `restore_noK` cannot handle, and §5 shows the rule handles it.  The
question the round exists to settle is whether such an occurrence can appear *inside* a block the
specification accepts — because that, and only that, would make the strengthening load-bearing.

It cannot, and this is a theorem rather than an observation about one witness: `VIndField.WF.pos`
(F7) requires `∀ a ∈ r.args, D.NoBlock a` of every recursive field's index arguments, and
`VIndCtor.WF.args_fresh` (F5) requires the same of every constructor's result indices.  `K` listing
members of the block is a hypothesis of the theorem below (`hKB`), discharged here by
`tq_K_sub_blockNames` and **not** a global invariant of the framework, so block-free implies
companion-free; and the head of an *own*
occurrence is off `K` by definition.  Hence at every canonical own-head occurrence the whole
expression is `VExpr.NoConsts K` and `restore_noK` already applies.

`tq_ownOcc_noConsts_of_WF` is that statement, for an arbitrary block.  So:

> **Negative result.**  `restore_ownOcc`'s freedom in the residual arguments is not reachable from
> `VIndField.WF`/`VIndCtor.WF` at a canonical own-head occurrence, at *any* block.  `restore_noK`
> suffices there, and `restore_ownHeads` is a strictly stronger theorem with no witness in this
> theory.

**What is left open, precisely.**  The clause that pins a *stored* field type is `pos`'s last
conjunct, an `IsDefEqType` against `r.canonType`, not an equation — so the theorem below covers
the **canonical** result of every recursive field and every constructor, and covers stored types
only where they are canonical (`VIndCtor.Canonical`, e.g. `ntreeAux`).  It does not rule out a
stored type that mentions a companion constant somewhere defeq-irrelevant; §4's redex is exactly
such a stored type, and there the companion count happens to be zero.  Whether a WF stored type
can put a companion inside a *uniform own* occurrence's residual is **not** settled here.

**Lean's kernel enforces the same restriction**, by three separate messages — an own-member
occurrence carrying a block constant in an index argument is rejected in a constructor's result
type (`invalid return type`), in a recursive field's index (`arg #2 … contains a non valid
occurrence of the datatypes being declared`), and inside a nesting argument, where the *companion*
constructor's own field is the one rejected (`arg #3 of
'_nested.Lean4Lean.MRedex.TQWit.MI_1.node' …`).  Those three were **measured by `lean_run_code`
outside the repository, not machine-checked here**, and deliberately so: a rejected `inductive`
command still adds constants to the environment — `#print axioms` on them reports `sorryAx` — so
a `#guard_msgs` control over a rejected `inductive` would import three new `sorry`-dependent
constants into the build.  (Measured: the three `#guard_msgs` blocks were written, passed, and
were removed for exactly this reason.)

The three lemmas below are stated generally and kept local; they belong next to
`VIndRestore.restore_noK` in `Theory/Inductive/Restore.lean` as soon as a second consumer
appears. -/

theorem noConsts_mono {S S' : List Name} (h : ∀ n ∈ S, n ∈ S') :
    ∀ {e : VExpr}, VExpr.NoConsts S' e → VExpr.NoConsts S e
  | .bvar _, _ | .sort _, _ => trivial
  | .const _ _, hc => fun hm => hc (h _ hm)
  | .app _ _, hc => ⟨noConsts_mono h hc.1, noConsts_mono h hc.2⟩
  | .lam _ _, hc => ⟨noConsts_mono h hc.1, noConsts_mono h hc.2⟩
  | .forallE _ _, hc => ⟨noConsts_mono h hc.1, noConsts_mono h hc.2⟩

theorem noConsts_mkApp {S : List Name} {f : VExpr} (hf : VExpr.NoConsts S f) :
    ∀ (args : List VExpr), (∀ a ∈ args, VExpr.NoConsts S a) →
      VExpr.NoConsts S (f.mkApp args)
  | [], _ => hf
  | a :: as, ha =>
    noConsts_mkApp (f := .app f a)
      (show VExpr.NoConsts S (.app f a) from ⟨hf, ha a List.mem_cons_self⟩) as
      (fun b hb => ha b (List.mem_cons_of_mem _ hb))

theorem noConsts_bvars {S : List Name} (lo : Nat) :
    ∀ (n : Nat), ∀ a ∈ VExpr.bvars lo n, VExpr.NoConsts S a
  | 0, _, h => absurd h (by simp [VExpr.bvars])
  | n+1, a, h => by
    rw [VExpr.bvars, List.mem_cons] at h
    rcases h with rfl | h
    · trivial
    · exact noConsts_bvars lo n a h

/-- **The negative result, for an arbitrary block.**  A uniform occurrence of a member *off* `K`
whose residual arguments are block-free — which is what `VIndField.WF.pos` and
`VIndCtor.WF.args_fresh` guarantee of `r.args` and `C.args` — is `VExpr.NoConsts K` outright, so
`VIndRestore.restore_noK` applies to it and `restore_ownOcc` buys nothing. -/
theorem tq_ownOcc_noConsts_of_WF {D : VInductDecl'} {K : List Name}
    (hKB : ∀ n ∈ K, n ∈ D.blockNames) {j k : Nat} {args : List VExpr}
    (hown : (D.types.getD j default).name ∉ K)
    (hargs : ∀ a ∈ args, D.NoBlock a) : VExpr.NoConsts K (D.tyApp j k args) := by
  rw [VInductDecl'.tyApp]
  refine noConsts_mkApp (show VExpr.NoConsts K (.const _ D.ownLvls) from hown) _ fun a ha => ?_
  rcases List.mem_append.1 ha with h | h
  · exact noConsts_bvars k _ a h
  · exact noConsts_mono hKB (hargs a h)

/-- …hence the restoration is the identity there **by `restore_noK`**, with no appeal to the
`OwnHeads` rule.  This is the statement whose *failure* would have made the round positive. -/
theorem tq_restore_id_of_WF {R : VIndRestore} {D : VInductDecl'} {K : List Name}
    (hown : R.OwnId D K) (hKB : ∀ n ∈ K, n ∈ D.blockNames) {j k : Nat} {args : List VExpr}
    (hj : (D.types.getD j default).name ∉ K) (hargs : ∀ a ∈ args, D.NoBlock a) :
    R.restore D k (D.tyApp j k args) = D.tyApp j k args :=
  VIndRestore.restore_noK hown k _ (tq_ownOcc_noConsts_of_WF hKB hj hargs)

/-- The two hypotheses are exactly what the two `WF` clauses hand over, at this block: `K`'s one
name is a block name, and the own member's name is off `K`. -/
theorem tq_K_sub_blockNames : ∀ n ∈ tqK, n ∈ (tqAux tqAuxNodeB).blockNames := by decide

/-- **The instance at §4's own position.**  The companion field's `recArg` targets member `0` with
`args = [Prop]`; `Prop` is block-free, so `tq_restore_id_of_WF` gives the identity, and §4's
`tq_restore_redexBody_id` — the `restore_ownOcc` route — is redundant at this witness. -/
theorem tq_restore_redexBody_id_of_WF :
    tqRestore.restore (tqAux tqAuxNodeB) 2 ((tqAux tqAuxNodeB).tyApp 0 2 [.sort .zero])
      = (tqAux tqAuxNodeB).tyApp 0 2 [.sort .zero] :=
  tq_restore_id_of_WF tqRestore_ownId tq_K_sub_blockNames (by decide)
    (by intro a ha; rw [show a = .sort .zero from by simpa using ha]; trivial)

/-- …and the two routes are about the *same* expression: §4's `tqNt` **is** that `tyApp`. -/
theorem tq_nt_eq_tyApp : tqNt = (tqAux tqAuxNodeB).tyApp 0 2 [.sort .zero] := rfl

/-! ## §7 The companion-pointing positions, where the index DOES change something

`OwnHeads` fails at the user constructor's field and the restoration genuinely moves it — as at
`MRWit.MJ` and `MPWit.MP`, so the predicate is not satisfied by everything here either.  What the
index adds is visible in *what* the move produces: the residual index is appended **after** the
presented spine and is **not** restored, so the restored occurrence has `2 + 1` arguments where
the stored one had `1 + 1`.  At `MJ`, `MP` and `ntreeAux` the companion residual is `[]`
(`tq_cone_unindexed`), so this arity bookkeeping was untested. -/

def tqObjField : VExpr := (tqObj.fields.getD 0 default).type

/-- The companion-pointing occurrence, with a **non-empty** residual of its own. -/
theorem tq_uniformOcc_objField :
    (tqAux tqAuxNodeB).uniformOcc? 0 tqObjField = some (1, [.sort .zero]) := by decide

/-- **What the restoration produces**: `MI Prop (fun x => TQ #1 Prop) Prop` — the presented spine
of length 2, then the residual index `Prop`, carried through unrestored. -/
theorem tq_objField_restore_eq :
    tqRestore.restore (tqAux tqAuxNodeB) 0 tqObjField
      = .app (.app (.app (.const ``MI []) (.sort .zero))
          (.lam (.sort .zero) (.app (.app (.const ``TQ []) (.bvar 1)) (.sort .zero))))
        (.sort .zero) := rfl

theorem tq_objField_restore_ne :
    tqRestore.restore (tqAux tqAuxNodeB) 0 tqObjField ≠ tqObjField := by decide

/-- …so `OwnHeads` does **not** hold there, by the theorem contrapositively. -/
theorem tq_not_ownHeads_objField : ¬ (tqAux tqAuxNodeB).OwnHeads tqK 0 tqObjField :=
  fun h => tq_objField_restore_ne (VIndRestore.restore_ownHeads tqRestore_ownId h)

theorem tq_objFieldTypesR_ne_fields :
    tqObj.fieldTypesR (tqAux tqAuxNodeB) tqRestore ≠ tqObj.fields.map (·.type) := by decide

/-! ## §8 The stored-type case, **closed**: a companion inside a uniform own occurrence's
residual, at a stored field type the specification admits

§6 left exactly one case open, and named it precisely: `VIndField.WF.pos`'s last conjunct is
`env.IsDefEqType D.uvars Γ F.type (r.canonType D i)`, an `IsDefEqType` and **not** an equation,
so F7's `∀ a ∈ r.args, D.NoBlock a` constrains the *canonical* residual and says nothing about
what the **stored** type's residual contains.  §6's `tq_ownOcc_noConsts_of_WF` is therefore a
theorem about `D.tyApp j k args` — the canonical form — and it does not transfer to `F.type`.

This section closes the case *in the affirmative*: there is a stored field type at which

* the trigger fires and reports the block's **own** member (so `OwnHeads` holds and
  `restore_ownOcc`/`restore_ownHeads` apply, `tq_hostile_restore_id`),
* `VExpr.NoConsts tqK` is **false** (so `restore_noK` does not apply,
  `tq_hostile_not_noConsts`), and
* §6's theorem does not apply either, because its `hargs` is false of the *stored* residual
  (`tq_hostile_args_not_noBlock`) — the failure is located at the hypothesis, not at the
  conclusion,

and the type is one `VIndField.WF` **accepts**: §8.3 proves `VIndField.WF` of it outright, in a
concrete `Ordered` environment built in §8.4.  So the strengthening is load-bearing at a stored
type, which is what §6 could not decide.

**Read the gradings in §8.6 and §8.8 before quoting this as a win.**  What is closed is that the
*specification* admits such a stored type; **no block in this tree has one**, and the
construction cannot produce one (§8.6).  That is the honest scope. -/

/-- The residual index argument, stored hostilely: a β-redex whose *argument* is a companion
occurrence.  Definitionally `Prop` (§8.3), syntactically it names `_nested.MI_1`. -/
def tqHostileArg : VExpr :=
  .app (.lam (.sort (.succ .zero)) (.sort .zero))
    (.app (.app (.const tqNestedName []) (.bvar 1)) (.sort .zero))

/-- **The witness stored type**: `TQ #1 ((fun y : Type => Prop) (_nested.MI_1 #1 Prop))`, in the
context of the *second* field of `TQ.obj` — one earlier field, then the parameter at `#1`. -/
def tqHostile : VExpr := .app (.app (.const ``TQ []) (.bvar 1)) tqHostileArg

/-- The user's constructor with the hostile field **appended**: the genuine nesting field of §1.2
is field `0`, unchanged (`tq_objH_field0`), and the hostile stored type is field `1`.  So the
block below is the block of §1 with one extra stored field, not a different block. -/
def tqObjH : VIndCtor where
  name := ``TQ.obj
  params := [.sort (.succ .zero)]
  fields :=
    [{ type := .app (.app (.const tqNestedName []) (.bvar 0)) (.sort .zero),
       lvl := .succ .zero,
       recArg := some { binders := [], idx := 1, args := [.sort .zero] } },
     { type := tqHostile, lvl := .succ .zero,
       recArg := some { binders := [], idx := 0, args := [.sort .zero] } }]
  args := [.sort .zero]

theorem tq_objH_field0 : tqObjH.fields.getD 0 default = tqObj.fields.getD 0 default := rfl

/-- The hostile field's `recArg`, named: it points at the block's **own** member `0`, with the
canonical index argument `Prop`, which is block-free — F7 is satisfied *as F7 is stated*. -/
def tqHostileRec : VIndRecArg where
  binders := []
  idx := 0
  args := [.sort .zero]

theorem tq_hostileRec_stored : (tqObjH.fields.getD 1 default).recArg = some tqHostileRec := rfl

theorem tq_hostileRec_args_noBlock : ∀ a ∈ tqHostileRec.args, (tqAux tqAuxNodeB).NoBlock a := by
  intro a ha
  rw [show a = .sort .zero from by simpa [tqHostileRec] using ha]; trivial

/-- The block: §1's `tqAux tqAuxNodeB` with `TQ`'s constructor replaced by `tqObjH`.  Everything
`OwnId`, the trigger and `blockNames` read — the members' names, types and index telescopes, and
the parameter telescope — is unchanged, which is why §8.2's transfers are `rfl`. -/
def tqAuxH : VInductDecl' :=
  { tqAux tqAuxNodeB with
    types :=
      [{ (tqAux tqAuxNodeB).types.getD 0 default with ctors := [tqObjH] },
       (tqAux tqAuxNodeB).types.getD 1 default] }

/-! ### §8.1 The block's invariants transfer, and the trigger fires with a hostile residual -/

theorem tq_auxH_blockNames : tqAuxH.blockNames = [``TQ, tqNestedName] := rfl

theorem tq_auxH_np : tqAuxH.np = 1 := rfl

theorem tq_auxH_params : tqAuxH.params = (tqAux tqAuxNodeB).params := rfl

theorem tq_auxH_blockNames_nodup : tqAuxH.blockNames.Nodup := by decide

theorem tq_auxH_allNames_nodup : tqAuxH.allNames.Nodup := by decide

theorem tq_auxH_types0 : tqAuxH.types[0]? = some
    { name := ``TQ,
      type := .forallE (.sort (.succ .zero))
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))),
      indices := [.sort (.succ .zero)], ctors := [tqObjH] } := rfl

theorem tq_auxH_types1 : tqAuxH.types[1]? = (tqAux tqAuxNodeB).types[1]? := rfl

/-- `OwnId` at the new block — the §3 proof verbatim, because `OwnId` reads only the members'
names, levels, presented arguments and constructor names, none of which moved. -/
theorem tqRestore_ownId_H : tqRestore.OwnId tqAuxH tqK where
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [tqAuxH, tqAux] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [tqAuxH, tqAux] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [tqAuxH, tqAux] at hT
  recName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [tqAuxH, tqAux] at hT
  ctorName := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [tqAuxH, tqAux] at hT

/-- **The trigger fires on the stored type**, at the block's own member `0`, with the residual
the hostile β-redex.  `decide`: the trigger is a decision. -/
theorem tq_hostile_uniformOcc :
    tqAuxH.uniformOcc? 1 tqHostile = some (0, [tqHostileArg]) := by decide

/-- …and the residual is **not** block-free, which is the coordinate §6 could not reach: the
whole point of §6 is that F7 forces this to be *true* of `r.args`; it is false of the residual
the trigger reads off the **stored** type. -/
theorem tq_hostile_args_not_noBlock :
    ¬ ∀ a ∈ [tqHostileArg], tqAuxH.NoBlock a :=
  fun h => (h tqHostileArg List.mem_cons_self).2.1.1 (by decide)

/-- `restore_noK`'s hypothesis is **false** of the stored type. -/
theorem tq_hostile_not_noConsts : ¬ VExpr.NoConsts tqK tqHostile :=
  fun h => h.2.2.1.1 (by decide)

/-- `OwnHeads` holds of it, at one step. -/
theorem tq_hostile_ownHeads : tqAuxH.OwnHeads tqK 1 tqHostile :=
  .own tq_hostile_uniformOcc tq_auxH_types0 tq_own_notK

/-- **The conclusion, through `restore_ownOcc`.**  This is the instance §6 said it could not
find: a *stored* field type at an own-head occurrence where the whole-subterm test fails. -/
theorem tq_hostile_restore_id : tqRestore.restore tqAuxH 1 tqHostile = tqHostile :=
  VIndRestore.restore_ownOcc tqRestore_ownId_H tq_hostile_uniformOcc tq_auxH_types0 tq_own_notK

/-- …and the computation agrees, independently of the rule. -/
example : tqRestore.restore tqAuxH 1 tqHostile = tqHostile := by decide

/-! ### §8.2 The stored type is definitionally the canonical one — the step §55.7 expected to be
impossible

`tqHostileArg` β-reduces to `Prop`, so `tqHostile` is `IsDefEqType` to
`tqHostileRec.canonType tqAuxH 1 = TQ #1 Prop`, which is exactly what `VIndField.WF.pos`'s last
conjunct asks for.  The two environment premises are constant lookups for the block's **own**
member and for the **companion** — and both are constants `VInductDecl'.WF.ctors`'s environment
already holds, since it checks constructors in `env.addIndTypes D`, which declares every member of
the block (`VInductDecl'.typeConsts`).  Nothing here is smuggled in. -/

/-- Both members of the block are stored at this type: `Type → Type → Type`. -/
def tqMemberType : VExpr :=
  .forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))

theorem tq_memberType_eq :
    (tqAuxH.types.getD 0 default).type = tqMemberType
      ∧ (tqAuxH.types.getD 1 default).type = tqMemberType := ⟨rfl, rfl⟩

/-- The hostile field's own context, as `VIndCtor.WF.fields` builds it: the nesting field of
§1.2, then the parameter. -/
def tqHostileCtx : List VExpr :=
  [.app (.app (.const tqNestedName []) (.bvar 0)) (.sort .zero), .sort (.succ .zero)]

theorem tq_hostileCtx_eq :
    ((tqObjH.fields.take 1).map (·.type)).reverse ++ tqAuxH.params.reverse = tqHostileCtx := rfl

/-- The parameter, in the hostile field's context. -/
theorem tq_hostile_param_lookup : Lookup tqHostileCtx 1 (.sort (.succ .zero)) :=
  Lookup.succ (Lookup.zero (ty := .sort (.succ .zero)) (Γ := []))

theorem tq_hostile_param_hasType {env : VEnv} :
    env.HasType 0 tqHostileCtx (.bvar 1) (.sort (.succ .zero)) :=
  .bvar tq_hostile_param_lookup

/-- `Prop : Type`, in any context. -/
theorem tq_prop_hasType {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := .sortDF trivial trivial rfl

/-- Either member's constant, at its stored type. -/
theorem tq_member_const_hasType {env : VEnv} {U : Nat} {Γ : List VExpr} {n : Lean.Name}
    (h : env.constants n = some ⟨0, tqMemberType⟩) :
    env.HasType U Γ (.const n [])
      (.forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))) :=
  .constDF h nofun nofun rfl .nil

/-- The **companion** occurrence that sits inside the residual is perfectly well-typed: it is a
`Type`.  This is the fact that makes the case close rather than refute. -/
theorem tq_hostile_companion_hasType {env : VEnv}
    (hMI : env.constants tqNestedName = some ⟨0, tqMemberType⟩) :
    env.HasType 0 tqHostileCtx (.app (.app (.const tqNestedName []) (.bvar 1)) (.sort .zero))
      (.sort (.succ .zero)) :=
  have h1 : env.HasType 0 tqHostileCtx (.app (.const tqNestedName []) (.bvar 1))
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .appDF (tq_member_const_hasType hMI) tq_hostile_param_hasType
  .appDF h1 tq_prop_hasType

/-- `fun y : Type => Prop`, the eliminator that hides the companion. -/
theorem tq_hostile_lam_hasType {env : VEnv} :
    env.HasType 0 tqHostileCtx (.lam (.sort (.succ .zero)) (.sort .zero))
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .lamDF (.sortDF trivial trivial rfl) tq_prop_hasType

theorem tq_hostile_arg_hasType {env : VEnv}
    (hMI : env.constants tqNestedName = some ⟨0, tqMemberType⟩) :
    env.HasType 0 tqHostileCtx tqHostileArg (.sort (.succ .zero)) :=
  .appDF tq_hostile_lam_hasType (tq_hostile_companion_hasType hMI)

/-- **The β step.**  The residual is definitionally `Prop`, so the companion inside it is
invisible to `IsDefEqType`. -/
theorem tq_hostile_arg_defeq_prop {env : VEnv}
    (hMI : env.constants tqNestedName = some ⟨0, tqMemberType⟩) :
    env.IsDefEq 0 tqHostileCtx tqHostileArg (.sort .zero) (.sort (.succ .zero)) :=
  have hbody : env.HasType 0 (.sort (.succ .zero) :: tqHostileCtx) (.sort .zero)
      (.sort (.succ .zero)) := tq_prop_hasType
  .beta hbody (tq_hostile_companion_hasType hMI)

theorem tq_hostile_head_hasType {env : VEnv}
    (hTQ : env.constants ``TQ = some ⟨0, tqMemberType⟩) :
    env.HasType 0 tqHostileCtx (.app (.const ``TQ []) (.bvar 1))
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .appDF (tq_member_const_hasType hTQ) tq_hostile_param_hasType

theorem tq_hostile_hasType {env : VEnv}
    (hTQ : env.constants ``TQ = some ⟨0, tqMemberType⟩)
    (hMI : env.constants tqNestedName = some ⟨0, tqMemberType⟩) :
    env.HasType 0 tqHostileCtx tqHostile (.sort (.succ .zero)) :=
  .appDF (tq_hostile_head_hasType hTQ) (tq_hostile_arg_hasType hMI)

/-- **`VIndField.WF.pos`'s last conjunct, discharged at the hostile stored type.**  This is the
statement §55.7 item 1 of `docs/handoff-iota-stored.md` predicted would be refutable. -/
theorem tq_hostile_defeq_canon {env : VEnv}
    (hTQ : env.constants ``TQ = some ⟨0, tqMemberType⟩)
    (hMI : env.constants tqNestedName = some ⟨0, tqMemberType⟩) :
    env.IsDefEqType 0 tqHostileCtx tqHostile (tqHostileRec.canonType tqAuxH 1) :=
  ⟨.succ .zero, .appDF (tq_hostile_head_hasType hTQ) (tq_hostile_arg_defeq_prop hMI)⟩

/-! ### §8.3 …and the whole of `VIndField.WF` holds of it

Every clause, not just the defeq one.  `pos`'s block-freeness conjuncts are about `r.binders` and
`r.args` — the **canonical** data — and they are satisfied: `binders = []` and `args = [Prop]`.
That is the whole mechanism of the closure: F7 is a condition on `r`, and `r` is clean. -/

theorem tq_hostile_ctx_onCtx {env : VEnv}
    (hMI : env.constants tqNestedName = some ⟨0, tqMemberType⟩) :
    OnCtx tqHostileCtx (env.IsType 0) := by
  refine ⟨⟨trivial, ⟨_, .sortDF trivial trivial rfl⟩⟩, ⟨.succ .zero, ?_⟩⟩
  have h0 : env.HasType 0 [VExpr.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) :=
    .bvar (Lookup.zero (ty := .sort (.succ .zero)) (Γ := []))
  have h1 : env.HasType 0 [VExpr.sort (.succ .zero)] (.app (.const tqNestedName []) (.bvar 0))
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .appDF (tq_member_const_hasType hMI) h0
  exact .appDF h1 tq_prop_hasType

theorem tq_hostile_canonResult_hasType {env : VEnv}
    (hTQ : env.constants ``TQ = some ⟨0, tqMemberType⟩) :
    env.HasType 0 tqHostileCtx (tqHostileRec.canonResult tqAuxH 1) (.sort tqAuxH.lvl) :=
  .appDF (tq_hostile_head_hasType hTQ) tq_prop_hasType

theorem tq_hostile_hasArgs {env : VEnv} :
    env.HasArgs 0 tqHostileCtx (VExpr.liftTele 1 (tqAuxH.types.getD 0 default).indices)
      tqHostileRec.args :=
  .cons tq_prop_hasType .nil

/-- **The specification accepts the hostile stored field.**  `pre`, `Γ` and `i` are exactly what
`VIndCtor.WF.fields` supplies at field `1` of `tqObjH` (`tq_hostileCtx_eq`). -/
theorem tq_hostile_field_WF {env : VEnv}
    (hTQ : env.constants ``TQ = some ⟨0, tqMemberType⟩)
    (hMI : env.constants tqNestedName = some ⟨0, tqMemberType⟩) :
    VIndField.WF env tqAuxH (tqObjH.fields.take 1) tqHostileCtx 1
      (tqObjH.fields.getD 1 default) where
  hasType := tq_hostile_hasType hTQ hMI
  level := by
    intro ls
    simp [tqAuxH, tqAux, tqObjH, VLevel.eval, Lean.Nat.imax]
  pos := by
    refine ⟨by decide, rfl, by simp, tq_hostileRec_args_noBlock, ?_, ?_, ?_, ?_⟩
    · exact tq_hostile_ctx_onCtx hMI
    · exact tq_hostile_canonResult_hasType hTQ
    · rintro T' hT'
      cases hT'
      exact tq_hostile_hasArgs
    · exact tq_hostile_defeq_canon hTQ hMI
  binders_indep := by
    rintro r hr
    cases hr
    rintro i' t F' h1 h2 h3 k B hB
    exact absurd hB (by simp)

/-! ### §8.4 The two constant lookups are satisfiable — a closed witness

The template is `MRWit.mr_env_exists` (`Theory/Inductive/StoredIota.lean` §5.4): two `addConst`
steps over `VEnv.empty`.  Both members are stored at the same type, so one `VConstant.WF` serves
twice.  (This is *not* the staged environment of the real step — it is the minimum that makes
§8.3's premises inhabited, so that §8.3 is not green by an unsatisfiable hypothesis.) -/

theorem tq_memberType_hasType {env : VEnv} :
    env.HasType 0 [] tqMemberType
      (.sort (.imax (.succ (.succ .zero))
        (.imax (.succ (.succ .zero)) (.succ (.succ .zero))))) :=
  .forallEDF (.sortDF trivial trivial rfl)
    (.forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl))

theorem tq_memberType_constant_wf {env : VEnv} : VConstant.WF env ⟨0, tqMemberType⟩ :=
  ⟨_, tq_memberType_hasType⟩

theorem tq_env_exists : ∃ env : VEnv, env.Ordered ∧
    env.constants ``TQ = some ⟨0, tqMemberType⟩ ∧
    env.constants tqNestedName = some ⟨0, tqMemberType⟩ := by
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := VEnv.empty) (name := ``TQ)
    (ci := ⟨0, tqMemberType⟩) rfl
  have c1 := VEnv.addConst_constants_eq he1
  have hTQ : e1.constants ``TQ = some ⟨0, tqMemberType⟩ := by rw [c1]; exact if_pos rfl
  have ho1 : e1.Ordered := .const .empty tq_memberType_constant_wf he1
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := tqNestedName)
    (ci := ⟨0, tqMemberType⟩) (by rw [c1]; exact if_neg (by decide))
  have c2 := VEnv.addConst_constants_eq he2
  refine ⟨e2, .const ho1 tq_memberType_constant_wf he2, ?_, by rw [c2]; exact if_pos rfl⟩
  rw [c2]
  exact (if_neg (show ¬ (tqNestedName = ``TQ) from by decide)).trans hTQ

/-- **The two lookups are the *staged* environment's, not a convenient pair.**
`VInductDecl'.WF.ctors` checks constructors in `env.addIndTypes D`, and at `tqAuxH` over the empty
environment that is *exactly* the environment §8.4 builds: `typeConsts` is
`[(TQ, ⟨0, tqMemberType⟩), (_nested.MI_1, ⟨0, tqMemberType⟩)]`, so the two `addConst` steps above
**are** `addIndTypes`.  This is what makes §8.3's premises the specification's own, rather than an
assumption chosen to make the closure work. -/
theorem tq_typeConsts_eq : tqAuxH.typeConsts =
    [(``TQ, ⟨0, tqMemberType⟩), (tqNestedName, ⟨0, tqMemberType⟩)] := rfl

theorem tq_staged_env_exists : ∃ env : VEnv, VEnv.empty.addIndTypes tqAuxH = some env ∧
    env.Ordered ∧ env.constants ``TQ = some ⟨0, tqMemberType⟩ ∧
    env.constants tqNestedName = some ⟨0, tqMemberType⟩ := by
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := VEnv.empty) (name := ``TQ)
    (ci := ⟨0, tqMemberType⟩) rfl
  have c1 := VEnv.addConst_constants_eq he1
  have hTQ : e1.constants ``TQ = some ⟨0, tqMemberType⟩ := by rw [c1]; exact if_pos rfl
  have ho1 : e1.Ordered := .const .empty tq_memberType_constant_wf he1
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := tqNestedName)
    (ci := ⟨0, tqMemberType⟩) (by rw [c1]; exact if_neg (by decide))
  have c2 := VEnv.addConst_constants_eq he2
  refine ⟨e2, ?_, .const ho1 tq_memberType_constant_wf he2, ?_,
    by rw [c2]; exact if_pos rfl⟩
  · show VEnv.empty.addConstList tqAuxH.typeConsts = some e2
    rw [tq_typeConsts_eq]
    simp [VEnv.addConstList, he1, he2]
  · rw [c2]
    exact (if_neg (show ¬ (tqNestedName = ``TQ) from by decide)).trans hTQ

/-- **§8.3 with every premise discharged.**  The specification's field clause accepts the hostile
stored type in a *concrete* `Ordered` environment. -/
theorem tq_hostile_field_WF_closed : ∃ env : VEnv, env.Ordered ∧
    VIndField.WF env tqAuxH (tqObjH.fields.take 1) tqHostileCtx 1
      (tqObjH.fields.getD 1 default) := by
  obtain ⟨env, henv, hTQ, hMI⟩ := tq_env_exists
  exact ⟨env, henv, tq_hostile_field_WF hTQ hMI⟩

/-- **The closure, in one statement.**  In the environment `VInductDecl'.WF.ctors` itself supplies,
the specification's field clause accepts a stored field type at which `restore_noK` fails and
`restore_ownOcc` succeeds. -/
theorem tq_hostile_field_WF_staged : ∃ env : VEnv, VEnv.empty.addIndTypes tqAuxH = some env ∧
    env.Ordered ∧ VIndField.WF env tqAuxH (tqObjH.fields.take 1) tqHostileCtx 1
      (tqObjH.fields.getD 1 default) := by
  obtain ⟨env, hstage, henv, hTQ, hMI⟩ := tq_staged_env_exists
  exact ⟨env, hstage, henv, tq_hostile_field_WF hTQ hMI⟩

/-! ### §8.5 Why this makes the strengthening load-bearing, and where the alternatives fail

The stored type **is** a `tyApp` — `tq_hostile_eq_tyApp` — so §6's `tq_restore_id_of_WF` is a
statement *about this very expression*, and it does not apply: its `hargs` is false here
(`tq_hostile_args_not_noBlock`).  Likewise `restore_noK`'s `VExpr.NoConsts` is false
(`tq_hostile_not_noConsts`).  The failure is at the hypothesis of each, and the conclusion is
nonetheless true (`tq_hostile_restore_id`, and `decide` agrees).  So on the *stored* telescope —
the telescope ruling 122e moved the whole iota layer onto — `restore_ownOcc` proves something its
corollary cannot. -/

theorem tq_hostile_eq_tyApp : tqHostile = tqAuxH.tyApp 0 1 [tqHostileArg] := rfl

theorem tq_objH_fieldTypesR_split :
    tqObjH.fieldTypesR tqAuxH tqRestore
      = [tqRestore.restore tqAuxH 0 (tqObjH.fields.getD 0 default).type,
         tqRestore.restore tqAuxH 1 tqHostile] := rfl

/-- **The stored entry is fixed, and only the rule says so.**  Entry `1` of `TQ.obj`'s restored
field telescope is the stored type itself. -/
theorem tq_objH_entry1_fixed :
    (tqObjH.fieldTypesR tqAuxH tqRestore).getD 1 default
      = (tqObjH.fields.getD 1 default).type := by
  rw [tq_objH_fieldTypesR_split]; exact tq_hostile_restore_id

/-- …while entry `0` — the genuine nesting field — still **moves**, as at `MRWit.MJ` and
`MPWit.MP`.  So the constructor is not one where the restoration is globally trivial: the two
entries are on opposite sides of the rule. -/
theorem tq_objH_entry0_moves :
    (tqObjH.fieldTypesR tqAuxH tqRestore).getD 0 default
      ≠ (tqObjH.fields.getD 0 default).type := by decide

/-- **`Faithful` does not exclude the hostile block.**  Every clause of
`VIndRestore.Faithful` is guarded by `T.name ∈ K`, and `tqAuxH` differs from §1's block only in
the constructors of the member `TQ`, which is **off** `K`.  So the hostile block inherits
`Faithful` from §1's block verbatim — nothing in `VEnv.AddNested`'s restoration obligations sees
the hostile field. -/
theorem tq_auxH_faithful {env : VEnv} {npJ : Nat → Nat}
    (h : tqRestore.Faithful (tqAux tqAuxNodeB) env tqK npJ) :
    tqRestore.Faithful tqAuxH env tqK npJ where
  ty_agree := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; exact h.ty_agree 1 _ rfl hK
    · simp [tqAuxH, tqAux] at hT
  ctor_agree := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT
      intro C hC
      rw [show ((tqAux tqAuxNodeB).types.getD 1 default).ctors = [tqAuxNodeB] from rfl] at hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      exact h.ctor_agree 1 _ rfl hK tqAuxNodeB List.mem_cons_self
    · simp [tqAuxH, tqAux] at hT
  ctors_complete := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; exact h.ctors_complete 1 _ rfl hK
    · simp [tqAuxH, tqAux] at hT

/-! ### §8.6 Anti-vacuity, measured: **no block in this tree has such a stored type**

The closure above is a statement about what the *specification* accepts.  This subsection measures
the other half, because it is the half that decides how much the closure is worth.

`storedCleanB D K` decides: *at every constructor field of `D`, if the trigger fires on the
**stored** type, is the residual free of `K`-names?*  That is precisely the condition under which
`VIndRestore.restore_noK` suffices at every stored occurrence.  It is `true` at every block in the
witness cone and `false` at `tqAuxH` — so §8 exhibits the first block in the tree at which the
strengthening is needed, and it is a block **I wrote for the purpose**, not one any construction
produces.

These two definitions and the bridge lemma belong beside `VIndRestore.restore_noK` in
`Theory/Inductive/Restore.lean` if a second consumer appears; kept local here on the same
convention as §6's three helpers. -/

/-- Boolean twin of `VExpr.NoConsts` (which has no `Decidable` instance — see
`MRWit.mr_redex_noK`'s docstring). -/
def hasConstB (K : List Name) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const c _ => decide (c ∈ K)
  | .app a b | .lam a b | .forallE a b => hasConstB K a || hasConstB K b

theorem hasConstB_eq_false_iff {K : List Name} :
    ∀ {e : VExpr}, hasConstB K e = false ↔ VExpr.NoConsts K e
  | .bvar _ | .sort _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | .const c _ => by simp [hasConstB, VExpr.NoConsts]
  | .app a b => by
    show (hasConstB K a || hasConstB K b) = false ↔ (VExpr.NoConsts K a ∧ VExpr.NoConsts K b)
    rw [Bool.or_eq_false_iff]
    exact and_congr hasConstB_eq_false_iff hasConstB_eq_false_iff
  | .lam a b => by
    show (hasConstB K a || hasConstB K b) = false ↔ (VExpr.NoConsts K a ∧ VExpr.NoConsts K b)
    rw [Bool.or_eq_false_iff]
    exact and_congr hasConstB_eq_false_iff hasConstB_eq_false_iff
  | .forallE a b => by
    show (hasConstB K a || hasConstB K b) = false ↔ (VExpr.NoConsts K a ∧ VExpr.NoConsts K b)
    rw [Bool.or_eq_false_iff]
    exact and_congr hasConstB_eq_false_iff hasConstB_eq_false_iff

/-- **The scan.**  At every stored field type on which the trigger fires, is the residual
`K`-free?  `true` means `restore_noK` covers every stored occurrence of the block. -/
def storedCleanB (D : VInductDecl') (K : List Name) : Bool :=
  D.ctorsAll.all fun p => p.2.fields.zipIdx.all fun q =>
    match D.uniformOcc? q.2 q.1.type with
    | some (_, rest) => rest.all fun a => !hasConstB K a
    | none => true

/-- The bridge from the Boolean scan to `VExpr.NoConsts`, so that the `decide`s below are a
statement about the specification and not about a `Bool`. -/
theorem noConsts_of_storedCleanB {D : VInductDecl'} {K : List Name}
    (h : storedCleanB D K = true) {t : Nat} {C : VIndCtor} (hC : (t, C) ∈ D.ctorsAll)
    {F : VIndField} {i : Nat} (hF : (F, i) ∈ C.fields.zipIdx)
    {j : Nat} {rest : List VExpr} (hu : D.uniformOcc? i F.type = some (j, rest)) :
    ∀ a ∈ rest, VExpr.NoConsts K a := by
  rw [storedCleanB, List.all_eq_true] at h
  have h1 := h _ hC
  rw [List.all_eq_true] at h1
  have h2 := h1 _ hF
  simp only [hu, List.all_eq_true] at h2
  intro a ha
  exact hasConstB_eq_false_iff.1 (by simpa using h2 a ha)

/-- **`tqAuxH` is the block the scan flags** — and the only one. -/
theorem tq_auxH_not_storedClean : storedCleanB tqAuxH tqK = false := by decide

/-- **Every block in the witness cone is clean**, including §1's own block: so at all of them
`restore_noK` covers every stored uniform occurrence, and §8's strengthening buys nothing.  The
`tqAux tqAuxNodeB` entry is the sharpest one — it is the same members, the same `K` and the same
restoration as `tqAuxH`; only the stored field differs. -/
theorem tq_cone_storedClean :
    storedCleanB (tqAux tqAuxNodeB) tqK = true
      ∧ storedCleanB (MRWit.mrAux MRWit.mrAuxNodeB) MRWit.mrK = true
      ∧ storedCleanB (MPWit.mpAux MPWit.mpAuxNodeB) MPWit.mpK = true
      ∧ storedCleanB InductiveDeclExamples.ntreeAux InductiveDeclExamples.ntreeK = true
      ∧ storedCleanB InductiveDeclExamples.nfnAux InductiveDeclExamples.nfnK = true := by
  decide

/-- …and the *construction* cannot produce a flagged block: `VNestedOcc.ctor` builds the
companion constructor's recursive field as the head-β redex `(fun x => I p π) k`
(`tq_auxNodeB_built`, `MRWit`/`MPWit`'s `Built` equations), whose residual is a `bvar` run and a
sort.  So the hostile stored type has to be written by hand, as §8 writes it. -/
theorem tq_built_storedClean :
    storedCleanB (tqAux (tqOcc.ctor (tqAux tqAuxNodeB).header tqRestore miNode)) tqK = true := by
  decide

/-! ### §8.7 The load-bearing instance, at an existing consumer

`VIndRestore.substC_atRec_fieldTypes_defeq_of_noK` (`Theory/Inductive/NestedTele.lean` §T15.7) is
the form ruling 122e's payoff is currently used in: it charges the field-telescope obligation only
at fields whose **stored** type mentions a companion.  At `tqObjH`'s field `1` that premise
**fires** (`tq_hostile_not_noConsts`), so that form charges a real obligation there.  The sharper
form `substC_atRec_fieldTypes_defeq'` charges it only where the substituted entries *differ*, and
at that field they do not — but the only route to that is `restore_ownOcc`.

So the two forms of §T15.7 separate exactly here, and this is the concrete cost of not having the
strengthening: without it, `_of_noK` is the best available and the hostile field carries an
obligation that is in fact empty. -/

theorem tq_hostile_entry_substC_eq (σ : CSubst) :
    (tqAuxH.atRec tqHostile).substC σ
      = (tqAuxH.atRec (tqRestore.restore tqAuxH 1 tqHostile)).substC σ := by
  rw [tq_hostile_restore_id]

/-- **`substC_atRec_fieldTypes_defeq'`'s premise is false at the hostile field** — so that form
asks nothing there — while `_of_noK`'s premise is true.  Both halves in one statement. -/
theorem tq_hostile_obligation_split (σ : CSubst) :
    ¬ ((tqAuxH.atRec tqHostile).substC σ
        ≠ (tqAuxH.atRec (tqRestore.restore tqAuxH 1 tqHostile)).substC σ)
      ∧ ¬ VExpr.NoConsts tqK (tqObjH.fields.getD 1 default).type :=
  ⟨fun h => h (tq_hostile_entry_substC_eq σ), tq_hostile_not_noConsts⟩

/-! ### §8.8 What the real kernel does with the same shape — and the ruling this asks for

Measured with `lean_run_code` on scratch snippets **outside the repository**, for the reason §6
gives: a rejected `inductive` still adds `sorryAx`-carrying constants to the environment, so a
`#guard_msgs` control over one would import three `sorry`-dependent constants into the build.  The
proxy is a plain **mutual** block, because the kernel's positivity check does not distinguish a
companion from any other member of the block being declared — `has_ind_occ` is one list.

Four declarations across two runs, four verdicts:

| declaration | verdict |
| --- | --- |
| `TT : Type → Type` with field `TT Prop` (clean) | **accepted** |
| field `TT ((fun _ : Type => Prop) Nat)` — a β redex in the index, no block constant in it | **accepted** |
| field `TT ((fun _ : Type => Prop) (SS Prop))` — a *sibling* member hidden under the redex | **rejected**: `(kernel) arg #1 of 'TT.hostile' contains a non valid occurrence of the datatypes being declared` |
| field `TT ((fun _ : Type => Prop) (TT Prop))` — the **own** member hidden under the redex | **rejected**, same message, at that block's own `hostile` |

So the redex is not what offends: a block constant *anywhere* in a stored index argument is, whether
it survives whnf or not.  **Lean's kernel is strictly stricter here than `VIndField.WF.pos` is**, and
that is the real content of §8:

> The stored-type case closes because F7's `some` branch constrains the **`VIndRecArg` record**
> (`r.binders`, `r.args`) and pins `F.type` only up to `IsDefEqType`.  That slack is deliberate in
> the `none` branch — the docstring there explains why a syntactic `D.NoBlock F.type` would reject
> declarations both kernels accept — but in the `some` branch it admits stored types the C++ kernel
> **rejects**.  `restore_ownOcc` is load-bearing for the specification exactly on those.

This is slack, not unsoundness: the refinement direction is *checker ⇒ spec*, and a more permissive
spec is discharged by a stricter check.  But it hands the ledger a choice that §6 could not see:

1. **Keep F7 as it is.**  Then `restore_ownOcc`/`restore_ownHeads` are load-bearing, §8 is their
   witness, and nothing further is owed.
2. **Tighten F7's `some` branch** to require the *stored* type's own-head residual to be
   block-free.  Then §8's witness stops being well-formed, the stored-type case is *refuted* after
   all, and `restore_noK` suffices everywhere — at the cost of one new spec conjunct, whose
   refinement obligation the measurements above suggest the kernel already discharges.

Either way the corner is now decided by a ruling rather than by a missing theorem, which is what §6
left open. -/

end TQWit
end MRedex
end Lean4Lean
