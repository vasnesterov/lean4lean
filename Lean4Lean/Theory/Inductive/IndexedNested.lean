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

end TQWit
end MRedex
end Lean4Lean
