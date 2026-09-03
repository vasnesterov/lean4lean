import Lean4Lean.Theory.Inductive.IndexedNested
import Lean4Lean.Theory.Inductive.RecTyped
import Lean4Lean.Theory.Typing.StrengthenAxiom

/-!
# The indexed nested block: the `WF`-staging flag, settled at witnesses

`docs/handoff-valat.md` §2(c) flagged, and explicitly did **not** claim:

> If a nested block's *foreign* member has an index whose type depends on a foreign **parameter**,
> then `member.indices = instAllTele (src.indices.map (·.instL lvls)) args 0` **mentions the
> spine**, and `WF.indices_constsIn` then forces the spine to be `env`-clean — which a nesting
> spine is not.  So `D.WF env` looks **unsatisfiable** for that class of nested declarations …
> If it is real it is a staging defect in `VInductDecl'.WF`.

This file settles it in both directions, at witnesses rather than by argument.

* **§2 the flag is REAL**: `¬ wiAux.WF env` for *every* `env` that does not already declare the
  block's own head — and the refutation fires twice over, once through `VIndType.WF.indices` and
  once through `VIndType.WF.isType`, because the built companion's *stored type* mentions the own
  head as well.  The member is the one `VNestedOcc.member` builds (`wi_member_built`, `rfl`), so
  this is the specification's own construction, not a hand-written record.
* **§3 it is NOT a defect**, and that is a measurement outside Lean4Lean: **Lean's own kernel
  rejects the same class**, with `(kernel) unknown constant`, because `check_inductive_types`
  (`~/lean4/src/kernel/inductive.cpp:254`) type-checks *every* member's stored type before
  `declare_inductive_types` (`:360`) adds any of the block's constants — the identical staging to
  `VInductDecl'.WF`'s `types` clause.  So `kernel_sound`'s coverage is not narrowed: the class is
  empty of Lean declarations.  §3 records the verdicts; they were measured with `lake env lean` on
  scratch files and are not re-derivable inside Lean4Lean.
* **§4 the spec DOES cover the indexed nested block**: `tqAux.WF env` — `MRedex.TQWit`'s block
  (`Theory/Inductive/IndexedNested.lean`), the one indexed nested block in the tree, both of whose
  members carry an index and whose companion is built by `VNestedOcc.member` from an *indexed*
  container.  So the flag's scope is exactly the class the kernel rejects, and no wider.
* **§5 the three never-exercised slots**: `VIndRestore.MotiveHargs`' `hpi`/`hAs`/`hsort` are the
  `T.indices = []` identities at every witness in the tree (`docs/handoff-faminhab.md` §4b item 1,
  which graded the family *inhabited, one slot of four exercised*).  At `tqAux`'s **indexed**
  companion they are not: `hAs` is a real `HasArgs.cons` against a one-entry index telescope.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkApp bvars instAll instAllTele splitPis)

/-! ## §1 The general refutations

Two of `VIndType.WF`'s three clauses are staged at the **pre-block** environment, so each one
refutes a block whose member's data mentions a constant `env` does not declare.  Both are the
`VIndType`-level statement of `Verify/Inductive/ValAtPrice.lean` §4's `WF.indices_constsIn`, in
the contrapositive and *in the `Theory` layer* (that file is under `Verify`, which `Theory` may
not import; `ctxConstsIn_of_index` below is the `ctxConstsIn_mem` it needs). -/

/-- Every entry of a constant-closed context is constant-closed. -/
theorem ctxConstsIn_of_index {P : Name → Prop} : ∀ {Γ : List VExpr}, CtxConstsIn P Γ →
    ∀ A ∈ Γ, A.ConstsIn P
  | [], _, _, hA => nomatch hA
  | _ :: Γ, h, A, hA => by
    rcases List.mem_cons.1 hA with rfl | hA
    · exact h.2
    · exact ctxConstsIn_of_index (Γ := Γ) h.1 A hA

/-- **`D.WF env` is refuted by one dirty index type.**  `VIndType.WF.indices` is an `OnCtx` at
`env`, so every entry of every member's index telescope mentions only `env`'s constants. -/
theorem VInductDecl'.not_WF_of_index_undeclared {env : VEnv} {D : VInductDecl'}
    (henv : env.Ordered) {T : VIndType} (hT : T ∈ D.types) {A : VExpr} (hA : A ∈ T.indices)
    (hbad : ¬ A.ConstsIn env.contains) : ¬ D.WF env := by
  intro hD
  refine hbad (ctxConstsIn_of_index
    (VEnv.ctxConstsIn_of_onCtx henv (hD.types T hT).indices) A ?_)
  exact List.mem_append_left _ (List.mem_reverse.2 hA)

/-- **…and by a dirty stored type.**  `VIndType.WF.isType` is staged at `env` too. -/
theorem VInductDecl'.not_WF_of_type_undeclared {env : VEnv} {D : VInductDecl'}
    (henv : env.Ordered) {T : VIndType} (hT : T ∈ D.types)
    (hbad : ¬ T.type.ConstsIn env.contains) : ¬ D.WF env := by
  intro hD
  obtain ⟨_, h⟩ := (hD.types T hT).isType
  exact hbad (h.constsIn henv.constsIn trivial).1

namespace IndexedWit

/-! ## §2 The flag, instantiated: a foreign index type that depends on a foreign parameter

`WI : (α : Type) → α → Type` is the smallest foreign block in the flagged class: its one index's
type **is** its one parameter.  Nesting through it at `α := TI`, the block's own member, is what
`ElimNestedInductive` would be asked to do for `TI.node : WI TI t → TI`; the companion
`VNestedOcc.member` builds then has

* `type = TI → Type`, and
* `indices = [TI]`,

both of which mention a member of the very block being declared. -/

def tiName : Name := `IndexedWit.TI
def wiName : Name := `IndexedWit.WI
def wiAuxName : Name := `_nested.IndexedWit.WI_1

/-- **The foreign member, with a parameter-dependent index type.** -/
def wiSrc : VIndType where
  name := wiName
  type := .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort (.succ .zero)))
  indices := [.bvar 0]
  ctors := []

def wiDecl : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero)]
  lvl := .succ .zero
  isLE := false
  types := [wiSrc]

/-- **The nesting occurrence**: the parameter slot the index type depends on is filled with the
block's own member. -/
def wiOcc : VNestedOcc where
  decl := wiDecl
  idx := 0
  lvls := []
  args := [.const tiName []]
  auxName := wiAuxName
  ctorName := id

def wiRestore : VIndRestore where
  tyName j := if j = 1 then wiName else tiName
  tyLvls _ := []
  tyArgs _ := [.const tiName []]
  ctorName := id
  recName := id

/-- The block: the user's member `TI : Type`, and the companion. -/
def wiAux : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := false
  types :=
    [{ name := tiName, type := .sort (.succ .zero), indices := [], ctors := [] },
     { name := wiAuxName, type := .forallE (.const tiName []) (.sort (.succ .zero)),
       indices := [.const tiName []], ctors := [] }]

/-- **The companion is the one the construction builds** — not a hand-written record. -/
theorem wi_member_built :
    wiAux.types[1]? = some (wiOcc.member wiAux.header wiRestore) := rfl

/-- …and this is where the own head enters it: `instAllTele` puts the spine in the index slot. -/
theorem wi_member_indices :
    (wiOcc.member wiAux.header wiRestore).indices = [.const tiName []] := rfl

theorem wi_member_type :
    (wiOcc.member wiAux.header wiRestore).type
      = .forallE (.const tiName []) (.sort (.succ .zero)) := rfl

/-- The source's index type really does depend on the foreign parameter (else the flag's premise
is not met). -/
theorem wi_src_index_is_param : wiSrc.indices = [.bvar 0] := rfl

/-- **THE FLAG IS REAL.**  For every environment in which the block's own head is fresh — which
is every environment a declaration step is ever run at — `wiAux` has **no** well-formedness.
Through `VIndType.WF.indices`. -/
theorem wi_not_WF_indices {env : VEnv} (henv : env.Ordered) (hfresh : ¬ env.contains tiName) :
    ¬ wiAux.WF env :=
  VInductDecl'.not_WF_of_index_undeclared henv
    (T := wiOcc.member wiAux.header wiRestore)
    (List.mem_of_getElem? wi_member_built) (A := .const tiName [])
    (by rw [wi_member_indices]; exact List.mem_cons_self) hfresh

/-- **…and again through `VIndType.WF.isType`**, because the built companion's *stored type*
mentions the own head too: that is the flag's second half ("the same argument applies to
`WF.isType` when the foreign member's post-parameter codomain depends on a parameter"). -/
theorem wi_not_WF_isType {env : VEnv} (henv : env.Ordered) (hfresh : ¬ env.contains tiName) :
    ¬ wiAux.WF env :=
  VInductDecl'.not_WF_of_type_undeclared henv
    (T := wiOcc.member wiAux.header wiRestore)
    (List.mem_of_getElem? wi_member_built)
    (by rw [wi_member_type]; exact fun h => hfresh h.1)

/-- **Existentially closed**: an environment at which it fires, nothing hypothesised.
`VEnv.empty` declares nothing, so the own head is fresh there. -/
theorem wi_not_WF_empty : ¬ wiAux.WF VEnv.empty :=
  wi_not_WF_indices .empty nofun

/-! ### §2a …and the freshness hypothesis is free at every declaration step

`wi_not_WF_indices` is stated at an arbitrary `env` in which the own head is fresh, and that is
not a restriction: `VEnv.addConst` returns `none` on a name already taken, so an environment at
which the block's types can be added at all has the own head fresh.  Hence **no environment at
which the declaration step is even defined satisfies `wiAux.WF`** — which is the unsatisfiability
claim in the only form that matters, since `VInductDecl'.WF.ctors` is vacuous exactly when
`addIndTypes` fails. -/

theorem wi_fresh_of_step {env e : VEnv} (h : env.addIndTypes wiAux = some e) :
    ¬ env.contains tiName := by
  rintro ⟨ci, hc⟩
  simp [VEnv.addIndTypes, VEnv.addConstList, VInductDecl'.typeConsts, wiAux,
    VEnv.addConst, hc] at h

/-- **THE UNSATISFIABILITY, in the form the declaration step sees it.** -/
theorem wi_not_WF_of_step {env e : VEnv} (henv : env.Ordered)
    (h : env.addIndTypes wiAux = some e) : ¬ wiAux.WF env :=
  wi_not_WF_indices henv (wi_fresh_of_step h)

/-! ### §2b An environment that declares the FOREIGN block, so the witness is not vacuous by
absence of the container -/

def wiEnv : VEnv :=
  { VEnv.empty with constants := fun n => if wiName = n then some ⟨0, wiSrc.type⟩ else none }

theorem wiEnv_eq : VEnv.empty.addConst wiName ⟨0, wiSrc.type⟩ = some wiEnv := rfl

theorem wiEnv_wi : wiEnv.constants wiName = some ⟨0, wiSrc.type⟩ := rfl

theorem wiEnv_ordered : wiEnv.Ordered :=
  .const .empty ⟨_, by type_tac⟩ wiEnv_eq

/-- **CLOSED, at an environment that declares the container.**  `WI` is present with its declared
type; the block's own head and the companion's name are fresh; and `wiAux` has no `WF`. -/
theorem wi_not_WF_wiEnv :
    wiEnv.constants wiName = some ⟨0, wiSrc.type⟩ ∧ wiEnv.Ordered ∧ ¬ wiAux.WF wiEnv :=
  ⟨wiEnv_wi, wiEnv_ordered, wi_not_WF_indices wiEnv_ordered (by rintro ⟨ci, hc⟩; simp [wiEnv, tiName, wiName] at hc)⟩

end IndexedWit

/-! ## §2c The class-level statement, at the built member

The witness above is one instance; this is the statement in the flag's own vocabulary — the
expression is `VNestedOcc.member`'s `indices` field verbatim
(`Theory/Inductive/NestedBuild.lean:448`). -/

theorem VNestedOcc.not_WF_of_member_index_undeclared {env : VEnv} {D : VInductDecl'}
    {N : VNestedOcc} {R : VIndRestore} {j : Nat} (henv : env.Ordered)
    (hj : D.types[j]? = some (N.member D.header R))
    {A : VExpr} (hA : A ∈ instAllTele (N.src.indices.map (·.instL N.lvls)) N.args 0)
    (hbad : ¬ A.ConstsIn env.contains) : ¬ D.WF env :=
  VInductDecl'.not_WF_of_index_undeclared henv (List.mem_of_getElem? hj) hA hbad

/-! ## §4 …and the spec DOES cover the indexed nested block

`MRedex.TQWit`'s `tqAux tqAuxNodeB` (`Theory/Inductive/IndexedNested.lean` §1) is the tree's one
indexed nested block: `TQ (α : Type) : Type → Type` nesting through the **indexed** container
`MI (α : Type) (β : α → Type) : Type → Type`, so *both* members carry an index
(`tq_indices`, `tq_aux_indices`) and the companion is `VNestedOcc.member`'s output
(`tq_member_built`).  Its index type is `Type` — closed, hence outside §2's class, hence exactly
the shape F2's row 1 says Lean accepts.

`VInductDecl'.WF` holds there.  The proof is `ParamRedex.lean` §11's `mpAuxB_WF` — the *unindexed*
parameterised redex block — with the four places the index shows up filled in rather than
discharged by `.nil`:

* `VIndType.WF.indices` is an `OnCtx` over a **two**-entry context (`tq_indexCtx_WF`) instead of a
  one-entry one;
* `VIndCtor.WF.args_len` is `1 = 1` instead of `0 = 0`;
* `VIndCtor.WF.args_ty` and `VIndField.WF.pos`'s index clause are real `HasArgs.cons` steps
  against a one-entry index telescope, where every earlier nested witness has `.nil`
  (`tq_cone_unindexed`).

So: **an indexed nested block is buildable in the current spec and `D.WF` is satisfiable there**
— outcome 3 of the brief is refuted, and the flag's scope is exactly §2's class. -/

namespace MRedex
namespace TQWit

section
variable {env : VEnv}

theorem tq_params_WF :
    OnCtx (tqAux tqAuxNodeB).params.reverse (env.IsType (tqAux tqAuxNodeB).uvars) :=
  ⟨trivial, _, .sort (by decide)⟩

/-- **The clause the unindexed witnesses cannot exercise**: the index telescope's own context,
`indices.reverse ++ params.reverse`, has *two* entries here. -/
theorem tq_indexCtx_WF (T : VIndType) (hT : T ∈ (tqAux tqAuxNodeB).types) :
    OnCtx (T.indices.reverse ++ (tqAux tqAuxNodeB).params.reverse)
      (env.IsType (tqAux tqAuxNodeB).uvars) := by
  simp only [tqAux, List.mem_cons, List.not_mem_nil, or_false] at hT
  obtain rfl | rfl := hT <;> exact ⟨⟨trivial, _, .sort (by decide)⟩, _, .sort (by decide)⟩

theorem tq_const_staged {env₂ : VEnv} (hs : env.addIndTypes (tqAux tqAuxNodeB) = some env₂) :
    env₂.constants ``TQ = some ⟨0, tqMemberType⟩ :=
  VEnv.addConstList_constants hs (``TQ, ⟨0, tqMemberType⟩) (by exact List.Mem.head _)

theorem tq_nested_const_staged {env₂ : VEnv}
    (hs : env.addIndTypes (tqAux tqAuxNodeB) = some env₂) :
    env₂.constants tqNestedName = some ⟨0, tqMemberType⟩ :=
  VEnv.addConstList_constants hs (tqNestedName, ⟨0, tqMemberType⟩)
    (by exact List.Mem.tail _ (List.Mem.head _))

theorem tq_binders_indep {pre : List VIndField} {i : Nat} {r : VIndRecArg}
    (hr : r.binders = []) : r.BindersIndep pre i := by
  intro i' t F' hF' hs he k B hB
  rw [hr] at hB
  simp at hB

/-- The index argument every constructor and every recursive field of this block carries is
`Prop`, which mentions no block constant. -/
theorem tq_args_noBlock : ∀ a ∈ [(VExpr.sort .zero)], (tqAux tqAuxNodeB).NoBlock a := by decide

/-- **The one β step the redex block costs** — `ParamRedex.lean` §11's `mp_redex_pos_defeq` at the
indexed block, where the contractum carries an index argument as well as the parameter. -/
theorem tq_redex_pos_defeq {env₂ : VEnv}
    (ht : env₂.constants ``TQ = some ⟨0, tqMemberType⟩) :
    env₂.IsDefEqType (tqAux tqAuxNodeB).uvars [.sort .zero, .sort (.succ .zero)] tqRedex
      (({ binders := [], idx := 0, args := [.sort .zero] } : VIndRecArg).canonType
        (tqAux tqAuxNodeB) 1) := by
  refine ⟨.succ .zero, ?_⟩
  exact VEnv.IsDefEq.beta (A := .sort .zero) (B := .sort (.succ .zero))
    (e := .app (.app (.const ``TQ []) (.bvar 2)) (.sort .zero)) (e' := .bvar 0)
    (by type_tac) (by type_tac)

/-- **`VInductDecl'.WF` AT THE INDEXED NESTED BLOCK**, over an arbitrary environment. -/
theorem tqAuxB_WF : (tqAux tqAuxNodeB).WF env where
  types_ne := by simp [tqAux]
  params := tq_params_WF
  types := by
    intro T hT
    have hidx := tq_indexCtx_WF (env := env) T hT
    simp only [tqAux, List.mem_cons, List.not_mem_nil, or_false] at hT
    obtain rfl | rfl := hT <;>
      exact { indices := hidx, isType := ⟨_, by type_tac⟩, canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₂ hs j T hT C hC
    have ht := tq_const_staged hs
    have hf := tq_nested_const_staged hs
    match j, hT with
    | 0, hT =>
      simp only [tqAux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := ?_,
               args_len := rfl, args_fresh := tq_args_noBlock,
               args_ty := .cons (by type_tac) .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [tqObj, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, tqAux, Lean.Nat.imax]
                binders_indep := fun r hr => by cases hr; exact tq_binders_indep rfl
                pos := ⟨by decide, rfl, nofun, tq_args_noBlock, tq_params_WF, by type_tac,
                        fun T' hT' => by cases hT'; exact .cons (by type_tac) .nil,
                        ⟨_, by type_tac⟩, by decide⟩ }
      | (_ + 1), hF => simp [tqObj] at hF
    | 1, hT =>
      simp only [tqAux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := ?_,
               args_len := rfl, args_fresh := tq_args_noBlock,
               args_ty := .cons (by type_tac) .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [tqAuxNodeB, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, tqAux, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.sort .zero, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                        _, by type_tac⟩ }
      | 1, hF =>
        simp only [tqAuxNodeB, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, tqAux, Lean.Nat.imax]
                binders_indep := fun r hr => by cases hr; exact tq_binders_indep rfl
                pos := ⟨by decide, rfl, nofun, tq_args_noBlock,
                        ⟨tq_params_WF, _, by type_tac⟩, by type_tac,
                        fun T' hT' => by cases hT'; exact .cons (by type_tac) .nil,
                        tq_redex_pos_defeq ht, by decide⟩ }
      | (_ + 2), hF => simp [tqAuxNodeB] at hF
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, tqAux])

/-! ### §4a The index slots are non-empty, so §4's `HasArgs` steps are not `.nil` in disguise -/

theorem tq_ctor_args_ne_nil : tqObj.args ≠ [] ∧ tqAuxNodeB.args ≠ [] := by decide

theorem tq_recArg_args_ne_nil :
    ∀ p ∈ (tqAux tqAuxNodeB).ctorsAll, ∀ F ∈ p.2.fields, ∀ r, F.recArg = some r → r.args ≠ [] := by
  decide

/-! ## §5 `MotiveHargs`' `hpi`/`hAs`/`hsort`, exercised

`docs/handoff-faminhab.md` §4b item 1 grades `VIndRestore.MotiveHargs` (`RecTyped.lean` §3) as
*inhabited, one slot of four exercised*: at every nested witness in the tree the companion is
unindexed, so the spine `VExpr.bvars 0 T.indices.length` is `[]`, which forces `As = []`
(`hAs_nil_of_spine_nil` below), and then `hpi` and `hsort` are the two identities
`instAll B _ = B'` and `B' = .sort w`.  Only `hbody` carries content there.

At `tqAux`'s **indexed** companion the spine is `[.bvar 0]`, `As` is a one-entry telescope, and
`hAs` is a real `HasArgs.cons` whose subject is looked up in the index window that `liftTele t`
opens.  This is the first instance of the family in which all four slots do work. -/

/-- **The collapse, as a theorem rather than as a remark**: an empty spine forces the telescope
`hAs` is stated against to be empty, so `hpi` and `hsort` degenerate.  This is what makes
"one slot of four exercised" precise. -/
theorem hAs_nil_of_spine_nil {e : VEnv} {U : Nat} {Γ As : List VExpr}
    (h : e.HasArgs U Γ As []) : As = [] := by cases h; rfl

/-- The companion member, as `D.types[1]?` delivers it. -/
def tqT1 : VIndType where
  name := tqNestedName
  type := tqMemberType
  indices := [.sort (.succ .zero)]
  ctors := [tqAuxNodeB]

theorem tq_types_one : (tqAux tqAuxNodeB).types[1]? = some tqT1 := rfl

/-- **The spine is NOT empty here** — the exact negation of
`InductiveDeclExamples.fi_motive_window_empty`. -/
theorem tq_motive_window : VExpr.bvars 0 tqT1.indices.length = [.bvar 0] := rfl

theorem tq_companion_indexed : tqT1.indices ≠ [] := by decide

section
variable {e : VEnv}
variable (hMI : e.constants ``MI = some ⟨0, miType.type⟩)
variable (hTQ : e.constants ``TQ = some ⟨0, tqMemberType⟩)

include hMI hTQ in
/-- **`MotiveHargs` AT AN INDEXED COMPANION.**  `As = [Type]`, the spine is `[.bvar 0]`, and `hAs`
is `HasArgs.cons` on a `Lookup` into the index window — the slot no witness in the tree could
exercise.  `hbody` is the restored head `MI Prop (fun _ : Prop => TQ α Prop)` typed over the
parameter block, i.e. the same content `fi_motiveHargs` carries at the unindexed block. -/
theorem tq_motiveHargs (σ : CSubst) :
    tqRestore.MotiveHargs (tqAux tqAuxNodeB) σ e 1 tqT1 :=
  ⟨[.sort (.succ .zero)], .forallE (.sort (.succ .zero)) (.sort (.succ .zero)),
    .sort (.succ .zero), .succ .zero, by type_tac, rfl, .cons (by type_tac) .nil, rfl⟩

include hMI hTQ in
/-- …and in the ∀-shape the closure `VEnv.recConstsR_wf_of_recHargsD` binds, so the guard
`T.name ∈ K` is discharged at the block rather than assumed. -/
theorem tq_hmotD (σ : CSubst) : ∀ (t : Nat) (T : VIndType),
    (tqAux tqAuxNodeB).types[t]? = some T → T.name ∈ tqK →
    tqRestore.MotiveHargs (tqAux tqAuxNodeB) σ e t T := by
  rintro (_ | _ | t) T hT hK
  · cases hT; exact absurd hK (by decide)
  · cases hT; exact tq_motiveHargs hMI hTQ σ
  · simp [tqAux] at hT

end

/-- **THE SLOT CANNOT BE DODGED AT THIS BLOCK.**  Every `MotiveHargs` witness at the indexed
companion has a **one-entry** `As`, since `hAs`'s spine has one entry; at an unindexed companion the
same inversion gives `As = []`, which is exactly why `hpi`/`hAs`/`hsort` were identities at every
earlier witness.  So §5 is not one lucky choice of `As` — no other length is available. -/
theorem tq_motiveHargs_As_len {e : VEnv} {σ : CSubst}
    (h : tqRestore.MotiveHargs (tqAux tqAuxNodeB) σ e 1 tqT1) :
    ∃ (As : List VExpr) (B B' : VExpr) (w : VLevel),
      e.HasType (tqAux tqAuxNodeB).recUvars
          (((tqAux tqAuxNodeB).atRecTele (tqAux tqAuxNodeB).params).reverse)
          ((tqAux tqAuxNodeB).atRec (tqRestore.tyBody (tqAux tqAuxNodeB) 1)) B ∧
        VExpr.instAll B (VExpr.bvars (tqT1.indices.length + 1) (tqAux tqAuxNodeB).np)
          = VExpr.mkPi As B' ∧
        VExpr.instAll B' (VExpr.bvars 0 tqT1.indices.length) = .sort w ∧
        As.length = 1 := by
  obtain ⟨As, B, B', w, hbody, hpi, hAs, hsort⟩ := h
  exact ⟨As, B, B', w, hbody, hpi, hsort, by simpa [tq_motive_window] using hAs.length_eq⟩

/-! ### §5a What §5 does NOT claim

* `hpi` is `rfl` and `hsort` is `rfl` at this witness, as they are at `ntreeAux` — the difference
  is that here they are `rfl` **at a one-entry `As`** rather than at the forced `As = []`; the
  index type is the closed `Type`, so nothing in `As` depends on the parameter.  The remaining
  coordinate — a companion index telescope that is block-free but **depends on the outer block's
  parameters** — is admitted by Lean (F2 row 2 of `docs/handoff-indexedwit.md`: `V2 (α β : Type) :
  List α → Type` nested as `V2 γ (T5 γ)`) and has **no witness in the tree**, mine included.
* `MotiveHargs` is data, not a theorem: §5 inhabits it, it does not produce it.  The general
  producer is still absent (`docs/handoff-faminhab.md` §8 item 2).
* Only `MotiveHargs` is exercised here.  The corresponding `IotaHargs` index slots are not.
-/

end
end TQWit
end MRedex

/-! ## §6 The remaining coordinate: a companion index telescope that depends on the PARAMETERS

§5's index type is the closed `Type`, so nothing in `As` mentions the block's parameters, and §5a
lists that as the one coordinate still unexercised.  F2 row 2 of `docs/handoff-indexedwit.md` says
Lean **accepts** that shape, so it is not a hypothetical: this section builds it.

`WJ (α β : Type) : (α → Type) → Type` is the smallest container with a parameter-dependent index
type that is *reachable* — the index type `α → Type` has the closed inhabitant `fun _ : α => Prop`,
whereas §2's `WI : (α : Type) → α → Type` has none, which is why the kernel's other rejection rule
(`is_nested_inductive_app`, no locals in the nested parameters) bites there.  Nesting through it at
`α := γ` (the block's own **parameter**) and `β := T5 γ` (the block's own **member**) gives a
companion `_nested.WJ_1 (γ : Type) : (γ → Type) → Type` whose index telescope is `[γ → Type]`:
block-free, so `D.WF` survives, and parameter-dependent, so `MotiveHargs`' `As` moves with the
parameter.

Both declarations below are real, and Lean's own kernel accepts them (that is what the
`vconst(type_of% ·)` anchors check).  Unlike `TQWit`'s block this one is **canonical** — the field
is stored at `r.canonType` on the nose, so §6's `VIndField.WF.pos` needs no β step. -/

namespace IndexedWit

/-- The container.  Its index's type mentions its first parameter. -/
inductive WJ (α : Type) (β : Type) : (α → Type) → Type where
  | mk : WJ α β (fun _ => Prop)

/-- The user's block, nesting through `WJ` at its own parameter and its own member. -/
inductive T5 (γ : Type) : Type where
  | node : WJ γ (T5 γ) (fun _ => Prop) → T5 γ

def wjMk : VIndCtor where
  name := ``WJ.mk
  params := [.sort (.succ .zero), .sort (.succ .zero)]
  fields := []
  args := [.lam (.bvar 1) (.sort .zero)]

def wjType : VIndType where
  name := ``WJ
  type := .forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero))
    (.forallE (.forallE (.bvar 1) (.sort (.succ .zero))) (.sort (.succ .zero))))
  indices := [.forallE (.bvar 1) (.sort (.succ .zero))]
  ctors := [wjMk]

def wjDecl : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero), .sort (.succ .zero)]
  lvl := .succ .zero
  isLE := true
  types := [wjType]

/-- **The container's index type really does depend on its parameter.** -/
theorem wj_index_param_dependent :
    wjType.indices = [.forallE (.bvar 1) (.sort (.succ .zero))] := rfl

example : wjType.type = (vconst(type_of% @WJ)).type := rfl
example : wjMk.type wjDecl 0 = (vconst(type_of% @WJ.mk)).type := rfl

def t5NestedName : Name := `_nested.WJ_1

def wjOcc : VNestedOcc where
  decl := wjDecl
  idx := 0
  lvls := []
  args := [.bvar 0, .app (.const ``T5 []) (.bvar 0)]
  auxName := t5NestedName
  ctorName n := if n = ``WJ.mk then `_nested.WJ_1.mk else n

def t5Restore : VIndRestore where
  tyName j := if j = 1 then ``WJ else ``T5
  tyLvls _ := []
  tyArgs j := if j = 1 then [.bvar 0, .app (.const ``T5 []) (.bvar 0)] else [.bvar 0]
  ctorName n := if n = `_nested.WJ_1.mk then ``WJ.mk else n
  recName n := if n = `_nested.WJ_1.rec then `T5.rec_1 else n

def t5K : List Name := [t5NestedName]

/-- The user's constructor, after `replaceIfNested`: the nested occurrence is the companion, and
its index argument `fun _ : γ => Prop` is block-free. -/
def t5Node : VIndCtor where
  name := ``T5.node
  params := [.sort (.succ .zero)]
  fields :=
    [{ type := .app (.app (.const t5NestedName []) (.bvar 0)) (.lam (.bvar 0) (.sort .zero)),
       lvl := .succ .zero,
       recArg := some { binders := [], idx := 1, args := [.lam (.bvar 0) (.sort .zero)] } }]
  args := []

/-- The companion's constructor, as `VNestedOcc.ctor` computes it (`t5_ctor_built`). -/
def t5AuxMk : VIndCtor where
  name := `_nested.WJ_1.mk
  params := [.sort (.succ .zero)]
  fields := []
  args := [.lam (.bvar 0) (.sort .zero)]

def t5Aux : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero)]
  lvl := .succ .zero
  isLE := true
  types :=
    [{ name := ``T5, type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero)),
       indices := [], ctors := [t5Node] },
     { name := t5NestedName,
       type := .forallE (.sort (.succ .zero))
         (.forallE (.forallE (.bvar 0) (.sort (.succ .zero))) (.sort (.succ .zero))),
       indices := [.forallE (.bvar 0) (.sort (.succ .zero))],
       ctors := [t5AuxMk] }]

/-! ### §6.1 The transcription, anchored against Lean and against the construction -/

example : ((t5Aux).types.getD 0 default).type = (vconst(type_of% @T5)).type := rfl

theorem t5_node_declared :
    (t5Node.typeR t5Aux t5Restore 0).substC (t5Restore.csubstTy t5Aux t5K)
      = (vconst(type_of% @T5.node)).type := rfl

theorem t5_member_built : t5Aux.types[1]? = some (wjOcc.member t5Aux.header t5Restore) := rfl

theorem t5_ctor_built : wjOcc.ctor t5Aux.header t5Restore wjMk = t5AuxMk := rfl

/-- **THE COORDINATE**: the companion's index telescope mentions the block's parameter — and no
block constant, which is why (unlike §2) `WF` survives. -/
theorem t5_companion_indices :
    (wjOcc.member t5Aux.header t5Restore).indices
      = [.forallE (.bvar 0) (.sort (.succ .zero))] := rfl

theorem t5_companion_indices_noBlock :
    ∀ A ∈ (wjOcc.member t5Aux.header t5Restore).indices, t5Aux.NoBlock A := by decide

theorem t5_companion_indices_ne_nil :
    (wjOcc.member t5Aux.header t5Restore).indices ≠ [] := by decide

/-- …and it is **not** closed, which is what separates §6 from §5. -/
theorem t5_index_not_closed :
    ¬ VExpr.ClosedTele (wjOcc.member t5Aux.header t5Restore).indices 0 := by
  rw [t5_companion_indices]
  simp [VExpr.ClosedTele, VExpr.ClosedN]

theorem t5_np_one : t5Aux.np = 1 := rfl

/-- The block is **canonical** — the recursive field is stored at `r.canonType` on the nose — so
unlike `TQWit`'s redex block §6.2's `VIndField.WF.pos` needs no β step. -/
theorem t5_node_canonical : t5Node.Canonical t5Aux := by
  intro i F r hF hr
  match i, hF with
  | 0, hF =>
    simp only [t5Node, List.getElem?_cons_zero, Option.some.injEq] at hF
    subst hF; cases hr; rfl
  | (_ + 1), hF => simp [t5Node] at hF

theorem t5_ctorsAll : t5Aux.ctorsAll = [(0, t5Node), (1, t5AuxMk)] := rfl

/-! ### §6.2 `VInductDecl'.WF` at the parameter-dependent indexed nested block -/

section
variable {env : VEnv}

theorem t5_params_WF : OnCtx t5Aux.params.reverse (env.IsType t5Aux.uvars) :=
  ⟨trivial, _, .sort (by decide)⟩

/-- **The clause §5's closed index type cannot exercise**: the index telescope's well-formedness
needs the parameter in context, because the index type mentions it. -/
theorem t5_indexCtx_WF (T : VIndType) (hT : T ∈ t5Aux.types) :
    OnCtx (T.indices.reverse ++ t5Aux.params.reverse) (env.IsType t5Aux.uvars) := by
  simp only [t5Aux, List.mem_cons, List.not_mem_nil, or_false] at hT
  obtain rfl | rfl := hT
  · exact ⟨trivial, _, .sort (by decide)⟩
  · exact ⟨⟨trivial, _, .sort (by decide)⟩, _, by type_tac⟩

theorem t5_const_staged {env₂ : VEnv} (hs : env.addIndTypes t5Aux = some env₂) :
    env₂.constants ``T5 = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩ :=
  VEnv.addConstList_constants hs
    (``T5, ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩) (by exact List.Mem.head _)

theorem t5_nested_const_staged {env₂ : VEnv} (hs : env.addIndTypes t5Aux = some env₂) :
    env₂.constants t5NestedName = some ⟨0, .forallE (.sort (.succ .zero))
      (.forallE (.forallE (.bvar 0) (.sort (.succ .zero))) (.sort (.succ .zero)))⟩ :=
  VEnv.addConstList_constants hs (t5NestedName, _) (by exact List.Mem.tail _ (List.Mem.head _))

theorem t5_index_arg_noBlock :
    ∀ a ∈ [(VExpr.lam (.bvar 0) (.sort .zero))], t5Aux.NoBlock a := by decide

/-- **`VInductDecl'.WF` AT THE PARAMETER-DEPENDENT INDEXED NESTED BLOCK**, over an arbitrary
environment.  Every `HasArgs` against an index telescope here has a **parameter-dependent** entry,
which is the first such instance anywhere in the tree. -/
theorem t5Aux_WF : t5Aux.WF env where
  types_ne := by simp [t5Aux]
  params := t5_params_WF
  types := by
    intro T hT
    have hidx := t5_indexCtx_WF (env := env) T hT
    simp only [t5Aux, List.mem_cons, List.not_mem_nil, or_false] at hT
    obtain rfl | rfl := hT <;>
      exact { indices := hidx, isType := ⟨_, by type_tac⟩, canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₂ hs j T hT C hC
    have ht := t5_const_staged hs
    have hf := t5_nested_const_staged hs
    match j, hT with
    | 0, hT =>
      simp only [t5Aux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := ?_,
               args_len := rfl, args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [t5Node, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, t5Aux, Lean.Nat.imax]
                binders_indep := fun r hr => by
                  cases hr; intro _ _ _ _ _ _ k B hB; simp at hB
                pos := ⟨by decide, rfl, nofun, t5_index_arg_noBlock, t5_params_WF, by type_tac,
                        fun T' hT' => by cases hT'; exact .cons (by type_tac) .nil,
                        ⟨_, by type_tac⟩, by decide⟩ }
      | (_ + 1), hF => simp [t5Node] at hF
    | 1, hT =>
      simp only [t5Aux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      exact { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := nofun,
              args_len := rfl, args_fresh := t5_index_arg_noBlock,
              args_ty := .cons (by type_tac) .nil, result := by type_tac }
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, t5Aux])

end

/-! ### §6.3 `MotiveHargs` with a parameter-dependent `As` -/

def t5T1 : VIndType where
  name := t5NestedName
  type := .forallE (.sort (.succ .zero))
    (.forallE (.forallE (.bvar 0) (.sort (.succ .zero))) (.sort (.succ .zero)))
  indices := [.forallE (.bvar 0) (.sort (.succ .zero))]
  ctors := [t5AuxMk]

theorem t5_types_one : t5Aux.types[1]? = some t5T1 := rfl

section
variable {e : VEnv}
variable (hWJ : e.constants ``WJ = some ⟨0, wjType.type⟩)
variable (hT5 : e.constants ``T5
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)

include hWJ hT5 in
/-- **`MotiveHargs` AT A PARAMETER-DEPENDENT INDEXED COMPANION.**  `As = [#2 → Type]` — it mentions
the parameter, so neither `hpi` nor `hAs` is a statement about closed data, and `hAs`' subject is
found by a `Lookup` whose type only matches *after* the `liftTele` that opens the index window.
This is the coordinate `docs/handoff-faminhab.md` §4b/§5.5 and §5a above both leave open. -/
theorem t5_motiveHargs (σ : CSubst) : t5Restore.MotiveHargs t5Aux σ e 1 t5T1 :=
  ⟨[.forallE (.bvar 2) (.sort (.succ .zero))],
    .forallE (.forallE (.bvar 0) (.sort (.succ .zero))) (.sort (.succ .zero)),
    .sort (.succ .zero), .succ .zero, by type_tac, rfl, .cons (by type_tac) .nil, rfl⟩

include hWJ hT5 in
theorem t5_hmotD (σ : CSubst) : ∀ (t : Nat) (T : VIndType),
    t5Aux.types[t]? = some T → T.name ∈ t5K → t5Restore.MotiveHargs t5Aux σ e t T := by
  rintro (_ | _ | t) T hT hK
  · cases hT; exact absurd hK (by decide)
  · cases hT; exact t5_motiveHargs hWJ hT5 σ
  · simp [t5Aux] at hT

end

/-- **The `As` §6.3 supplies is parameter-dependent**, so §5a's remaining coordinate is exercised:
the entry is not closed at the parameter depth the spine points into. -/
theorem t5_As_not_closed :
    ¬ VExpr.ClosedTele [(VExpr.forallE (.bvar 2) (.sort (.succ .zero)))] 0 := by
  simp [VExpr.ClosedTele, VExpr.ClosedN]

end IndexedWit

end Lean4Lean

#print axioms Lean4Lean.ctxConstsIn_of_index
#print axioms Lean4Lean.VInductDecl'.not_WF_of_index_undeclared
#print axioms Lean4Lean.VInductDecl'.not_WF_of_type_undeclared
#print axioms Lean4Lean.IndexedWit.wi_member_built
#print axioms Lean4Lean.IndexedWit.wi_not_WF_indices
#print axioms Lean4Lean.IndexedWit.wi_not_WF_isType
#print axioms Lean4Lean.IndexedWit.wi_not_WF_empty
#print axioms Lean4Lean.IndexedWit.wi_fresh_of_step
#print axioms Lean4Lean.IndexedWit.wi_not_WF_of_step
#print axioms Lean4Lean.IndexedWit.wi_not_WF_wiEnv
#print axioms Lean4Lean.VNestedOcc.not_WF_of_member_index_undeclared
#print axioms Lean4Lean.MRedex.TQWit.tq_redex_pos_defeq
#print axioms Lean4Lean.MRedex.TQWit.tq_indexCtx_WF
#print axioms Lean4Lean.MRedex.TQWit.tqAuxB_WF
#print axioms Lean4Lean.MRedex.TQWit.tq_recArg_args_ne_nil
#print axioms Lean4Lean.MRedex.TQWit.hAs_nil_of_spine_nil
#print axioms Lean4Lean.MRedex.TQWit.tq_motive_window
#print axioms Lean4Lean.MRedex.TQWit.tq_motiveHargs
#print axioms Lean4Lean.MRedex.TQWit.tq_motiveHargs_As_len
#print axioms Lean4Lean.MRedex.TQWit.tq_hmotD
#print axioms Lean4Lean.IndexedWit.t5_node_declared
#print axioms Lean4Lean.IndexedWit.t5_member_built
#print axioms Lean4Lean.IndexedWit.t5_ctor_built
#print axioms Lean4Lean.IndexedWit.t5_companion_indices
#print axioms Lean4Lean.IndexedWit.t5_index_not_closed
#print axioms Lean4Lean.IndexedWit.t5_node_canonical
#print axioms Lean4Lean.IndexedWit.t5_indexCtx_WF
#print axioms Lean4Lean.IndexedWit.t5Aux_WF
#print axioms Lean4Lean.IndexedWit.t5_motiveHargs
#print axioms Lean4Lean.IndexedWit.t5_hmotD
#print axioms Lean4Lean.IndexedWit.t5_As_not_closed
