import Lean4Lean.Theory.Inductive.NestedTele
-- 2026-09-03: for `MRedex.TQWit.tqAux`, the only *indexed* parameterised nested block in the
-- tree.  §6 needs it because every other witness has `T.indices = []`, which makes §2's
-- instantiation window empty and its content untested.
import Lean4Lean.Theory.Inductive.IndexedNested

/-!
# `IotaHargs` in general: the pieces that are not data

`VIndRestore.IotaHargs` (`Theory/Inductive/NestedTele.lean` §T16.11a) is the only remaining input
to `VEnv.iotaRulesRS_wf_of_hargsD` — i.e. to obligation **(C)** of `VEnv.addInductR_ordered'` at
a *parameterful* nested block, after `Verify/Inductive/FlipPriceCompose.lean` discharged every
name-discipline hypothesis from the reserved-prefix barrier.  It unfolds to

    htele ∧ ∃ A₀ v, hfunM ∧ hconv ∧ hmaj

and §T16.10 of `NestedTele.lean` prices the three residual items: `hargs` twice (the type head
and the constructor head), `htele`, and **`hfunM`**, of which it says

> §T8 shows it is `hmot` + `hidx`, not data; what §T16 does not do is the domain identification
> (`tyApp'_instAll'`, the step `recApp_partial_hasType` performs internally), so `hfunM` is
> **stated, not derived**.

This file derives it.  §1 supplies the missing commutation (`substC` through `instAll`), §2 the
substituted domain identification, §3 `hfunM` from `hidx` alone — `hmot` turns out to be
derivable too, off `lookup_motive_substC` at the ι-context — and §4 assembles `IotaHargs`.

**Nothing here is a discharge of (C).**  §4's hypotheses still contain the two `hargs` bundles
and `htele`; what changes is that `hfunM` is no longer among them.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars liftTele instAll)

/-! ## §1 `substC` commutes with `instAll`

`VExpr.substC_liftN` and `VExpr.substC_inst` (`Theory/Typing/ConstSubst.lean`) are in the tree;
the iterated form is not, and it is what pushes a `substC` past a saturated instantiation. -/

namespace VExpr

/-- **`substC` through `instAll`.**  The `Closed` hypothesis is `substC_inst`'s: without it the
values could capture the instantiated variables. -/
theorem substC_instAll {σ : CSubst} (hσ : σ.Closed) :
    ∀ {as : List VExpr} {e : VExpr} {k : Nat},
      (instAll e as k).substC σ = instAll (e.substC σ) (as.map (substC · σ)) k
  | [], _, _ => rfl
  | a :: as, e, k => by
    rw [instAll_cons, substC_instAll hσ, substC_inst hσ, List.map_cons, instAll_cons,
      List.length_map]

end VExpr

/-! ## §2 The substituted domain identification

`VInductDecl'.tyApp'_instAll` (`Theory/Inductive/Lemmas.lean`) is the unsubstituted computation:
the motive's stored domain `I_j p ι`, lifted over the recursor telescope and applied to index
*arguments* `ιs`, is `I_j` at the shifted parameter block with spine `ιs`.  §T16.10's
`tyApp'_instAll'` is that statement one `substC` out; with §1 it is three rewrites. -/

namespace VInductDecl'

/-- **§T16.10's `tyApp'_instAll'`.**  The substituted motive's domain, applied to the substituted
index spine, is the substituted `tyApp'` at the shifted parameter block.  No environment, no `np`
bound, and `σ.Closed` is the only hypothesis beyond the two arithmetic ones. -/
theorem tyApp'_substC_instAll {D : VInductDecl'} {σ : CSubst} (hσ : σ.Closed)
    {j ni K M : Nat} {as : List VExpr} (hlen : as.length = ni)
    (h : K + 1 + (ni + j) - ni = M) :
    instAll (((D.tyApp' j (ni + j) (bvars 0 ni)).substC σ).liftN (K + 1) ni)
        (as.map (VExpr.substC · σ)) 0
      = (D.tyApp' j M as).substC σ := by
  rw [← VExpr.substC_liftN hσ, ← VExpr.substC_instAll hσ,
    VInductDecl'.tyApp'_instAll (D := D) hlen h]

end VInductDecl'

/-! ## §3 `hfunM`, derived

`substC_motiveApp_partial` (§T8) is `hfunM` up to the domain identification; §2 supplies that.
What remains of §T16.10's "`hmot` + `hidx`" is `hidx` alone: `hmot` at the ι-rule context is
`lookup_motive_substC` at `Δ := fields ++ minors`, `Γ₀ := params`, an equation between lengths. -/

namespace VInductDecl'

/-- **`hmot` at the ι-rule context, derived.**  `lookup_motive_substC` needs the context split as
`Δ ++ (motives.map …).reverse ++ Γ₀`; `iotaCtx`'s reverse is exactly that with `Δ` the field and
minor blocks (length `C.fields.length + D.nmin`) and `Γ₀` the parameter block. -/
theorem lookup_motive_iotaCtx_substC {D : VInductDecl'} {σ : CSubst} {C : VIndCtor} {j : Nat}
    (hj : j < D.nm) :
    Lookup (((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
      (C.fields.length + D.nmin + (D.nm - 1 - j))
      (((D.motiveType j).substC σ).liftN (C.fields.length + D.nmin + (D.nm - 1 - j) + 1)) := by
  have hsplit : ((D.iotaCtx C).map (VExpr.substC · σ)).reverse
      = ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type)))).map
            (VExpr.substC · σ)).reverse ++ (D.minors.map (VExpr.substC · σ)).reverse
          ++ ((D.motives.map (VExpr.substC · σ)).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse) := by
    simp [VInductDecl'.iotaCtx, List.map_append, List.reverse_append, List.append_assoc]
  have hlen : (((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type)))).map
        (VExpr.substC · σ)).reverse ++ (D.minors.map (VExpr.substC · σ)).reverse).length
      = C.fields.length + D.nmin := by simp
  rw [hsplit, ← List.append_assoc, ← hlen]
  exact VInductDecl'.lookup_motive_substC hj _ _

end VInductDecl'

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {σ : CSubst} {e : VEnv}
variable {j : Nat} {T : VIndType} {C : VIndCtor}

/-- **`IotaHargs`' `hfunM`, derived from `hidx` alone.**

`hidx` is the substituted D-series datum (`VIndCtor.WF.args_ty` moved across `σ` by §T1's
`HasArgs.substC`); everything else — the motive lookup and the domain identification §T16.10
flagged — is discharged here.  No environment hypothesis, no `np` bound. -/
theorem iotaHargs_hfunM (hσ : σ.Closed) (hT : D.types[j]? = some T) (hj : j < D.nm)
    (hlen : C.args.length = T.indices.length)
    (hidx : e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
      (liftTele (C.fields.length + D.nmin + (D.nm - 1 - j) + 1)
        ((liftTele j (D.atRecTele T.indices) 0).map (VExpr.substC · σ)) 0)
      ((C.args.map fun a =>
        (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ))) :
    e.HasType D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
      ((VExpr.bvar (C.fields.length + D.nmin + (D.nm - 1 - j))).mkApp
        ((C.args.map fun a =>
          (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ)))
      (.forallE ((D.tyApp' j (D.nm + D.nmin + C.fields.length)
        (C.args.map fun a =>
          (D.atRec a).liftN (D.nm + D.nmin) C.fields.length)).substC σ)
        (.sort D.elimLvl)) := by
  have h := VIndRestore.substC_motiveApp_partial (D := D) (σ := σ) (e := e)
    (U := D.recUvars) (t := j) (T := T)
    (k := C.fields.length + D.nmin + (D.nm - 1 - j)) hT
    (VInductDecl'.lookup_motive_iotaCtx_substC hj) hidx
  rwa [VInductDecl'.tyApp'_substC_instAll (D := D) hσ
    (M := D.nm + D.nmin + C.fields.length)
    (as := C.args.map fun a => (D.atRec a).liftN (D.nm + D.nmin) C.fields.length)
    (by simpa using hlen) (by omega)] at h

end
end VIndRestore

/-! ## §4 `IotaHargs`, assembled

`IotaHargs` is `htele ∧ ∃ A₀ v, hfunM ∧ hconv ∧ hmaj`.  §3 removes `hfunM`; the two conversions
are §8.9's two head defeqs (`substC_tyApp'_defeq_tyAppR'_comp` and
`substC_ctorApp'_defeq_ctorAppR_comp`, neither with an `np` bound) at the ι-rule's own context,
with `A₀ := D.tyAppR' …` — the *contracted* type head, which is what makes `hconv` the type head
defeq read backwards.

What is left, and it is the honest list: `htele` (§T15.4's `iotaCtx_teleDefEq`, i.e. `hmot`
+ `hmin` + `hfld`), the two `hargs` bundles (`hbody`/`hAs` per head, plus the telescope typing
`hOnp`/`hbv` and the shape facts `hpi`/`hsort`), the `hidx` of §3, and `hres` — the constructor's
result identification, `instAt_ctor_hpi`'s `B'` read at the ι-rule's numbering. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {e : VEnv}
variable {j : Nat} {T : VIndType} {C : VIndCtor}

/-- **`R.IotaHargs D σ e j C` in general**, from `htele`, the two head `hargs` bundles, `hidx`
and `hres`.  `hfunM` is *not* a hypothesis: §3 derives it.

This is not a discharge of obligation (C): `htele` and the two bundles are exactly §T16.10's
residual, and `hres` is its σ-free identification at the ι-rule's numbering.  It is the statement
that nothing *else* is needed — in particular no `hσ`, no `Ordered`-after-substitution, and no
bound on `D.np`. -/
theorem iotaHargs_of_heads
    (hat : R.SubstAt D K σ) (hfr : R.SubstFree D σ) (hσ : σ.Closed)
    (hcl : ∀ a ∈ R.tyArgs j, a.ClosedN D.np) (henv : e.Ordered)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) (hC : C ∈ T.ctors) (hj : j < D.nm)
    (hlen : C.args.length = T.indices.length)
    {AsT AsC : List VExpr} {BT BT' BC BC' : VExpr} {v : VLevel}
    (htele : e.TeleDefEq D.recUvars [] ((D.iotaCtx C).map (VExpr.substC · σ))
      ((D.iotaCtxR R C).map (VExpr.substC · σ)))
    (hidx : e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
      (liftTele (C.fields.length + D.nmin + (D.nm - 1 - j) + 1)
        ((liftTele j (D.atRecTele T.indices) 0).map (VExpr.substC · σ)) 0)
      ((C.args.map fun a =>
        (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ)))
    (hOnp : OnCtx ((D.atRecTele D.params).reverse
      ++ ((D.iotaCtx C).map (VExpr.substC · σ)).reverse) (e.IsType D.recUvars))
    (hbvT : e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
      (D.atRecTele D.params) (bvars (D.nm + D.nmin + C.fields.length) D.np))
    (hbodyT : e.HasType D.recUvars ((D.atRecTele D.params).reverse
      ++ ((D.iotaCtx C).map (VExpr.substC · σ)).reverse) (D.atRec (R.tyBody D j)) BT)
    (hpiT : instAll BT (bvars (D.nm + D.nmin + C.fields.length) D.np) = mkPi AsT BT')
    (hAsT : e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse) AsT
      ((C.args.map fun a =>
        (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ)))
    (hsortT : instAll BT' ((C.args.map fun a =>
        (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ)) = .sort v)
    (hbvC : e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
      (D.atRecTele D.params) (bvars (C.fields.length + (D.nm + D.nmin)) D.np))
    (hbodyC : e.HasType D.recUvars ((D.atRecTele D.params).reverse
      ++ ((D.iotaCtx C).map (VExpr.substC · σ)).reverse) (D.atRec (R.ctorBody D j C)) BC)
    (hpiC : instAll BC (bvars (C.fields.length + (D.nm + D.nmin)) D.np) = mkPi AsC BC')
    (hAsC : e.HasArgs D.recUvars (((D.iotaCtx C).map (VExpr.substC · σ)).reverse) AsC
      (bvars 0 C.fields.length))
    (hres : instAll BC' (bvars 0 C.fields.length)
      = D.tyAppR' R j (D.nm + D.nmin + C.fields.length)
          ((C.args.map fun a =>
            (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ))) :
    R.IotaHargs D σ e j C := by
  refine ⟨htele, D.tyAppR' R j (D.nm + D.nmin + C.fields.length)
      ((C.args.map fun a =>
        (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ)),
    v, iotaHargs_hfunM hσ hT hj hlen hidx, ?_, ?_⟩
  · have hhead := substC_tyApp'_defeq_tyAppR'_comp (R := R) (D := D) (K := K) (σ := σ)
      (U := D.recUvars) (j := j) (T := T) hat hcl henv hT hK
      (k := D.nm + D.nmin + C.fields.length)
      (args := C.args.map fun a => (D.atRec a).liftN (D.nm + D.nmin) C.fields.length)
      hOnp hbvT hbodyT hpiT hAsT
    rw [hsortT] at hhead
    exact hhead.symm
  · have hmaj := substC_ctorApp'_defeq_ctorAppR_comp (R := R) (D := D) (K := K) (σ := σ)
      (U := D.recUvars) (j := j) (T := T) (C := C) hat hcl henv hT hK hC
      (k := C.fields.length + (D.nm + D.nmin)) (args := bvars 0 C.fields.length)
      hOnp hbvC hbodyC hpiC (by rwa [VExpr.map_substC_bvars])
    rw [← substC_ctorAppR (R := R) (D := D) (σ := σ) hfr hT hC,
      VExpr.map_substC_bvars, hres] at hmaj
    exact hmaj

end
end VIndRestore

/-! ## §5 Anti-vacuity: §3 at the canonical parameterised nested block

A clean axiom line is not evidence of content (`docs/vacuity-ledger.md` §0), so §3 is checked by
*joint* inhabitation: every hypothesis of `iotaHargs_hfunM` holding at once at a real block, with
the conclusion the one the hand proof needed.  The check below replaces the `.bvar` step of
`InductiveDeclExamples.rIotaRest_nil` / `_cons` / `_node` (§T16.15 of `NestedTele.lean`) by the
general derivation, leaving those files' `hconv`/`hmaj` untouched — so if §3's conclusion were the
wrong shape, `rIotaRest_*_gen` below would not typecheck.

**The degeneracy, stated separately.**  Every type of `ntreeAux` — and of `MRedex.MPWit.mpAux`,
and of `MRedex.MRWit.mrAux` — has an **empty index telescope** (measured: `T.indices = []` for
both members, and `C.args = []` at all three constructors).  So at these witnesses `hidx` is
`HasArgs.nil` and the `instAll` window of §2 is *empty*: the inhabitation below bounds §3 from
below only in the `ni = 0` direction.  §6 measures §2's `ni > 0` content separately, at the one
indexed parameterised nested block in the tree. -/

namespace InductiveDeclExamples

theorem ntree_types_unindexed : ∀ T ∈ ntreeAux.types, T.indices = [] := by decide

theorem ntree_ctorsAll_args_nil : ∀ p ∈ ntreeAux.ctorsAll, p.2.args = [] := by decide

/-- **`hfunM` at `ntreeAux`, from §3 and nothing block-specific.**  The only inputs are
`ntree_csubst_closed`, the two `decide`s above and `HasArgs.nil`. -/
theorem ntree_hfunM {F : VEnv} {j : Nat} {C : VIndCtor} (hj : j < ntreeAux.nm)
    (hmem : (j, C) ∈ ntreeAux.ctorsAll) :
    F.HasType ntreeAux.recUvars
        (((ntreeAux.iotaCtx C).map
          (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK))).reverse)
        ((VExpr.bvar (C.fields.length + ntreeAux.nmin + (ntreeAux.nm - 1 - j))).mkApp
          ((C.args.map fun a =>
            (ntreeAux.atRec a).liftN (ntreeAux.nm + ntreeAux.nmin) C.fields.length).map
              (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK))))
        (.forallE ((ntreeAux.tyApp' j (ntreeAux.nm + ntreeAux.nmin + C.fields.length)
          (C.args.map fun a =>
            (ntreeAux.atRec a).liftN (ntreeAux.nm + ntreeAux.nmin) C.fields.length)).substC
            (ntreeRestore.csubst ntreeAux ntreeK))
          (.sort ntreeAux.elimLvl)) := by
  obtain ⟨T, hT, _⟩ := VInductDecl'.mem_ctorsAll hmem
  have hidx0 : T.indices = [] := ntree_types_unindexed T (List.mem_of_getElem? hT)
  have hargs0 : C.args = [] := ntree_ctorsAll_args_nil (j, C) hmem
  refine VIndRestore.iotaHargs_hfunM ntree_csubst_closed hT hj (by rw [hidx0, hargs0]) ?_
  rw [hidx0, hargs0]
  exact .nil

section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
variable (hnil : F.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
variable (hcons : F.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)
variable (hnode : F.constants ``NTree.node
  = some ⟨1, (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
      (ntreeRestore.csubstTy ntreeAux ntreeK)⟩)

include hL hN hnil in
/-- `rIotaRest_nil` with its `hfunM` component supplied by §3. -/
theorem rIotaRest_nil_gen : rIotaRest F 1 nlistNil :=
  ⟨.app rLt (.app rNt (.bvar 5)), .succ (.param 1),
    ntree_hfunM (by decide) (by rw [ntreeAux_ctorsAll_eq]; simp),
    (rbetaL hL hN (k := 5) (.succ (.succ (.succ (.succ (.succ .zero)))))).symm,
    rbetaNil hN hnil (k := 5) (.succ (.succ (.succ (.succ (.succ .zero)))))⟩

include hL hN hcons in
/-- `rIotaRest_cons` with its `hfunM` component supplied by §3. -/
theorem rIotaRest_cons_gen : rIotaRest F 1 nlistCons :=
  ⟨.app rLt (.app rNt (.bvar 7)), .succ (.param 1),
    ntree_hfunM (by decide) (by rw [ntreeAux_ctorsAll_eq]; simp),
    (rbetaL hL hN (k := 7)
      (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))).symm,
    .appDF (.appDF (rbetaCons hN hcons (k := 7)
        (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))) (.bvar (.succ .zero)))
      (.defeqDF (rbetaL hL hN (k := 7)
        (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))  (.bvar .zero))⟩

include hL hN hnode in
/-- `rIotaRest_node` with its `hfunM` component supplied by §3. -/
theorem rIotaRest_node_gen : rIotaRest F 0 ntreeNode :=
  ⟨.app rNt (.bvar 7), .succ (.param 1),
    ntree_hfunM (by decide) (by rw [ntreeAux_ctorsAll_eq]; simp),
    .appDF (rNC hN) (.bvar (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))),
    .appDF (.appDF (.appDF (rNodeC hnode)
        (.bvar (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))) (.bvar (.succ .zero)))
      (.defeqDF (rbetaL hL hN (k := 7)
        (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))  (.bvar .zero))⟩

end

end InductiveDeclExamples

/-! ## §6 …and §2's `ni > 0` content, at the one indexed parameterised nested block

§5's inhabitation runs at `ni = 0`, where §2's `instAll` window is empty.  `MRedex.TQWit.tqAux
tqAuxNodeB` (`Theory/Inductive/IndexedNested.lean`) is the block that fixes that: `np = 1`,
`ni = 1` at both members, `tqObj.args = [Prop]`.  `tq_cone_unindexed` in that file already records
that `MRWit.mrAux`, `MPWit.mpAux` and `ntreeAux` are all unindexed, so this is the only place the
window is non-empty.

Three measurements, all `decide` on closed `VExpr`s, and none of them an instance of §2 — they are
the independent check that §2 is doing what it claims at a real point:

* `tq_tyApp'_substC_fires` — the substitution really fires at the companion member, so §2 is not
  `VInductDecl'.tyApp'_instAll` in disguise;
* `tq_tyApp'_window_moves` — the lifted, substituted domain is **not** already the answer, so the
  `instAll` step is not an identity;
* `tq_tyApp'_substC_instAll_decide` — the equation itself, at `j = 1`, `ni = 1`, `K = 3`,
  `as = [Prop]`, confirmed by kernel computation rather than by §2.

`tq_tyApp'_substC_instAll_gen` then derives the same equation *through* §2, which is what says §2's
hypothesis set (`σ.Closed` plus the two arithmetic side conditions) is inhabited at `ni > 0`. -/

namespace MRedex.TQWit

open VExpr (bvars instAll)

/-- `hcl` at the indexed block. -/
theorem tq_tyArgs_closedNp :
    ∀ j, ∀ a ∈ tqRestore.tyArgs j, a.ClosedN (tqAux tqAuxNodeB).np := by
  intro j a ha
  by_cases h : j = 1
  · rw [show tqRestore.tyArgs j
        = [.sort .zero,
           .lam (.sort .zero) (.app (.app (.const ``TQ []) (.bvar 1)) (.sort .zero))] from
      by simp [tqRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · trivial
    · exact ⟨trivial, ⟨trivial, Nat.lt_succ_self 1⟩, trivial⟩
  · rw [show tqRestore.tyArgs j = [.bvar 0] from by simp [tqRestore, h]] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; exact Nat.zero_lt_one

/-- …so §2's only non-arithmetic hypothesis holds here. -/
theorem tq_csubst_closed : (tqRestore.csubst (tqAux tqAuxNodeB) tqK).Closed :=
  VIndRestore.csubst_closed tqRestore (tqAux tqAuxNodeB) tqK ⟨trivial, trivial⟩
    tq_tyArgs_closedNp

/-- **The substitution fires**: `tyApp'` at the companion member is *not* fixed by `csubst`. -/
theorem tq_tyApp'_substC_fires :
    ((tqAux tqAuxNodeB).tyApp' 1 2 (bvars 0 1)).substC
        (tqRestore.csubst (tqAux tqAuxNodeB) tqK)
      ≠ (tqAux tqAuxNodeB).tyApp' 1 2 (bvars 0 1) := by decide

/-- **The `instAll` window is not an identity**: the lifted substituted domain differs from the
answer, so §2's computation moves the term. -/
theorem tq_tyApp'_window_moves :
    (((tqAux tqAuxNodeB).tyApp' 1 2 (bvars 0 1)).substC
        (tqRestore.csubst (tqAux tqAuxNodeB) tqK)).liftN 4 1
      ≠ ((tqAux tqAuxNodeB).tyApp' 1 5 [(.sort .zero : VExpr)]).substC
        (tqRestore.csubst (tqAux tqAuxNodeB) tqK) := by decide

/-- **§2's equation at `ni = 1`, by kernel computation** — an independent confirmation. -/
theorem tq_tyApp'_substC_instAll_decide :
    instAll ((((tqAux tqAuxNodeB).tyApp' 1 2 (bvars 0 1)).substC
          (tqRestore.csubst (tqAux tqAuxNodeB) tqK)).liftN 4 1)
        (([(.sort .zero : VExpr)]).map
          (VExpr.substC · (tqRestore.csubst (tqAux tqAuxNodeB) tqK))) 0
      = ((tqAux tqAuxNodeB).tyApp' 1 5 [(.sort .zero : VExpr)]).substC
          (tqRestore.csubst (tqAux tqAuxNodeB) tqK) := by decide

/-- **…and the same through §2**, so §2's hypotheses are jointly satisfied at `ni > 0`. -/
theorem tq_tyApp'_substC_instAll_gen :
    instAll ((((tqAux tqAuxNodeB).tyApp' 1 (1 + 1) (bvars 0 1)).substC
          (tqRestore.csubst (tqAux tqAuxNodeB) tqK)).liftN (3 + 1) 1)
        (([(.sort .zero : VExpr)]).map
          (VExpr.substC · (tqRestore.csubst (tqAux tqAuxNodeB) tqK))) 0
      = ((tqAux tqAuxNodeB).tyApp' 1 5 [(.sort .zero : VExpr)]).substC
          (tqRestore.csubst (tqAux tqAuxNodeB) tqK) :=
  VInductDecl'.tyApp'_substC_instAll tq_csubst_closed (ni := 1) (j := 1) (K := 3) rfl rfl

end MRedex.TQWit

/-! ## §7 §4's `A₀` and `hres` at `ntreeAux`: the shape check, measured

§5 bounds §3 from below.  §4 is a larger hypothesis set and this section bounds the two slots that
could be *mis-stated* — the ones where a wrong offset would make the premise set empty without any
instrument noticing.

`iotaHargs_of_heads` fixes `A₀ := D.tyAppR' R j (D.nm + D.nmin + C.fields.length) …`.  The three
hand proofs at `ntreeAux` (§T16.15 of `NestedTele.lean`) each *chose* an `A₀` independently.  They
agree, by `decide`, at all three rules — so §4's `hconv`/`hmaj` slots are stated at exactly the
types the witnesses satisfy.

`hres` — `instAll BC' (bvars 0 C.fields.length) = A₀`, the constructor's result identification at
the ι-rule numbering — is then satisfiable at each rule with `BC'` the `A₀` lifted over the field
telescope, which is the `B'` that `VIndRestore.instAt_ctor_hpi` (§T10) computes.  Both facts are
`decide`.

**Not checked here, and this is the honest list**: `hOnp`, `hbvT`/`hbvC`, `hbodyT`/`hbodyC`,
`hAsT`/`hAsC`, `hpiT`/`hpiC`, `hsortT`, and `htele`.  So §4's hypothesis set is **not** known to be
jointly satisfiable; what is measured is that the two slots §4 *invents* line up with the witness.
See `docs/handoff-iotahargs.md` §5 for where each of the rest comes from. -/

namespace InductiveDeclExamples

open VExpr (bvars instAll)

/-- §4's `A₀` at `nlistNil` is `rIotaRest_nil`'s. -/
theorem ntree_A0_nil_eq :
    ntreeAux.tyAppR' ntreeRestore 1 (ntreeAux.nm + ntreeAux.nmin + nlistNil.fields.length)
        ((nlistNil.args.map fun a =>
          (ntreeAux.atRec a).liftN (ntreeAux.nm + ntreeAux.nmin) nlistNil.fields.length).map
            (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK)))
      = .app rLt (.app rNt (.bvar 5)) := by decide

/-- §4's `A₀` at `nlistCons` is `rIotaRest_cons`'s. -/
theorem ntree_A0_cons_eq :
    ntreeAux.tyAppR' ntreeRestore 1 (ntreeAux.nm + ntreeAux.nmin + nlistCons.fields.length)
        ((nlistCons.args.map fun a =>
          (ntreeAux.atRec a).liftN (ntreeAux.nm + ntreeAux.nmin) nlistCons.fields.length).map
            (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK)))
      = .app rLt (.app rNt (.bvar 7)) := by decide

/-- §4's `A₀` at `ntreeNode` is `rIotaRest_node`'s. -/
theorem ntree_A0_node_eq :
    ntreeAux.tyAppR' ntreeRestore 0 (ntreeAux.nm + ntreeAux.nmin + ntreeNode.fields.length)
        ((ntreeNode.args.map fun a =>
          (ntreeAux.atRec a).liftN (ntreeAux.nm + ntreeAux.nmin) ntreeNode.fields.length).map
            (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK)))
      = .app rNt (.bvar 7) := by decide

/-- **`hres` is satisfiable at all three rules**, with `BC'` the `A₀` lifted over the field
telescope — `instAt_ctor_hpi`'s `B'`.  At `nlistNil` the field telescope is empty and `hres` is an
identity; at the two two-field constructors it moves the de Bruijn index by exactly `nf`. -/
theorem ntree_hres_satisfiable :
    instAll (.app rLt (.app rNt (.bvar 5))) (bvars 0 nlistNil.fields.length) 0
        = .app rLt (.app rNt (.bvar 5))
      ∧ instAll (.app rLt (.app rNt (.bvar 9))) (bvars 0 nlistCons.fields.length) 0
        = .app rLt (.app rNt (.bvar 7))
      ∧ instAll (.app rNt (.bvar 9)) (bvars 0 ntreeNode.fields.length) 0
        = .app rNt (.bvar 7) := by decide

end InductiveDeclExamples

/-! ## §8 Axiom audit

Hole-freeness only; `docs/vacuity-ledger.md` §0's warning applies — §5, §6 and §7 are the content
checks, and none of them is an axiom line. -/

#print axioms Lean4Lean.VExpr.substC_instAll
#print axioms Lean4Lean.VInductDecl'.tyApp'_substC_instAll
#print axioms Lean4Lean.VInductDecl'.lookup_motive_iotaCtx_substC
#print axioms Lean4Lean.VIndRestore.iotaHargs_hfunM
#print axioms Lean4Lean.VIndRestore.iotaHargs_of_heads
#print axioms Lean4Lean.InductiveDeclExamples.ntree_hfunM
#print axioms Lean4Lean.InductiveDeclExamples.rIotaRest_nil_gen
#print axioms Lean4Lean.InductiveDeclExamples.rIotaRest_cons_gen
#print axioms Lean4Lean.InductiveDeclExamples.rIotaRest_node_gen
#print axioms Lean4Lean.MRedex.TQWit.tq_csubst_closed
#print axioms Lean4Lean.MRedex.TQWit.tq_tyApp'_substC_fires
#print axioms Lean4Lean.MRedex.TQWit.tq_tyApp'_window_moves
#print axioms Lean4Lean.MRedex.TQWit.tq_tyApp'_substC_instAll_decide
#print axioms Lean4Lean.MRedex.TQWit.tq_tyApp'_substC_instAll_gen
#print axioms Lean4Lean.InductiveDeclExamples.ntree_A0_nil_eq
#print axioms Lean4Lean.InductiveDeclExamples.ntree_A0_cons_eq
#print axioms Lean4Lean.InductiveDeclExamples.ntree_A0_node_eq
#print axioms Lean4Lean.InductiveDeclExamples.ntree_hres_satisfiable

end Lean4Lean
