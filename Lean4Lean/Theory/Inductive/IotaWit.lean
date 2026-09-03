import Lean4Lean.Theory.Inductive.IotaHargsGen
import Lean4Lean.Theory.Inductive.ParamRedex

/-!
# `IotaWit`: `iotaHargs_of_heads` instantiated at a SECOND parameterised block

`Theory/Inductive/IotaHargsGen.lean` §4 (`VIndRestore.iotaHargs_of_heads`, arity 38) is the first
declaration in the tree with `VIndRestore.IotaHargs` in its conclusion and no witness in its
statement.  `docs/handoff-iotahargs.md` §5d grades it **"hole-free, shape-checked, inhabitation
unknown"**: eleven of its hypotheses — `hOnp`, `hbvT`, `hbvC`, `hbodyT`, `hbodyC`, `hAsT`, `hAsC`,
`hpiT`, `hpiC`, `hsortT`, `htele` — had never been checked at any witness, and no simultaneous
instance had been built.

This file builds one, at `MRedex.MPWit.mpAux mpAuxNodeB` — the **non-canonical** parameterised
redex block (`ParamRedex.lean` §1), whose companion constructor stores a β-redex.  Three results,
graded separately:

* **§1 — a restriction nobody had recorded.**  §4 inherits `hK : T.name ∈ K`, and at the member the
  step *declares* that is **false** (measured at both parameterised blocks).  So §4 covers 1 of
  `MP`'s 2 ι-rules and 2 of `NTree`'s 3.  §1a then measures that the uncovered rules are the ones
  where the head does **not** move, so the restriction is cheap — but it is real, and it means §4
  is not by itself a producer of `IotaHargs` for a whole block.
* **§2 — the degeneracy does NOT lift.**  `T.indices = []` at *both* members of `mpAux` and
  `C.args = []` at *both* its constructors, so §2 of `IotaHargsGen` still has an empty `instAll`
  window here.  `docs/handoff-iotahargs.md` §5b already said this for `MPWit.mpAux`; re-measured.
* **§3 — §4's hypothesis set IS jointly satisfiable**, at `j = 1`, `C = mpAuxNodeB`
  (`mp_iotaHargs_node_gen`, arity 5; `mp_iotaHargs_node_inhabited`, **arity 0**).  All eleven
  previously-unchecked hypotheses hold simultaneously; §4 then reproduces `mpIotaHargs_node`'s
  conclusion, and §5 routes obligation (C) at this block through §4 for the companion rule
  (`mp_iotaRulesRS_wf_gen`, arity 0).  §4 of this file measures which of the eleven carry content
  here and which sit at the empty window.

**This is not the flip, and it is not a discharge of (C) in general.**  What it converts is
§5d's "inhabitation unknown" into "inhabited, at two structurally different blocks", and it adds
one new obstruction (§1).
-/

namespace Lean4Lean

/-! ## §1 The `hK` restriction: §4 cannot reach the block's own member

`iotaHargs_of_heads` inherits `hK : T.name ∈ K` from `substC_tyApp'_defeq_tyAppR'_comp` and
`substC_ctorApp'_defeq_ctorAppR_comp` (`NestedRules.lean:1783/1803`), where it is load-bearing:
`hat.tySome j T hT hK` / `hat.ctorSome …` is what makes `substC` fire on the head constant
(`substC_tyApp'_comp`, `:1758`).  At the member the step **declares**, `σ` is `none` at that name,
so `hK` is false — not merely unproved.

Measured at both parameterised blocks in the tree. -/

theorem mp_own_not_mem_K : ((MRedex.MPWit.mpAux MRedex.MPWit.mpAuxNodeB).types.getD 0 default).name
    ∉ MRedex.MPWit.mpK := by decide

theorem ntree_own_not_mem_K : (InductiveDeclExamples.ntreeAux.types.getD 0 default).name
    ∉ InductiveDeclExamples.ntreeK := by decide

/-- …and the companion members ARE in `K`, so `hK` is not vacuous in the other direction. -/
theorem mp_companion_mem_K :
    ((MRedex.MPWit.mpAux MRedex.MPWit.mpAuxNodeB).types.getD 1 default).name
      ∈ MRedex.MPWit.mpK := by decide

theorem ntree_companion_mem_K : (InductiveDeclExamples.ntreeAux.types.getD 1 default).name
    ∈ InductiveDeclExamples.ntreeK := by decide

/-- **So §4 covers 1 of `MP`'s 2 ι-rules and 2 of `NTree`'s 3** — the uncovered ones are at
`j = 0`: the `MP.obj` and `NTree.node` rules. -/
theorem mp_ctorsAll_own_rule :
    (MRedex.MPWit.mpAux MRedex.MPWit.mpAuxNodeB).ctorsAll
      = [(0, MRedex.MPWit.mpObj), (1, MRedex.MPWit.mpAuxNodeB)] := rfl

/-! ### §1a …and the restriction is cheap: at the uncovered rules the head does not move

`hK` is exactly the condition that makes the substituted head a saturated redex.  Where it fails
the substitution is the identity on the head and `tyAppR'` collapses to `tyApp'`
(`VIndRestore.OwnId.tyAppR'_eq`, row 143d's head face), so §4's `hconv` slot degenerates to a
typing rather than a conversion.  Measured at both blocks, at the `k` the ι-rule uses. -/

theorem mp_csubst_own_none :
    MRedex.MPWit.mpRestore.csubst (MRedex.MPWit.mpAux MRedex.MPWit.mpAuxNodeB) MRedex.MPWit.mpK
        (((MRedex.MPWit.mpAux MRedex.MPWit.mpAuxNodeB).types.getD 0 default).name) = none := rfl

theorem mp_own_tyhead_fixed :
    (((MRedex.MPWit.mpAux MRedex.MPWit.mpAuxNodeB).tyApp' 0 6 []).substC
        (MRedex.MPWit.mpRestore.csubst (MRedex.MPWit.mpAux MRedex.MPWit.mpAuxNodeB)
          MRedex.MPWit.mpK))
      = (MRedex.MPWit.mpAux MRedex.MPWit.mpAuxNodeB).tyAppR' MRedex.MPWit.mpRestore 0 6 [] := by
  decide

theorem ntree_own_tyhead_fixed :
    (InductiveDeclExamples.ntreeAux.tyApp' 0 7 []).substC
        (InductiveDeclExamples.ntreeRestore.csubst InductiveDeclExamples.ntreeAux
          InductiveDeclExamples.ntreeK)
      = InductiveDeclExamples.ntreeAux.tyAppR' InductiveDeclExamples.ntreeRestore 0 7 [] := by
  decide

/-! ## §2 The degeneracy, re-measured at `mpAux` — it does NOT lift

`docs/handoff-iotahargs.md` §5b measured `T.indices = []` at `ntreeAux`, `MPWit.mpAux` and
`MRWit.mrAux`, and `C.args = []` at `ntreeAux`'s three constructors.  Re-measured here
independently, including the `C.args` half at `mpAux`'s two constructors, which §5b stated only
for `ntreeAux`.  So `IotaHargsGen` §2's `instAll` window is **empty at this witness too**, and
§4's `hidx`/`hAsT`/`hpiT`/`hsortT` are at that empty window in §3 below (§4 of this file says which
is which). -/

theorem mp_types_unindexed :
    ∀ T ∈ (MRedex.MPWit.mpAux MRedex.MPWit.mpAuxNodeB).types, T.indices = [] := by decide

theorem mp_ctorsAll_args_nil :
    ∀ p ∈ (MRedex.MPWit.mpAux MRedex.MPWit.mpAuxNodeB).ctorsAll, p.2.args = [] := by decide

/-! ## §3 §4's hypothesis set, JOINTLY SATISFIED at the companion ι-rule of `MP`

The abbreviations, the ι-context written out, and the six equations §4's slots need.  Every one
is `decide` or `rfl` on closed data, so none of them is an instance of §4. -/

namespace MRedex.MPWit

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars liftTele instAll)
open MRedex.MRWit (MDep mrNode mrDepDecl)

/-- The block, its substitution, and the companion ι-rule's context. -/
abbrev mpD : VInductDecl' := mpAux mpAuxNodeB
abbrev mpS : CSubst := mpRestore.csubst (mpAux mpAuxNodeB) mpK
abbrev mpIotaGamma : List VExpr := ((mpD.iotaCtx mpAuxNodeB).map (VExpr.substC · mpS)).reverse

/-- The seven-entry ι-context, written out: §17's five-entry shared prefix (reversed) under the
constructor's own two fields — `Prop` and the **stored redex** `mpFd 5 0`. -/
theorem mpIotaGamma_eq :
    mpIotaGamma = [mpFd 5 0, .sort .zero, mpA4, mpA3, mpA2, mpA1, mpA0] := by decide

/-- …split the way §T6.1's `hasArgs_params_bvars_ctx` needs it: six entries over the parameter
block.  This is what makes `hbvT`/`hbvC` a real lookup at `np = 1` rather than `HasArgs.nil`. -/
theorem mpIotaGamma_split :
    ((mpD.iotaCtx mpAuxNodeB).map (VExpr.substC · mpS)).reverse
      = [mpFd 5 0, .sort .zero, mpA4, mpA3, mpA2, mpA1]
        ++ ((mpD.atRecTele mpD.params).reverse ++ []) := by decide

/-- The two presented heads at the companion member, computed: `mpVc 0` and `mpNc 0`, i.e. the
*contractions* `MDep Prop (fun _ => MP α)` and `MDep.node Prop (fun _ => MP α)`. -/
theorem mp_atRec_tyBody_one' : mpD.atRec (mpRestore.tyBody mpD 1) = mpVc 0 := rfl

theorem mp_atRec_ctorBody_one : mpD.atRec (mpRestore.ctorBody mpD 1 mpAuxNodeB) = mpNc 0 := rfl

/-- **§4's canonical `A₀` at this rule is `mpIotaHargs_node`'s** — `mpVc 6`, chosen independently
by the hand proof (`ParamRedex.lean` §17.2).  The `ntree_A0_*_eq` check of `IotaHargsGen` §7, at
the second parameterised block. -/
theorem mp_A0_node : mpD.tyAppR' mpRestore 1 (mpD.nm + mpD.nmin + mpAuxNodeB.fields.length)
    ((mpAuxNodeB.args.map fun a => (mpD.atRec a).liftN (mpD.nm + mpD.nmin)
      mpAuxNodeB.fields.length).map (VExpr.substC · mpS)) = mpVc 6 := by decide

theorem mp_pcl : VExpr.ClosedTele (mpD.atRecTele mpD.params) 0 := ⟨trivial, trivial⟩

/-- **`hpiC` at this rule**: the constructor head's type, instantiated at the parameter spine
`bvars 6 1`, is a two-entry Pi whose second domain is the **stored β-redex**. -/
theorem mp_hpiC : instAll (.forallE (.sort .zero) (.forallE (mpFd 1 0) (mpVc 2)))
    (bvars (mpAuxNodeB.fields.length + (mpD.nm + mpD.nmin)) mpD.np)
    = mkPi [.sort .zero, mpFd 7 0] (mpVc 8) := by decide

/-- **`hres` at this rule**: the constructor's result identification, `instAll BC' (bvars 0 nf)`
against §4's `A₀`.  `nf = 2`, and the index moves by exactly `nf`. -/
theorem mp_hres : instAll (mpVc 8) (bvars 0 mpAuxNodeB.fields.length) = mpVc 6 := by decide

section
variable {F : VEnv}
variable (hD : F.constants ``MDep = some ⟨0, MRWit.mrDepType.type⟩)
variable (hP : F.constants ``MP
  = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
variable (hNd : F.constants ``MDep.node = some ⟨0, mrNode.type mrDepDecl 0⟩)
variable (hOb : F.constants ``MP.obj
  = some ⟨0, .forallE (.sort (.succ .zero)) (.forallE (mpVc 0) (.app mpNt (.bvar 1)))⟩)

include hD hP hNd hOb in
/-- **`hOnp`'s inner half** — the companion ι-context is a context.  §18.1's `mpOnCtx₀`/`mpOnCtx₁`
do the five-entry prefix; the two extra entries are the constructor's own `Prop` field and the
stored redex, the latter typed by `mpBetaF`. -/
theorem mpOnCtxIotaNode : OnCtx mpIotaGamma (F.IsType 1) := by
  obtain ⟨u2, h2⟩ := mpE2 hD hP
  obtain ⟨u3, h3⟩ := mpE3 hD hP hOb
  obtain ⟨u4, h4⟩ := mpE4 hD hP hNd
  rw [mpIotaGamma_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨trivial, mpIsTypeA0⟩, mpIsTypeA1 hP⟩, ⟨_, h2.hasType.1⟩⟩, ⟨_, h3.hasType.1⟩⟩,
    ⟨_, h4.hasType.1⟩⟩, ⟨_, .sortDF (l := .zero) trivial trivial rfl⟩⟩, ?_⟩
  exact ⟨_, (mpBetaF hP (m := 5) (j := 0)
    (.succ (.succ (.succ (.succ (.succ .zero))))) .zero).hasType.1⟩

include hD hP hNd hOb in
/-- **`iotaHargs_of_heads` INSTANTIATED**, at the companion ι-rule of the non-canonical
parameterised redex block.  All 38 arguments supplied at once; the conclusion is
`mpIotaHargs_node`'s, so §4's general route reproduces the hand proof at a second, structurally
different witness.

Where each of `docs/handoff-iotahargs.md` §5d's eleven unchecked hypotheses comes from:

| §5d hypothesis | here |
| --- | --- |
| `htele` | `mpIotaTele_node` (§17) |
| `hOnp` | `VEnv.onCtx_params_append` over `mpOnCtxIotaNode` |
| `hbvT`, `hbvC` | `hasArgs_params_bvars_ctx` at `mpIotaGamma_split` — a real `np = 1` lookup |
| `hbodyT` | `mp_tyBody_hasType` (§5.1 of `ParamRedex.lean`), *already in the tree* |
| `hbodyC` | `mpBetaN`'s right-hand typing at `k = 0` — the restored `MDep.node` head |
| `hpiC` | `mp_hpiC` — moves (`mp_hpiC_moves`) |
| `hAsC` | two `Lookup`s, the second at a **β-redex** domain (`mp_hAsC_second_is_redex`) |
| `hAsT`, `hpiT`, `hsortT` | at the **empty** index/argument window (§2) — degenerate, disclosed |
| `hres` | `mp_hres` — moves (`mp_hres_moves`) | -/
theorem mp_iotaHargs_node_gen (henv : F.Ordered) :
    mpRestore.IotaHargs mpD mpS F 1 mpAuxNodeB := by
  refine VIndRestore.iotaHargs_of_heads (K := mpK) (T := (mpD.types.getD 1 default))
    mpRestore_domSep.substAt mpRestore_substFree mp_csubst_closed
    (mpRestore_tyArgs_closedNp 1) henv rfl (by decide) (List.Mem.head _) (by decide) rfl
    (AsT := []) (BT := .sort (.succ .zero)) (BT' := .sort (.succ .zero))
    (AsC := [.sort .zero, mpFd 7 0]) (BC := .forallE (.sort .zero) (.forallE (mpFd 1 0) (mpVc 2)))
    (BC' := mpVc 8) (v := .succ .zero)
    (mpIotaTele_node hD hP hNd hOb) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact .nil
  · exact VEnv.onCtx_params_append henv mp_pcl ⟨trivial, mpIsTypeA0⟩
      (mpOnCtxIotaNode hD hP hNd hOb)
  · rw [mpIotaGamma_split]; exact VIndRestore.hasArgs_params_bvars_ctx mp_pcl rfl
  · exact mp_tyBody_hasType hD hP
  · rfl
  · exact .nil
  · rfl
  · rw [mpIotaGamma_split]; exact VIndRestore.hasArgs_params_bvars_ctx mp_pcl rfl
  · exact (mpBetaN hP hNd (Γ := .sort (.succ .zero) :: mpIotaGamma) (k := 0) .zero).hasType.2
  · exact mp_hpiC
  · exact .cons (.bvar (.succ .zero)) (.cons (.bvar .zero) .nil)
  · exact mp_hres

include hD hP hNd hOb in
/-- **`hdata` at `MP`, with the companion rule routed through §4** and the own rule through
`mpIotaHargs_obj` — which §1 shows §4 cannot reach. -/
theorem mp_hdata_gen (henv : F.Ordered) :
    ∀ (q j : Nat) (C : VIndCtor), mpD.ctorsAll[q]? = some (j, C) →
      mpRestore.IotaHargs mpD mpS F j C := by
  intro q j C hq
  rw [mpAuxB_ctorsAll_eq] at hq
  match q with
  | 0 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    exact mpIotaHargs_obj hD hP hNd hOb
  | 1 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    exact mp_iotaHargs_node_gen hD hP hNd hOb henv
  | (n+2) => simp at hq

end

/-! ### §3a Joint inhabitation with nothing assumed

`docs/vacuity-ledger.md` §0: a per-hypothesis check is not a joint one, and an arity-0 theorem is
the certificate.  `mp_stage₃_exists` supplies the seven staging environments, so the five
parameters of §3 are discharged rather than assumed. -/

/-- **ARITY 0**: §4's hypothesis set is inhabited at `mpAux mpAuxNodeB`, `j = 1`. -/
theorem mp_iotaHargs_node_inhabited :
    ∃ F : VEnv, F.Ordered ∧ mpRestore.IotaHargs mpD mpS F 1 mpAuxNodeB := by
  obtain ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩ := mp_stage₃_exists
  refine ⟨F₃, mpF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃, mp_iotaHargs_node_gen
    (mpF₃_mdep h hF₁ hF₂ hF₃) (mpF₃_mp hF₁ hF₂ hF₃) (mpF₃_mdepNode h hF₁ hF₂ hF₃)
    (mpF₃_obj hF₂ hF₃) (mpF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃)⟩

/-! ## §4 What is degenerate here and what is not, stated separately

`docs/handoff-iotahargs.md` §5b's degeneracy survives (§2 above), so three of §3's twelve slots
sit at the empty window.  The other nine do not, and these are the measurements that say so —
none of them is an instance of §4. -/

/-- `hpiC`'s `instAll` is **not** an identity: the parameter spine really moves the term. -/
theorem mp_hpiC_moves :
    instAll (.forallE (.sort .zero) (.forallE (mpFd 1 0) (mpVc 2)))
        (bvars (mpAuxNodeB.fields.length + (mpD.nm + mpD.nmin)) mpD.np)
      ≠ .forallE (.sort .zero) (.forallE (mpFd 1 0) (mpVc 2)) := by decide

/-- `hres` moves too — it is not the `nf = 0` identity that `nlistNil` gives. -/
theorem mp_hres_moves : mpVc 8 ≠ mpVc 6 := by decide

/-- **`hAsC` types an argument at a β-redex domain** — the structural feature `ntreeAux` does not
have, and the reason this witness is not a re-run of `IotaHargsGen` §5. -/
theorem mp_hAsC_second_is_redex :
    ([(.sort .zero : VExpr), mpFd 7 0]).getD 1 default
      = .app (.lam (.sort .zero) (.app mpNt (.bvar 8))) (.bvar 0) := rfl

/-- …and the ι-context itself moves under restoration, so `htele` is not `TeleDefEq.rfl`
(quoted from §17.1, re-stated here as the premise §3 relies on):
`mpIotaCtx_node_ne`. -/
theorem mp_htele_nontrivial :
    ((mpAux mpAuxNodeB).iotaCtx mpAuxNodeB).map (VExpr.substC · mpS)
      ≠ ((mpAux mpAuxNodeB).iotaCtxR mpRestore mpAuxNodeB).map (VExpr.substC · mpS) :=
  mpIotaCtx_node_ne

/-! ## §5 …and obligation (C) at this block, through §4 for the companion rule

`mpAuxB_iotaRulesRS_wf` (`ParamRedex.lean` §18.4) with `mpAuxB_hdata` replaced by `mp_hdata_gen`.
Nothing new is discharged — (C) was already a theorem here — but it says §4's general route is
strong enough to carry a real obligation at a parameterised block, which "shape-checked" was not. -/

theorem mp_iotaRulesRS_wf_gen :
    ∃ (env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv), VEnv.empty.addInduct' mrDepDecl = some env₁ ∧
      env₁.addIndTypes mpD = some E₁ ∧ E₁.addIndCtors mpD = some E₂ ∧
      E₂.addIndRecs mpD = some E₃ ∧
      env₁.addConstList (mpD.typeConstsC mpK) = some F₁ ∧
      F₁.addConstList (mpD.ctorConstsCR mpRestore mpK) = some F₂ ∧
      F₂.addConstList (mpD.recConstsR mpRestore mpK) = some F₃ ∧
      (∀ df ∈ mpD.iotaRulesRS mpRestore mpK, VDefEq.WF F₃ df) := by
  obtain ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩ := mp_stage₃_exists
  refine ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃, ?_⟩
  exact VEnv.iotaRulesRS_wf_of_hargsD mpRestore_ownId mpRestore_domSep.substAt
    mpRestore_substFree mp_csubst_closed
    (mp_csubst_WFD₃ h hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)
    (mpAuxB_WF.iotaCtx (mpEnv_ordered h) hE₁ hE₂ hE₃)
    (mpF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃) mpAuxB_recArg_lt
    (mp_hdata_gen (mpF₃_mdep h hF₁ hF₂ hF₃) (mpF₃_mp hF₁ hF₂ hF₃)
      (mpF₃_mdepNode h hF₁ hF₂ hF₃) (mpF₃_obj hF₂ hF₃)
      (mpF₃_ordered h hE₁ hE₂ hF₁ hF₂ hF₃))

end MRedex.MPWit

/-! ## §6 Axiom audit

Hole-freeness only.  `docs/vacuity-ledger.md` §0's warning applies: §1–§2 and §4 are the content
measurements, §3a and §5 the joint-inhabitation certificates, and no axiom line below is either. -/

#print axioms Lean4Lean.mp_own_not_mem_K
#print axioms Lean4Lean.ntree_own_not_mem_K
#print axioms Lean4Lean.mp_companion_mem_K
#print axioms Lean4Lean.ntree_companion_mem_K
#print axioms Lean4Lean.mp_ctorsAll_own_rule
#print axioms Lean4Lean.mp_csubst_own_none
#print axioms Lean4Lean.mp_own_tyhead_fixed
#print axioms Lean4Lean.ntree_own_tyhead_fixed
#print axioms Lean4Lean.mp_types_unindexed
#print axioms Lean4Lean.mp_ctorsAll_args_nil
#print axioms Lean4Lean.MRedex.MPWit.mpIotaGamma_eq
#print axioms Lean4Lean.MRedex.MPWit.mpIotaGamma_split
#print axioms Lean4Lean.MRedex.MPWit.mp_A0_node
#print axioms Lean4Lean.MRedex.MPWit.mp_hpiC
#print axioms Lean4Lean.MRedex.MPWit.mp_hres
#print axioms Lean4Lean.MRedex.MPWit.mpOnCtxIotaNode
#print axioms Lean4Lean.MRedex.MPWit.mp_iotaHargs_node_gen
#print axioms Lean4Lean.MRedex.MPWit.mp_hdata_gen
#print axioms Lean4Lean.MRedex.MPWit.mp_iotaHargs_node_inhabited
#print axioms Lean4Lean.MRedex.MPWit.mp_hpiC_moves
#print axioms Lean4Lean.MRedex.MPWit.mp_hres_moves
#print axioms Lean4Lean.MRedex.MPWit.mp_hAsC_second_is_redex
#print axioms Lean4Lean.MRedex.MPWit.mp_htele_nontrivial
#print axioms Lean4Lean.MRedex.MPWit.mp_iotaRulesRS_wf_gen

end Lean4Lean
