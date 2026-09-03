import Lean4Lean.Theory.Inductive.RecTyped
import Lean4Lean.Theory.Inductive.HTeleGen

/-!
# `FamInhabNTree`: obligation (B)'s data families INHABITED at a parameterised nested block

`docs/handoff-rectyped.md` §3b and `docs/handoff-htele.md` §4b both record the same gap: the four
bundled data families of `VEnv.recConstsR_wf_of_recHargsD` (`Theory/Inductive/RecTyped.lean` §4)
are *"inhabited nowhere at `D.np > 0`"*, so both that closure and (C)'s
`VIndRestore.hdata_of_recHargs_and_heads` (`Theory/Inductive/HTeleRecB.lean` §2) were hole-free
reductions with an unknown premise set.

This file closes that gap at the canonical parameterised nested block `ntreeAux` (`D.np = 1`).

* §1 the four families, each at every index the closures demand, over an arbitrary environment
  `F` carrying the five `listDecl`/`NTree` constant lookups;
* §2 the family *functions* in the exact shape the closures bind;
* §3 arity-0 joint inhabitation at `F₂` (obligation (B)'s environment) and at `F₃` ((C)'s);
* §4 obligation (B) **and** obligation (C) at `ntreeAux` *through the general bundle closures*;
* §5 anti-vacuity: which slots are degenerate and which carry a real conversion.

**Nothing here is edited outside this file.**  `RecTyped.lean`, `HTeleRecB.lean`, `HTeleGen.lean`
and `HargsShared.lean` are imported only.
-/

namespace Lean4Lean

open VExpr (bvars liftTele instAll mkPi mkApp)

namespace InductiveDeclExamples

/-! ## §0 The bundle slots at this block, written out

Every equation is `rfl` or `decide`.  These are what make §1's proofs readable: the families are
stated over `atRecTele`/`substC`/`liftTele`, and at this block each is a two-entry telescope of
`NTree`/`List` applications. -/

/-- The motive block's body at the companion index: the *restored* head `List (NTree α)`. -/
theorem fi_motBody : ntreeAux.atRec (ntreeRestore.tyBody ntreeAux 1)
    = .app rLt (.app rNt (.bvar 0)) := rfl

/-- …and its ambient context is the parameter block alone. -/
theorem fi_parCtx : (ntreeAux.atRecTele ntreeAux.params).reverse
    = [.sort (.succ (.param 1))] := rfl

/-- The constructor block's bodies at the companion's two constructors. -/
theorem fi_ctorBody_nil : ntreeAux.atRec (ntreeRestore.ctorBody ntreeAux 1 nlistNil)
    = .app (.const ``List.nil [.param 1]) (.app rNt (.bvar 0)) := rfl

theorem fi_ctorBody_cons : ntreeAux.atRec (ntreeRestore.ctorBody ntreeAux 1 nlistCons)
    = .app (.const ``List.cons [.param 1]) (.app rNt (.bvar 0)) := rfl


/-! ### §0b The field blocks of `MinorFldDefEq`, at each minor index

`MinorFldDefEq q C` lifts by `D.nm + q`, so unlike `HTeleGen.lean` §3's `q = D.nmin` instance the
offsets differ per entry.  Written out at all three. -/

/-- The ambient context at minor index `q`, for `q = 0, 1, 2`. -/
theorem fi_fldCtx0 : (((ntreeAux.minors.map (VExpr.substC · gS)).take 0).reverse
      ++ ((ntreeAux.motives.map (VExpr.substC · gS)).reverse
        ++ ((ntreeAux.atRecTele ntreeAux.params).map (VExpr.substC · gS)).reverse))
    = [rA2, rA1, rA0] := by decide

theorem fi_fldCtx1 : (((ntreeAux.minors.map (VExpr.substC · gS)).take 1).reverse
      ++ ((ntreeAux.motives.map (VExpr.substC · gS)).reverse
        ++ ((ntreeAux.atRecTele ntreeAux.params).map (VExpr.substC · gS)).reverse))
    = [rA3, rA2, rA1, rA0] := by decide

theorem fi_fldCtx2 : (((ntreeAux.minors.map (VExpr.substC · gS)).take 2).reverse
      ++ ((ntreeAux.motives.map (VExpr.substC · gS)).reverse
        ++ ((ntreeAux.atRecTele ntreeAux.params).map (VExpr.substC · gS)).reverse))
    = [rA4, rA3, rA2, rA1, rA0] := by decide

theorem fi_fld0_lhs : liftTele (ntreeAux.nm + 0)
      ((ntreeAux.atRecTele (ntreeNode.fields.map (·.type))).map (VExpr.substC · gS))
    = [.bvar 2, .app rV (.bvar 3)] := by decide

theorem fi_fld0_rhs : liftTele (ntreeAux.nm + 0)
      ((ntreeAux.atRecTele (ntreeNode.fieldTypesR ntreeAux ntreeRestore)).map
        (VExpr.substC · gS))
    = [.bvar 2, .app rLt (.app rNt (.bvar 3))] := by decide

theorem fi_fld1_lhs : liftTele (ntreeAux.nm + 1)
      ((ntreeAux.atRecTele (nlistNil.fields.map (·.type))).map (VExpr.substC · gS)) = [] := by
  decide

theorem fi_fld1_rhs : liftTele (ntreeAux.nm + 1)
      ((ntreeAux.atRecTele (nlistNil.fieldTypesR ntreeAux ntreeRestore)).map
        (VExpr.substC · gS)) = [] := by decide

theorem fi_fld2_lhs : liftTele (ntreeAux.nm + 2)
      ((ntreeAux.atRecTele (nlistCons.fields.map (·.type))).map (VExpr.substC · gS))
    = [.app rNt (.bvar 4), .app rV (.bvar 5)] := by decide

theorem fi_fld2_rhs : liftTele (ntreeAux.nm + 2)
      ((ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore)).map
        (VExpr.substC · gS))
    = [.app rNt (.bvar 4), .app rLt (.app rNt (.bvar 5))] := by decide

/-! ### §0c The minor block's ambient context, at the two companion constructors -/

theorem fi_minCtx1 :
    (liftTele (ntreeAux.nm + 1)
        ((ntreeAux.atRecTele (nlistNil.fields.map (·.type))).map (VExpr.substC · gS))
      ++ (ntreeAux.ihTypes 1 nlistNil).map (VExpr.substC · gS)).reverse
      ++ (((ntreeAux.minors.map (VExpr.substC · gS)).take 1).reverse
          ++ ((ntreeAux.motives.map (VExpr.substC · gS)).reverse
              ++ (ntreeAux.atRecTele ntreeAux.params).reverse))
    = [rA3, rA2, rA1, rA0] := by decide

theorem fi_minCtx2 :
    (liftTele (ntreeAux.nm + 2)
        ((ntreeAux.atRecTele (nlistCons.fields.map (·.type))).map (VExpr.substC · gS))
      ++ (ntreeAux.ihTypes 2 nlistCons).map (VExpr.substC · gS)).reverse
      ++ (((ntreeAux.minors.map (VExpr.substC · gS)).take 2).reverse
          ++ ((ntreeAux.motives.map (VExpr.substC · gS)).reverse
              ++ (ntreeAux.atRecTele ntreeAux.params).reverse))
    = [.app (.bvar 5) (.bvar 1), .app (.bvar 5) (.bvar 1), .app rV (.bvar 5),
        .app rNt (.bvar 4), rA4, rA3, rA2, rA1, rA0] := by decide


/-! ## §1 The families, over an arbitrary environment with the five constant lookups

The section variables are exactly `ConstSubstNested.lean` §E's, and they are discharged at `F₂`
and at `F₃` in §3 — `ntreeF₂_list` … `ntreeF₂_node`, `ntreeF₃_list` … `ntreeF₃_node`. -/

/-- The companion member of the block, as `D.types[1]?` delivers it. -/
def fiT1 : VIndType where
  name := `_nested.List_1
  type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
  indices := []
  ctors := [nlistNil, nlistCons]

theorem fi_types_one : ntreeAux.types[1]? = some fiT1 := rfl
theorem fi_types_zero : ntreeAux.types[0]? = some (ntreeAux.types.getD 0 default) := rfl

section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
variable (hnil : F.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
variable (hcons : F.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)

include hL hN in
/-- **`MotiveHargs` at the companion type.**  The only index the closure demands it at: the
block's own head is off `K`, where the entry defeq is free.

`hpi`/`hAs`/`hsort` are the `T.indices = []` identities — disclosed as degenerate in §5 — so the
content is `hbody`: the *restored* head `List (NTree α)` typed over the parameter block. -/
theorem fi_motiveHargs : ntreeRestore.MotiveHargs ntreeAux gS F 1 fiT1 :=
  ⟨[], .sort (.succ (.param 1)), .sort (.succ (.param 1)), .succ (.param 1),
    .appDF (rLC hL) (.appDF (rNC hN) (.bvar .zero)), rfl, .nil, rfl⟩

include hL hN in
/-- **`MinorFldDefEq` at `q = 0`** — `NTree.node`, a constructor of the block's *own* head, where
the closure still demands the field defeq because `C.fieldTypesR` rewrites the companion
occurrence inside it (`RecTyped.lean`'s `ntree_node_fieldTypesR_ne`). One `rbetaL`. -/
theorem fi_minorFld_node : ntreeRestore.MinorFldDefEq ntreeAux gS F 0 ntreeNode := by
  rw [VIndRestore.MinorFldDefEq, fi_fldCtx0, fi_fld0_lhs, fi_fld0_rhs]
  exact .rfl (.cons (rbetaL hL hN (k := 3) (.succ (.succ (.succ .zero)))) .nil)

include hL hN in
/-- **`MinorFldDefEq` at `q = 2`** — `_nested.List_1.cons`, the two-recursive-field constructor.
One `rbetaL`, at a *different* offset from `q = 0`'s. -/
theorem fi_minorFld_cons : ntreeRestore.MinorFldDefEq ntreeAux gS F 2 nlistCons := by
  rw [VIndRestore.MinorFldDefEq, fi_fldCtx2, fi_fld2_lhs, fi_fld2_rhs]
  exact .rfl (.cons (rbetaL hL hN (k := 5)
    (.succ (.succ (.succ (.succ (.succ .zero)))))) .nil)

/-- The type of the restored `List.cons` head, applied to the block's parameter. -/
def fiBcons : VExpr := .forallE (.app (.const ``NTree [.param 1]) (.bvar 0))
  (.forallE (.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 1))) (.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 2))))

/-! ### §1c `MinorCtorHargs`, piece by piece and then bundled

The pieces are stated separately from the bundle **on purpose**: `MinorCtorHargs`' component list
changed twice on 2026-09-03 (four conjuncts, then three after the `hAs`-drop stream landed
`Theory/Inductive/HargsShared.lean`'s derivation), and a re-packaging must not invalidate the
content.  §1c1–§1c3 are the content; §1c4 is the assembly, and it is the only thing that breaks if
the bundle is repackaged again.

`fi_hAs_*` is the `HasArgs` conjunct the current bundle no longer carries.  It is kept because it is
what `VIndRestore.minorCtor_hAs` produces in general, and because it is the slot where the β
conversion lives at `nlistCons` — see §5. -/

include hnil hN in
/-- §1c1 `hcbody` at `nlistNil`: the restored `List.nil` head over the parameter block. -/
theorem fi_hcbody_nil : F.HasType 2 [.sort (.succ (.param 1))]
    (.app (.const ``List.nil [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 0)))
    (.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 0))) := by
  refine .appDF (rNilC hnil) (.appDF (rNC hN) (.bvar ?_)); exact .zero

include hcons hN in
/-- §1c1 `hcbody` at `nlistCons`. -/
theorem fi_hcbody_cons : F.HasType 2 [.sort (.succ (.param 1))]
    (.app (.const ``List.cons [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 0))) fiBcons := by
  refine .appDF (rConsC hcons) (.appDF (rNC hN) (.bvar ?_)); exact .zero

include hL hN in
/-- §1c2 `hfun` at `nlistNil`: the minor's own motive `Lookup`, converted across **one** β step.
Not free even here, where the field window is empty. -/
theorem fi_hfun_nil : F.HasType 2 [rA3, rA2, rA1, rA0] (.bvar 1)
    (.forallE (.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 3))) (.sort (.param 0))) := by
  refine .defeqDF (.forallEDF (rbetaL hL hN (k := 3) ?_) (.sortDF rp0_wf rp0_wf rfl))
    (.bvar (.succ .zero))
  exact .succ (.succ (.succ .zero))

include hL hN in
/-- §1c2 `hfun` at `nlistCons`, at the nine-entry context the two fields and two ihs build. -/
theorem fi_hfun_cons : F.HasType 2 [.app (.bvar 5) (.bvar 1), .app (.bvar 5) (.bvar 1),
      .app rV (.bvar 5), .app (.const ``NTree [.param 1]) (.bvar 4), rA4, rA3, rA2, rA1, rA0] (.bvar 6)
    (.forallE (.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 8))) (.sort (.param 0))) := by
  refine .defeqDF (.forallEDF (rbetaL hL hN (k := 8) ?_) (.sortDF rp0_wf rp0_wf rfl))
    (.bvar (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
  exact .succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))

include hL hN in
/-- §1c3 the `HasArgs` conjunct at `nlistCons`: the presented field spine typed against the
**restored** field telescope.  Two `HasArgs.cons` steps, of which the second is a β conversion —
the context declares the second field at the *stored* type `rV #8` and the telescope presents it at
`List (NTree #8)`. -/
theorem fi_hAs_cons : F.HasArgs 2 [.app (.bvar 5) (.bvar 1), .app (.bvar 5) (.bvar 1),
      .app rV (.bvar 5), .app (.const ``NTree [.param 1]) (.bvar 4), rA4, rA3, rA2, rA1, rA0]
    [.app (.const ``NTree [.param 1]) (.bvar 8), .app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 9))] [.bvar 3, .bvar 2] := by
  refine .cons (.bvar (.succ (.succ (.succ .zero))))
    (.cons (.defeqDF (rbetaL hL hN (k := 8) ?_) (.bvar (.succ (.succ .zero)))) .nil)
  exact .succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))

include hN hnil hL in
/-- §1c4 **`MinorCtorHargs` at `q = 1`** — the field-less companion constructor.  Disclosed as the
*degenerate* entry in §5: the field window is empty, so `hpi`'s `mkPi` has no binders.  `hcbody`
and `hfun` are still real. -/
theorem fi_minorCtorHargs_nil : ntreeRestore.MinorCtorHargs ntreeAux gS F 1 1 nlistNil :=
  ⟨.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 0)), fi_hcbody_nil hN hnil, rfl, fi_hfun_nil hL hN⟩

include hN hcons hL in
/-- §1c4 **`MinorCtorHargs` at `q = 2`** — the non-degenerate entry: `_nested.List_1.cons` has
**two** recursive fields and its restored field telescope provably differs from the stored one
(`fi_fld2_lhs` vs `fi_fld2_rhs`), so `hpi`'s `mkPi` really has two binders and they are the restored
ones. -/
theorem fi_minorCtorHargs_cons : ntreeRestore.MinorCtorHargs ntreeAux gS F 2 1 nlistCons :=
  ⟨fiBcons, fi_hcbody_cons hN hcons, rfl, fi_hfun_cons hL hN⟩

end

/-! ### §1d `RecBodyHargs` — (B)'s fourth family, which (C) does not use

`docs/handoff-htele.md` §3 records that (C)'s telescope has no recursor-body entry, so this one is
outside the brief's three.  It is included because it is what upgrades §4 from "(C) through the
bundles" to "**(B) and (C)** through the bundles", and because it is cheap: `hconcl` is free
(`RecTyped.lean` §7 item 3 guessed this and did not check it — it is right). -/

/-- The recursor-body context at this block is §E's telescope on the nose. -/
theorem fi_bodyCtx : (((ntreeAux.atRecTele ntreeAux.params ++ ntreeAux.motives ++ ntreeAux.minors
      ++ liftTele (ntreeAux.nm + ntreeAux.nmin) (ntreeAux.atRecTele fiT1.indices)).map
      (VExpr.substC · gS)).reverse) = rTele.reverse := by decide

theorem fi_bodyHead_lhs : ((ntreeAux.tyApp' 1 (fiT1.indices.length + ntreeAux.nmin + ntreeAux.nm)
      (bvars 0 fiT1.indices.length)).substC gS) = .app rV (.bvar 5) := by decide

theorem fi_bodyHead_rhs : (ntreeAux.tyAppR' ntreeRestore 1
      (fiT1.indices.length + ntreeAux.nmin + ntreeAux.nm) (bvars 0 fiT1.indices.length))
    = .app rLt (.app rNt (.bvar 5)) := by decide

section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)

include hL hN in
/-- **`RecBodyHargs` at the companion recursor.**  The head defeq is one `rbetaL`; the conclusion
is the motive `Lookup` applied to the major premise, and it is **free**. -/
theorem fi_recBodyHargs : ntreeRestore.RecBodyHargs ntreeAux gS F 1 fiT1 := by
  refine ⟨.succ (.param 1), ?_, ?_⟩
  · rw [fi_bodyCtx, fi_bodyHead_lhs, fi_bodyHead_rhs]
    exact rbetaL hL hN (k := 5) (.succ (.succ (.succ (.succ (.succ .zero)))))
  · rw [fi_bodyHead_lhs, fi_bodyCtx]
    exact show F.HasType 2 (.app rV (.bvar 5) :: rTele.reverse) (.app (.bvar 4) (.bvar 0))
      (.sort (.param 0)) from
      .appDF (B := .sort (.param 0))
        (.bvar (.succ (.succ (.succ (.succ .zero))))) (.bvar .zero)

end

/-! ## §2 The family functions, in the shape the closures bind

`VEnv.recConstsR_wf_of_recHargsD` and `VIndRestore.hdata_of_recHargs_and_heads` bind their data as
∀-statements over the block's indices, with the `Hargs` bundles guarded by `T.name ∈ K`.  These are
those statements, discharged. -/

section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
variable (hnil : F.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
variable (hcons : F.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)

include hL hN in
theorem fi_hmotD : ∀ (t : Nat) (T : VIndType), ntreeAux.types[t]? = some T →
    T.name ∈ ntreeK → ntreeRestore.MotiveHargs ntreeAux gS F t T := by
  rintro (_ | _ | t) T hT hK
  · cases hT; exact absurd hK (by decide)
  · cases hT; exact fi_motiveHargs hL hN
  · simp [ntreeAux] at hT

include hL hN in
theorem fi_hfldD : ∀ (q t : Nat) (C : VIndCtor), ntreeAux.ctorsAll[q]? = some (t, C) →
    ntreeRestore.MinorFldDefEq ntreeAux gS F q C := by
  intro q t C hq
  rw [ntreeAux_ctorsAll_eq] at hq
  match q with
  | 0 => obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq; exact fi_minorFld_node hL hN
  | 1 => obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq; exact ntree_minorFld_nil F
  | 2 => obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq; exact fi_minorFld_cons hL hN
  | (n+3) => simp at hq

include hL hN hnil hcons in
theorem fi_hminD : ∀ (q t : Nat) (C : VIndCtor) (T : VIndType),
    ntreeAux.ctorsAll[q]? = some (t, C) → ntreeAux.types[t]? = some T → T.name ∈ ntreeK →
    ntreeRestore.MinorCtorHargs ntreeAux gS F q t C := by
  intro q t C T hq hT hK
  rw [ntreeAux_ctorsAll_eq] at hq
  match q with
  | 0 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    cases hT; exact absurd hK (by decide)
  | 1 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    exact fi_minorCtorHargs_nil hL hN hnil
  | 2 =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hq
    exact fi_minorCtorHargs_cons hL hN hcons
  | (n+3) => simp at hq

include hL hN in
theorem fi_hbodyD : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T →
    T.name ∈ ntreeK → ntreeRestore.RecBodyHargs ntreeAux gS F j T := by
  rintro (_ | _ | j) T hT hK
  · cases hT; exact absurd hK (by decide)
  · cases hT; exact fi_recBodyHargs hL hN
  · simp [ntreeAux] at hT

end


/-! ## §3 Instantiated at the staging environment `F₂` — obligation (B)'s own

The environment distinction is the trap `docs/handoff-htele.md` §5.6 records: the *freshness* inputs
(`ntree_csubst_fresh`) live at the **pre-block** environment `env₁`, the *substitution* inputs
(`ntree_csubst_WFD₂`) at the **staging pair** `(E₂, F₂)`, and the data families at `F₂`.  §3 keeps
them apart by taking all five staging equations and letting `ntreeAux_obligationB_of_bundles` route
them; §1's families are at whichever `F` carries the four lookups, which `F₂` does. -/

section
variable {env₁ E₁ E₂ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
variable (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)

include h hE₁ hE₂ hF₁ hF₂ in
/-- **OBLIGATION (B) AT THE CANONICAL PARAMETERISED NESTED BLOCK, THROUGH THE GENERAL BUNDLE
CLOSURE.**  `RecTyped.lean` §6b left this relative to the four data families and §6c said they were
inhabited nowhere at `D.np > 0`; §1 inhabits all four here, so the closure's premise set is now
known **jointly satisfiable** at a block with `D.np = 1`.

This is not a new proof of (B) at this block — `ConstSubstNested.lean` §E's
`ntreeAux_recConstsR_wf` already had it by the hand-built `mkPi` bridge.  What is new is that
`VEnv.recConstsR_wf_of_recHargsD`, the **general** closure, is certified non-vacuous above
`np = 0`. -/
theorem fi_ntreeAux_obligationB :
    ∀ c ∈ ntreeAux.recConstsR ntreeRestore ntreeK, VConstant.WF F₂ c.2 :=
  ntreeAux_obligationB_of_bundles h hE₁ hE₂ hF₁ hF₂
    (fi_hmotD (ntreeF₂_list h hF₁ hF₂) (ntreeF₂_ntree hF₁ hF₂))
    (fi_hfldD (ntreeF₂_list h hF₁ hF₂) (ntreeF₂_ntree hF₁ hF₂))
    (fi_hminD (ntreeF₂_list h hF₁ hF₂) (ntreeF₂_ntree hF₁ hF₂)
      (ntreeF₂_nil h hF₁ hF₂) (ntreeF₂_cons h hF₁ hF₂))
    (fi_hbodyD (ntreeF₂_list h hF₁ hF₂) (ntreeF₂_ntree hF₁ hF₂))

end

/-! ## §4 Arity 0: the four families are jointly inhabited with nothing assumed

The form `RecTyped.lean`'s `ntreeAux_recHargs_premises_inhabited` takes for the *non*-bundle
premises, now for the bundles themselves — one block, one `D`, one `R`, one `σ`, one environment,
all four families at every index the closure demands them at, simultaneously. -/

theorem fi_recHargs_bundles_inhabited :
    ∃ (env₁ E₁ E₂ F₁ F₂ : VEnv), VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some E₁ ∧ E₁.addIndCtors ntreeAux = some E₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁ ∧
      F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂ ∧
      (∀ (t : Nat) (T : VIndType), ntreeAux.types[t]? = some T → T.name ∈ ntreeK →
        ntreeRestore.MotiveHargs ntreeAux gS F₂ t T) ∧
      (∀ (q t : Nat) (C : VIndCtor), ntreeAux.ctorsAll[q]? = some (t, C) →
        ntreeRestore.MinorFldDefEq ntreeAux gS F₂ q C) ∧
      (∀ (q t : Nat) (C : VIndCtor) (T : VIndType), ntreeAux.ctorsAll[q]? = some (t, C) →
        ntreeAux.types[t]? = some T → T.name ∈ ntreeK →
        ntreeRestore.MinorCtorHargs ntreeAux gS F₂ q t C) ∧
      (∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → T.name ∈ ntreeK →
        ntreeRestore.RecBodyHargs ntreeAux gS F₂ j T) := by
  obtain ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂⟩ := ntree_stage₂_exists
  exact ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂,
    fi_hmotD (ntreeF₂_list h hF₁ hF₂) (ntreeF₂_ntree hF₁ hF₂),
    fi_hfldD (ntreeF₂_list h hF₁ hF₂) (ntreeF₂_ntree hF₁ hF₂),
    fi_hminD (ntreeF₂_list h hF₁ hF₂) (ntreeF₂_ntree hF₁ hF₂)
      (ntreeF₂_nil h hF₁ hF₂) (ntreeF₂_cons h hF₁ hF₂),
    fi_hbodyD (ntreeF₂_list h hF₁ hF₂) (ntreeF₂_ntree hF₁ hF₂)⟩

/-- …and the same three at `F₃`, the ι-stage environment obligation (C) is stated over.  Kept
separate because `Theory/Inductive/FamInhabC.lean` needs it and because the two environments are
genuinely different: `F₃` carries the *restored recursor* constants and `F₂` does not. -/
theorem fi_recHargs_bundles_inhabited₃ :
    ∃ (env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv), VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some E₁ ∧ E₁.addIndCtors ntreeAux = some E₂ ∧
      E₂.addIndRecs ntreeAux = some E₃ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁ ∧
      F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂ ∧
      F₂.addConstList (ntreeAux.recConstsR ntreeRestore ntreeK) = some F₃ ∧
      (∀ (t : Nat) (T : VIndType), ntreeAux.types[t]? = some T → T.name ∈ ntreeK →
        ntreeRestore.MotiveHargs ntreeAux gS F₃ t T) ∧
      (∀ (q t : Nat) (C : VIndCtor), ntreeAux.ctorsAll[q]? = some (t, C) →
        ntreeRestore.MinorFldDefEq ntreeAux gS F₃ q C) ∧
      (∀ (q t : Nat) (C : VIndCtor) (T : VIndType), ntreeAux.ctorsAll[q]? = some (t, C) →
        ntreeAux.types[t]? = some T → T.name ∈ ntreeK →
        ntreeRestore.MinorCtorHargs ntreeAux gS F₃ q t C) := by
  obtain ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩ := ntree_stage₃_exists
  exact ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃,
    fi_hmotD (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃),
    fi_hfldD (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃),
    fi_hminD (ntreeF₃_list h hF₁ hF₂ hF₃) (ntreeF₃_ntree hF₁ hF₂ hF₃)
      (ntreeF₃_nil h hF₁ hF₂ hF₃) (ntreeF₃_cons h hF₁ hF₂ hF₃)⟩

/-- **Obligation (B), arity 0, through the general bundle closure.** -/
theorem fi_obligationB_inhabited :
    ∃ (env₁ E₁ E₂ F₁ F₂ : VEnv), VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some E₁ ∧ E₁.addIndCtors ntreeAux = some E₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁ ∧
      F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂ ∧
      ∀ c ∈ ntreeAux.recConstsR ntreeRestore ntreeK, VConstant.WF F₂ c.2 := by
  obtain ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂⟩ := ntree_stage₂_exists
  exact ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂,
    fi_ntreeAux_obligationB h hE₁ hE₂ hF₁ hF₂⟩


/-! ## §5 Anti-vacuity, stated apart from hole-freeness

`docs/vacuity-ledger.md` §0: a clean axiom line is not evidence of content, and a *degenerate*
witness must be disclosed as one.  §5a is the block's non-degeneracy, §5b the slots that really
move, §5c the slots that are empty here and why. -/

/-- §5a The block is **parameterised**: `D.np = 1`, so none of this is the `np = 0` case
`VEnv.recConstsR_wf_of_np_zero` already handles. -/
theorem fi_np_pos : 0 < ntreeAux.np := by decide

/-- §5a The `Hargs` bundles are demanded at a **non-empty** set of indices — the companion is in
`K` — so §1 is not discharging a vacuous ∀. -/
theorem fi_companion_in_K : fiT1.name ∈ ntreeK := by decide

/-- §5a …and **not** at every index: the block's own head is off `K`, which is what
`RecTyped.lean`'s `ntree_recTyped_hK_false` refutes the alternative of.  So both branches of the
closure's case split are reached at this one block. -/
theorem fi_own_head_off_K : (ntreeAux.types.getD 0 default).name ∉ ntreeK := by decide

/-- §5b `MotiveHargs`' `hbody` is content: the subject is the **restored** head `List (NTree α)`,
not the stored `_nested.List_1 α`, and the two differ. -/
theorem fi_motBody_ne_stored : ntreeAux.atRec (ntreeRestore.tyBody ntreeAux 1)
    ≠ .app (.const `_nested.List_1 [.param 1]) (.bvar 0) := by decide

/-- §5b The field telescope **moves** at `q = 0` … -/
theorem fi_fld0_moves : liftTele (ntreeAux.nm + 0)
      ((ntreeAux.atRecTele (ntreeNode.fields.map (·.type))).map (VExpr.substC · gS))
    ≠ liftTele (ntreeAux.nm + 0)
      ((ntreeAux.atRecTele (ntreeNode.fieldTypesR ntreeAux ntreeRestore)).map
        (VExpr.substC · gS)) := by decide

/-- §5b … and at `q = 2`, the entry `MinorCtorHargs` is demanded at. -/
theorem fi_fld2_moves : liftTele (ntreeAux.nm + 2)
      ((ntreeAux.atRecTele (nlistCons.fields.map (·.type))).map (VExpr.substC · gS))
    ≠ liftTele (ntreeAux.nm + 2)
      ((ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore)).map
        (VExpr.substC · gS)) := by decide

/-- §5c … and **not** at `q = 1`: `nlistNil` has no fields, so that instance of `MinorFldDefEq` is
`TeleDefEq.nil` and carries nothing.  Disclosed, as `RecTyped.lean`'s `ntree_minorFld_nil` also
discloses it. -/
theorem fi_fld1_trivial : liftTele (ntreeAux.nm + 1)
      ((ntreeAux.atRecTele (nlistNil.fields.map (·.type))).map (VExpr.substC · gS))
    = liftTele (ntreeAux.nm + 1)
      ((ntreeAux.atRecTele (nlistNil.fieldTypesR ntreeAux ntreeRestore)).map
        (VExpr.substC · gS)) := by decide

/-- §5b **The `HasArgs` step at `nlistCons` is a conversion, not a `Lookup`.**  The context declares
the second field at the *stored* type `rV #8`; the telescope `hpi` fixes presents it at
`List (NTree #8)`, and the two are different terms.  This is the slot
`docs/handoff-htele.md` §5.3 found at the ι-context, here at the minor block. -/
theorem fi_hAs_second_needs_beta :
    (.app rV (.bvar 8) : VExpr) ≠ .app (.const ``List [.param 1])
      (.app (.const ``NTree [.param 1]) (.bvar 8)) := by decide

/-- §5b **`hfun`'s type moves too**, at both companion constructors: the minor's motive is looked up
at the stored companion application and `hfun` demands it at the restored one. -/
theorem fi_hfun_cons_type_moves :
    (.forallE (.app rV (.bvar 8)) (.sort (.param 0)) : VExpr)
      ≠ .forallE (.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 8)))
        (.sort (.param 0)) := by decide

theorem fi_hfun_nil_type_moves :
    (.forallE (.app rV (.bvar 3)) (.sort (.param 0)) : VExpr)
      ≠ .forallE (.app (.const ``List [.param 1]) (.app (.const ``NTree [.param 1]) (.bvar 3)))
        (.sort (.param 0)) := by decide

/-- §5b `RecBodyHargs`' head defeq moves; its `hconcl` is free.  Both halves recorded. -/
theorem fi_recBody_head_moves :
    ((ntreeAux.tyApp' 1 (fiT1.indices.length + ntreeAux.nmin + ntreeAux.nm)
        (bvars 0 fiT1.indices.length)).substC gS)
      ≠ (ntreeAux.tyAppR' ntreeRestore 1
        (fiT1.indices.length + ntreeAux.nmin + ntreeAux.nm) (bvars 0 fiT1.indices.length)) := by
  decide

/-- §5c **The degeneracy that bounds this corner, re-measured rather than cited.**  The companion is
unindexed, so `MotiveHargs`' `hAs` window (`bvars 0 T.indices.length`) is **empty** and its `hAs`
is `HasArgs.nil`; `hpi`/`hsort` are the corresponding identities.  Only `hbody` carries content at
this family, and any block with a genuinely *indexed* companion would ask for more. -/
theorem fi_companion_unindexed : fiT1.indices = [] := rfl

theorem fi_motive_window_empty : bvars 0 fiT1.indices.length = [] := rfl

/-- §5c …and `nlistNil`'s field window is empty for the same structural reason, which is why §1c4's
`nlistNil` instance is disclosed as degenerate and `nlistCons`' is the load-bearing one. -/
theorem fi_nil_fields_empty : nlistNil.fields = [] := rfl

theorem fi_cons_fields_two : nlistCons.fields.length = 2 := rfl

/-- §5c And the two `nlistCons` fields are **both recursive**, so the ih block is two entries long
and the `hfun` de Bruijn index is `6`, not `2` — the arithmetic that a field-less witness would
never exercise. -/
theorem fi_cons_ihTypes_two : (ntreeAux.ihTypes 2 nlistCons).length = 2 := rfl

/-! ## §6 Axiom audit — hole-freeness only, stated apart from §5's content claims -/

#print axioms Lean4Lean.InductiveDeclExamples.fi_motiveHargs
#print axioms Lean4Lean.InductiveDeclExamples.fi_minorFld_node
#print axioms Lean4Lean.InductiveDeclExamples.fi_minorFld_cons
#print axioms Lean4Lean.InductiveDeclExamples.fi_hcbody_nil
#print axioms Lean4Lean.InductiveDeclExamples.fi_hcbody_cons
#print axioms Lean4Lean.InductiveDeclExamples.fi_hfun_nil
#print axioms Lean4Lean.InductiveDeclExamples.fi_hfun_cons
#print axioms Lean4Lean.InductiveDeclExamples.fi_hAs_cons
#print axioms Lean4Lean.InductiveDeclExamples.fi_minorCtorHargs_nil
#print axioms Lean4Lean.InductiveDeclExamples.fi_minorCtorHargs_cons
#print axioms Lean4Lean.InductiveDeclExamples.fi_recBodyHargs
#print axioms Lean4Lean.InductiveDeclExamples.fi_hmotD
#print axioms Lean4Lean.InductiveDeclExamples.fi_hfldD
#print axioms Lean4Lean.InductiveDeclExamples.fi_hminD
#print axioms Lean4Lean.InductiveDeclExamples.fi_hbodyD
#print axioms Lean4Lean.InductiveDeclExamples.fi_ntreeAux_obligationB
#print axioms Lean4Lean.InductiveDeclExamples.fi_recHargs_bundles_inhabited
#print axioms Lean4Lean.InductiveDeclExamples.fi_recHargs_bundles_inhabited₃
#print axioms Lean4Lean.InductiveDeclExamples.fi_obligationB_inhabited
#print axioms Lean4Lean.InductiveDeclExamples.fi_hAs_second_needs_beta
#print axioms Lean4Lean.InductiveDeclExamples.fi_fld2_moves

end InductiveDeclExamples
end Lean4Lean
