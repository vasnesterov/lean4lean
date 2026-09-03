import Lean4Lean.Verify.Inductive.ValRestGeneral
import Lean4Lean.Theory.Inductive.CtorBeta

/-!
# The **undecomposed whole-type bridge**, in general

`Verify/Inductive/ValRestGeneral.lean` leaves obligations (B) and (C) of `VEnv.addInductR_ordered'`
standing on three premises whose two sides are `mkPi`s under a `substC` — and, for one of them, under
a level instantiation as well, at a **free** `U`, `Γ` and `ls`:

* `hbridgeD` inside `VIndRestore.csubst_WFD` (§6 there),
* `VIndRestore.CtorTypeBridge` (§4 there),
* `VIndRestore.RecTypeBridge` (§5 there).

Concrete instances exist at `ntreeAux` (`ntree_hbridgeD`, `ntree_ctorTypeBridge`,
`ntree_recTypeBridge`), so the arithmetic demonstrably works at a real parameterised nested block.
This file does the general statements.

## What is proved

* **§A the level/context absorber, and it is an `↔`.**  The free `U`, free `Γ` and free `ls` of
  `hbridgeD` cost **nothing**: `IsDefEq.instL` then `IsDefEq.weak0` turn a bridge at `Γ = []`,
  `U = D.uvars`, *no* `instL` into the free-everything form, and `VExpr.LevelWF.instL_id` turns it
  back.  So free `ls` is **not** the obstacle — `ConstSubstNested.lean` §H.3's
  `rRecConstClause0` already used this two-step route at `ntreeAux`; it was simply never stated in
  general, while `ntree_node_const_defeq` (the *other* concrete instance) instead rebuilds the whole
  defeq by hand at free `U`, which is what does not generalise.
* **§B the whole-type ctor bridge at a DECLARED member, in general.**  `mkPi_congrU` over
  `CtorBeta`'s `substC_fieldTypes_defeq_of_noK` (telescope) and `ctorResult_defeq` (result, free),
  with the `OnCtx` read off the source constant's own `IsType` by `IsType.mkPi_inv`.  The
  *whole* premise is `CtorBeta` §3's `hfld` — one typed defeq per recursive field naming a companion.
* **§C `hbridgeD` in general = (A)'s `hfld`.**  §A ∘ §B.  So §6 of `ValRestGeneral` introduces **no
  new obligation**: its premise is obligation (A)'s per-field datum, absorbed through the level
  quantifier.
* **§D `RecTypeBridge` in general.**  `mkPi_congrU` over `NestedTele.lean` §T15.2's
  `recTypeTele_teleDefEq_of_blocks` and §T15.3's `substC_recBody_defeq`, with `OnCtx` again free from
  `IsType.mkPi_inv`.  This is `recConstsR_wf_of_blocks`' own internals, exposed as the whole-pi defeq
  rather than consumed into a `VConstant.WF`.  Its hypotheses are that theorem's `hM`, `hQ`, `hbody`
  — nothing new, and **no** `T.name ∈ K` needed.
* **§E `CtorTypeBridge` in general, as an `↔` against the symmetric form.**  Its left side is
  *unsubstituted*, so it is not `mkPi_congrU`'s shape until one σ-identity on `C.typeR D R j` is
  supplied; §E states that as an explicit premise and gives the `↔`, then reduces the symmetric form
  to a telescope datum plus a **live** result datum.  At a companion member the result is live
  because `CtorBeta`'s `ctorResult_defeq` needs `T.name ∉ K`; that is content, not slack.
* **§F item (c): the arity-0 witness at `ntreeAux`** (`uvars = 1`,
  `params = [.sort (.succ (.param 0))]`, `recUvars = 2`), existentially closed over the staging, with
  §A, §B and §C *instantiated* — `hbridgeD` at `ntreeAux` obtained **through the general route** and
  not through `ntree_node_const_defeq`.

## What is NOT claimed

Nothing here discharges `CtorBeta`'s `hfld`, or §D's `hM`/`hQ`/`hbody`, or §E's result datum: those
are the β-redex arithmetic the previous rounds already priced, and this file *routes* to them rather
than shrinking them.  Nothing here touches `HargsShared`'s two data.  No frozen file is edited; no
`sorry`; no `VEnv.HasArgs.of_mkApp`; no `PiInv`.

## Item (d): holes

**None.**  `VEnv.IsDefEq.uniq` is not entered: §A's `↔` is between two forms of the *same* defeq, so
the converse direction is `instL_id` and not uniqueness of types.  Where a uniqueness-shaped step
would have been convenient — reading a bridge back off a typing — this file states an implication and
says so at the statement, following `ValRestGeneral.lean` §5's house style.
`VEnv.AxiomConservativityWF` and the restriction cycle are absent.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi)

/-! ## §A The level/context absorber, and it is an `↔`

`hbridgeD`'s shape is "for every `Γ` and every level list `ls` of the right length, a defeq between
the two `instL ls`-instances".  Its content is a **single** defeq at `Γ = []` and at the identity
instantiation.  Both directions are two lines, and neither needs unique typing.

**Why this is stated at all**, given that `ConstSubstNested.lean` §H.3 does it inline twice: because
the *other* concrete instance of the same shape, `InductiveDeclExamples.ntree_node_const_defeq`,
does **not** do it this way — it rebuilds the defeq at free `U` and free `l` from `constDF`/`beta`
— and that route is per-block.  Naming the general route is what stops a successor reaching for the
per-block one. -/

namespace VExpr

/-- **The free-`Γ`/free-`ls` bridge shape, named** — exactly the right disjunct of
`CSubst.WFD.const`, and exactly `csubst_WFD`'s `hbridgeD` at one constructor. -/
def BridgeD (e : VEnv) (n : Nat) (X Y : VExpr) : Prop :=
  ∀ (U : Nat) {Γ : List VExpr} {ls : List VLevel}, (∀ l ∈ ls, l.WF U) → ls.length = n →
    ∃ v, e.IsDefEq U Γ (X.instL ls) (Y.instL ls) (.sort v)

variable {e : VEnv} {n : Nat} {X Y : VExpr}

/-- **Forward: the free `U`, `Γ` and `ls` are free.**  `IsDefEq.instL` then `IsDefEq.weak0`; the
length hypothesis is not even used, which is itself worth recording — `hbridgeD`'s `ls.length = uvars`
is dead weight in this direction. -/
theorem bridgeD_of_bridge (henv : e.Ordered) (h : ∃ v, e.IsDefEq n [] X Y (.sort v)) :
    BridgeD e n X Y := by
  intro U Γ ls hls _
  obtain ⟨v, hv⟩ := h
  exact ⟨_, (hv.instL hls (U' := U) (ls := ls)).weak0 henv⟩

/-- **Backward: the identity instantiation recovers the single defeq.**  `VLevel.params n` is a legal
`ls` (`params_wf`, `params_length`) and `LevelWF.instL_id` makes it the identity on both sides.  So
nothing was lost in the forward direction; in particular this is **not** a uniqueness-of-types step
and does not touch `VEnv.IsDefEq.uniq`. -/
theorem bridge_of_bridgeD (hX : X.LevelWF n) (hY : Y.LevelWF n) (h : BridgeD e n X Y) :
    ∃ v, e.IsDefEq n [] X Y (.sort v) := by
  obtain ⟨v, hv⟩ := h n (ls := VLevel.params n) (Γ := []) VLevel.params_wf VLevel.params_length
  exact ⟨v, hX.instL_id ▸ hY.instL_id ▸ hv⟩

/-- **THE `↔`.**  Under `Ordered` and the two `LevelWF` side conditions — which every stored constant
type satisfies — the free-everything bridge **is** the single bridge at `Γ = []` and `U = n`.

This is the statement that stops the free level context being re-reported as an obstacle. -/
theorem bridgeD_iff (henv : e.Ordered) (hX : X.LevelWF n) (hY : Y.LevelWF n) :
    BridgeD e n X Y ↔ ∃ v, e.IsDefEq n [] X Y (.sort v) :=
  ⟨bridge_of_bridgeD hX hY, bridgeD_of_bridge henv⟩


/-- **…and the `↔` with the `IsType` doing the work on one side.**  `Y`'s `LevelWF` is free from a
typing (`IsDefEq.levelWF` at the empty context), so only the restored side's `LevelWF` is a real side
condition. -/
theorem bridgeD_iff_of_isType (henv : e.Ordered) (hX : X.LevelWF n) (hY : e.IsType n [] Y) :
    BridgeD e n X Y ↔ ∃ v, e.IsDefEq n [] X Y (.sort v) :=
  let ⟨_, hY'⟩ := hY
  bridgeD_iff henv hX (hY'.levelWF trivial).1

end VExpr

/-! ## §B The whole-type bridge at a **declared** member, in general

`CtorBeta.lean` reduced obligation (A) to per-recursive-field data, but it consumed that data into
a `VConstant.WF` (`ctorConstsCR_wf_of_fieldsD`) rather than exposing the whole-pi defeq that
`ValRestGeneral` §6 asks for.  This section exposes it.  There is nothing new in the proof: it is
`mkPi_congrU` over `CtorBeta` §1's telescope and `CtorBeta` §2's result, and the `OnCtx` that
`mkPi_congrU` adds is **free** — `IsType.mkPi_inv` reads it off the same `IsType` §2 already needs.

`hK : T.name ∉ K` is what makes the result conjunct free, exactly as in `CtorBeta` §2, and
`ctorConstsCR` declares constructors only at members off `K`, so it is not a restriction. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {e₁ : VEnv} {U : Nat}
variable {C : VIndCtor} {j : Nat} {T : VIndType}

/-- **THE WHOLE-TYPE CTOR BRIDGE, GENERAL, AT A DECLARED MEMBER.**  Both sides under `substC σ`, at
`Γ = []` and a single `U`.  The only premise beyond `hown` and the source constant's own typing is
`hfld` — `CtorBeta` §3's per-recursive-field datum, *the same list of hypotheses, in the same
contexts*.

So `ValRestGeneral` §6's `hbridgeD` is obligation (A)'s residual and not a second one; §C makes that
precise by absorbing the level quantifier. -/
theorem substC_ctorType_bridge' (hown : R.OwnId D K) (he₁ : e₁.Ordered)
    (hty : e₁.IsType U [] ((C.type D j).substC σ))
    (hfld : ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → ¬ VExpr.NoConsts K F.type →
      ∃ u, e₁.IsDefEq U
        ((((C.fields.map (·.type)).map (VExpr.substC · σ)).take i).reverse
          ++ (C.params.map (VExpr.substC · σ)).reverse)
        (F.type.substC σ) ((R.restore D i F.type).substC σ) (.sort u))
    (hres : ∃ v : VLevel, e₁.IsDefEq U
      (((C.params ++ C.fields.map (·.type)).map (VExpr.substC · σ)).reverse)
      ((C.canonResult D j).substC σ)
      ((D.tyAppR R j C.fields.length C.args).substC σ) (.sort v)) :
    ∃ v, e₁.IsDefEq U [] ((C.typeR D R j).substC σ) ((C.type D j).substC σ) (.sort v) := by
  have htele : e₁.TeleDefEq U [] ((C.params ++ C.fields.map (·.type)).map (VExpr.substC · σ))
      ((C.params ++ C.fieldTypesR D R).map (VExpr.substC · σ)) := by
    rw [List.map_append, List.map_append]
    refine VEnv.TeleDefEq.append VEnv.TeleDefEq.refl (substC_fieldTypes_defeq_of_noK hown ?_)
    intro i F r hF hr hnc
    simpa only [List.append_nil] using hfld i F r hF hr hnc
  have hty' := hty
  rw [VIndCtor.type, VExpr.substC_mkPi] at hty'
  obtain ⟨hOn, -⟩ := VEnv.IsType.mkPi_inv he₁ (Γ := []) ⟨⟩ hty'
  obtain ⟨v, hres⟩ := hres
  obtain ⟨u, h⟩ := VEnv.IsDefEq.mkPi_congrU htele (by simpa using hOn)
    ⟨v, by simpa using hres⟩
  refine ⟨u, ?_⟩
  rw [VIndCtor.type, VIndCtor.typeR, VExpr.substC_mkPi, VExpr.substC_mkPi]
  exact h.symm

/-- **…and at a DECLARED member the result datum is free**, by `CtorBeta` §2.  This is the form §C
consumes: the whole premise is `hfld`. -/
theorem substC_ctorType_bridge (hown : R.OwnId D K) (he₁ : e₁.Ordered)
    (hT : D.types[j]? = some T) (hK : T.name ∉ K)
    (hty : e₁.IsType U [] ((C.type D j).substC σ))
    (hfld : ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → ¬ VExpr.NoConsts K F.type →
      ∃ u, e₁.IsDefEq U
        ((((C.fields.map (·.type)).map (VExpr.substC · σ)).take i).reverse
          ++ (C.params.map (VExpr.substC · σ)).reverse)
        (F.type.substC σ) ((R.restore D i F.type).substC σ) (.sort u)) :
    ∃ v, e₁.IsDefEq U [] ((C.typeR D R j).substC σ) ((C.type D j).substC σ) (.sort v) :=
  substC_ctorType_bridge' hown he₁ hty hfld (ctorResult_defeq hown he₁ hT hK hty)

end
end VIndRestore

/-! ## §C Item (b) in general: `csubst_WFD`'s `hbridgeD` **is** obligation (A)'s `hfld`

§A ∘ §B.  The free `U`, `Γ` and `ls` of `ValRestGeneral` §6's `hbridgeD` cost two lemma applications;
the substance is §B's single defeq; and §B's only premise is `CtorBeta` §3's per-recursive-field
`hfld`.  So **§6 introduces no obligation that (A) did not already carry.**

Note which `CSubst` well-formedness is used: `(R.csubstTy D K).WF`, the *type-constants-only*
substitution, whose `const` bridge is the syntactic equation `substC_tyType_eq` and is therefore
**not** the one `ConstSubstNested.lean` §B refutes at a parameterised block.  The refuted one is
`(R.csubst D K).WF`, and it does not appear here. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {env env₃ e₁ : VEnv}

/-- **`hbridgeD` IN GENERAL, AT EVERY `U`, FROM (A)'s PER-FIELD DATUM.**  Plugs straight into
`VIndRestore.csubst_WFD`'s `hbridgeD` at any fixed `U`: `fun j T C hT hK hC => csubst_hbridgeD … U j T C hT hK hC`.

`hfld` is *character for character* `VEnv.ctorConstsCR_wf_of_fieldsD`'s `hfld`, so a caller that has
discharged obligation (A) through `CtorBeta` has already discharged this. -/
theorem csubst_hbridgeD (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃)
    (henv₃ : env₃.Ordered) (he₁ : e₁.Ordered)
    (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hfld : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → ¬ VExpr.NoConsts K F.type →
        ∃ u : VLevel, e₁.IsDefEq D.uvars
          ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
            ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse)
          (F.type.substC (R.csubstTy D K))
          ((R.restore D i F.type).substC (R.csubstTy D K)) (.sort u)) :
    ∀ (U : Nat) (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors → ∀ {Γ : List VExpr} {ls : List VLevel},
      (∀ l ∈ ls, l.WF U) → ls.length = D.uvars →
      ∃ v, e₁.IsDefEq U Γ (((C.typeR D R j).substC (R.csubstTy D K)).instL ls)
        (((C.type D j).substC (R.csubstTy D K)).instL ls) (.sort v) := by
  intro U j T C hT hK hC Γ ls hls hlen
  refine VExpr.bridgeD_of_bridge he₁ ?_ U hls hlen
  refine substC_ctorType_bridge hown he₁ hT hK ?_ (hfld j T C hT hK hC)
  exact (hD.ctors env₃ h₃ j T hT C hC).constant_wf henv₃ |>.substC hσ

/-- **…and the `↔`, so a successor cannot hand the level quantifier back.**  At one constructor, the
free-everything form is *equivalent* to the single `Γ = []`, `U = D.uvars` defeq, given only that the
restored substituted type has well-formed levels.

**Why this direction of the `↔` is stated at `LevelWF` and not read off a typing** (recorded at the
statement, per house style): reading `((C.typeR D R j).substC σ).LevelWF D.uvars` off a *typing* of
the restored type would need the step's own declaration to be in scope, which is `RestoreStep`'s
business and not this file's; and reading the bridge back off two typings of the same term would be
uniqueness of types, i.e. `VEnv.IsDefEq.uniq`, one of the thirteen holes.  `LevelWF` is the cheap
premise that avoids both. -/
theorem csubst_hbridgeD_iff (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃)
    (henv₃ : env₃.Ordered) (he₁ : e₁.Ordered)
    (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars)
    {j : Nat} {T : VIndType} {C : VIndCtor} (hT : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hlwR : ((C.typeR D R j).substC (R.csubstTy D K)).LevelWF D.uvars) :
    VExpr.BridgeD e₁ D.uvars ((C.typeR D R j).substC (R.csubstTy D K))
        ((C.type D j).substC (R.csubstTy D K))
      ↔ ∃ v, e₁.IsDefEq D.uvars [] ((C.typeR D R j).substC (R.csubstTy D K))
        ((C.type D j).substC (R.csubstTy D K)) (.sort v) :=
  VExpr.bridgeD_iff_of_isType he₁ hlwR
    ((hD.ctors env₃ h₃ j T hT C hC).constant_wf henv₃ |>.substC hσ)

end
end VIndRestore

/-! ## §D `RecTypeBridge` in general

`NestedTele.lean` §T15.2 (`recTypeTele_teleDefEq_of_blocks`) and §T15.3 (`substC_recBody_defeq`)
already supply the recursor telescope's `TeleDefEq` and the body defeq under `substC`, with **no bound
on `D.np`** — but `recConstsR_wf_of_blocks` consumes them into a `VConstant.WF`, so the whole-pi
defeq `ValRestGeneral` §5 wants was never exposed.  It is `mkPi_congrU` over the same two data, with
the `OnCtx` free from `IsType.mkPi_inv`, exactly as `ConstSubstNested.lean` §H.2's `rRecPi0`/`rRecPi1`
do it at `ntreeAux` — this is those two, de-instantiated.

`T.name ∈ K` is **not** needed: the general statement holds at every member, which is why it also
covers `rRecPi0` (a declared member) and not only `rRecPi1` (the companion). -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {σ : CSubst} {e₂ : VEnv} {j : Nat} {T : VIndType}

/-- **THE WHOLE-TYPE RECURSOR BRIDGE, GENERAL.**  `rRecPi0`/`rRecPi1` at a free block.  `hM`, `hQ`
and `hbody` are `VEnv.recConstsR_wf_of_blocks`' own hypotheses, unchanged; `hty` is the source
recursor constant's typing after substitution, which that theorem's `hsrc`/`hσ` already deliver. -/
theorem substC_recType_bridge (he₂ : e₂.Ordered) (hT : D.types[j]? = some T)
    (hty : e₂.IsType D.recUvars [] ((D.recType j).substC σ))
    (hM : e₂.TeleDefEq D.recUvars (((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)
      (D.motives.map (VExpr.substC · σ)) ((D.motivesR R).map (VExpr.substC · σ)))
    (hQ : e₂.TeleDefEq D.recUvars ((D.motives.map (VExpr.substC · σ)).reverse
        ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)
      (D.minors.map (VExpr.substC · σ)) ((D.minorsR R).map (VExpr.substC · σ)))
    (hbody : ∃ v : VLevel, e₂.IsDefEq D.recUvars
      (((D.atRecTele D.params ++ D.motives ++ D.minors ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map (VExpr.substC · σ)).reverse)
      ((VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
            (VExpr.bvars 0 T.indices.length))
          ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
            (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC σ)
      ((VExpr.forallE (D.tyAppR' R j (T.indices.length + D.nmin + D.nm)
            (VExpr.bvars 0 T.indices.length))
          ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
            (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC σ) (.sort v)) :
    ∃ v, e₂.IsDefEq D.recUvars [] ((D.recTypeR R j).substC σ) ((D.recType j).substC σ)
      (.sort v) := by
  have hg : D.types.getD j default = T := VInductDecl'.getD_types hT
  have hrt : (D.recType j).substC σ
      = mkPi ((D.atRecTele D.params ++ D.motives ++ D.minors ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map (VExpr.substC · σ))
        ((VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
            (VExpr.bvars 0 T.indices.length))
          ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
            (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC σ) := by
    simp only [VInductDecl'.recType, hg, VExpr.substC_mkPi]
  have hrtR : (D.recTypeR R j).substC σ
      = mkPi ((D.atRecTele D.params ++ D.motivesR R ++ D.minorsR R ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map (VExpr.substC · σ))
        ((VExpr.forallE (D.tyAppR' R j (T.indices.length + D.nmin + D.nm)
            (VExpr.bvars 0 T.indices.length))
          ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
            (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC σ) := by
    simp only [VInductDecl'.recTypeR, hg, VExpr.substC_mkPi]
  rw [hrt] at hty
  obtain ⟨hOn, -⟩ := VEnv.IsType.mkPi_inv he₂ (Γ := []) ⟨⟩ hty
  obtain ⟨u, h⟩ := VEnv.IsDefEq.mkPi_congrU
    (VInductDecl'.recTypeTele_teleDefEq_of_blocks hM hQ) (by simpa using hOn)
    (by simpa using hbody)
  exact ⟨u, hrt ▸ hrtR ▸ h.symm⟩

/-- **`RecTypeBridge` ITSELF, IN GENERAL** — `ValRestGeneral` §5's premise, discharged down to
`recConstsR_wf_of_blocks`' three data and nothing else.

`hσ` is taken at `CSubst.WFD`, not `CSubst.WF`: `ConstSubstNested.lean` §B refutes
`(R.csubst D K).WF` at every parameterised block, and `WFD` is the weakening that exists for exactly
that reason.  This is the same choice `VEnv.recConstsR_wf_of_substCD'` makes. -/
theorem recTypeBridge_of_blocks {E₂ : VEnv} {K : List Name}
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : (R.csubst D K).WFD E₂ e₂ D.recUvars) (he₂ : e₂.Ordered)
    (hM : e₂.TeleDefEq D.recUvars
      (((D.atRecTele D.params).map (VExpr.substC · (R.csubst D K))).reverse)
      (D.motives.map (VExpr.substC · (R.csubst D K)))
      ((D.motivesR R).map (VExpr.substC · (R.csubst D K))))
    (hQ : e₂.TeleDefEq D.recUvars
      ((D.motives.map (VExpr.substC · (R.csubst D K))).reverse
        ++ ((D.atRecTele D.params).map (VExpr.substC · (R.csubst D K))).reverse)
      (D.minors.map (VExpr.substC · (R.csubst D K)))
      ((D.minorsR R).map (VExpr.substC · (R.csubst D K))))
    (hbody : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → ∃ v : VLevel,
      e₂.IsDefEq D.recUvars
        (((D.atRecTele D.params ++ D.motives ++ D.minors ++
            VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
            (VExpr.substC · (R.csubst D K))).reverse)
        ((VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
              (VExpr.bvars 0 T.indices.length))
            ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
              (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC (R.csubst D K))
        ((VExpr.forallE (D.tyAppR' R j (T.indices.length + D.nmin + D.nm)
              (VExpr.bvars 0 T.indices.length))
            ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
              (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC (R.csubst D K)) (.sort v)) :
    R.RecTypeBridge D K e₂ := by
  intro j T hT _
  refine substC_recType_bridge he₂ hT ?_ hM hQ (hbody j T hT)
  exact (hsrc (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩)
    (by simp only [VInductDecl'.recConsts, List.mem_map]
        exact ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hT, rfl⟩)).substCD hσ

end
end VIndRestore

/-! ## §E `CtorTypeBridge` in general — the asymmetry, named, and an `↔` that isolates it

`ValRestGeneral` §4's `CtorTypeBridge` is **not** the symmetric shape §B handles: its left side is the
*unsubstituted* `C.typeR D R j`, against `(C.type D j).substC (R.csubst D K)` on the right.  So its
telescope is `C.params ++ C.fieldTypesR D R` against `(C.params ++ fields).map (substC · σ)`, which is
a different pair from `CtorBeta` §1's (that one has **both** sides under `substC`).

Closing the difference is exactly one σ-identity per companion constructor,
`(C.typeR D R j).substC (R.csubst D K) = C.typeR D R j`.  §E.1 states the `↔` it buys; §E.2 then
reduces the symmetric form at a **companion** member to `hfld` plus a *live* result datum.

**Why the result datum is live here and free in §B, and it is content rather than slack.**
`CtorBeta` §2's `ctorResult_defeq` discharges the result conjunct using `hK : T.name ∉ K` — at a
declared member the restored head *is* the block's own head (`OwnId.tyAppR_eq`).  At a companion member
`T.name ∈ K` and the head genuinely moves: at `ntreeAux` this is the β-step
`_nested.List_1 α ↝ ntreeVal α` that `ntree_ctorTypeBridge_nil` performs.  So §E cannot be made to
look like §B, and a successor should not try. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {env env₃ e₁ F : VEnv}

/-- **§E.1 THE `↔`.**  Given the σ-identity on the restored companion constructor types,
`CtorTypeBridge` *is* the symmetric (both-sides-substituted) whole-type bridge — the shape §B, §C and
§D all speak.  Nothing else separates them, and both directions are `rw`. -/
theorem ctorTypeBridge_iff_substC
    (hnoc : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      (C.typeR D R j).substC (R.csubst D K) = C.typeR D R j) :
    R.CtorTypeBridge D K F ↔
      ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
        ∃ v, F.IsDefEq D.uvars [] ((C.typeR D R j).substC (R.csubst D K))
          ((C.type D j).substC (R.csubst D K)) (.sort v) := by
  constructor
  · intro h j T hT hK C hC
    rw [hnoc j T hT hK C hC]; exact h j T hT hK C hC
  · intro h j T hT hK C hC
    rw [← hnoc j T hT hK C hC]; exact h j T hT hK C hC

/-- **§E.2 `CtorTypeBridge` FROM THE PER-FIELD DATUM AND THE COMPANION RESULT DATUM.**  §E.1
composed with §B's primitive.  `hres` is the residue that (A) does not have: one result-head defeq per
companion constructor. -/
theorem ctorTypeBridge_of_entries (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃)
    (henv₃ : env₃.Ordered) (he₁ : e₁.Ordered)
    (hσ : (R.csubst D K).WFD env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hnoc : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      (C.typeR D R j).substC (R.csubst D K) = C.typeR D R j)
    (hfld : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → ¬ VExpr.NoConsts K F.type →
        ∃ u : VLevel, e₁.IsDefEq D.uvars
          ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubst D K))).take i).reverse
            ++ (C.params.map (VExpr.substC · (R.csubst D K))).reverse)
          (F.type.substC (R.csubst D K))
          ((R.restore D i F.type).substC (R.csubst D K)) (.sort u))
    (hres : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      ∃ v : VLevel, e₁.IsDefEq D.uvars
        (((C.params ++ C.fields.map (·.type)).map (VExpr.substC · (R.csubst D K))).reverse)
        ((C.canonResult D j).substC (R.csubst D K))
        ((D.tyAppR R j C.fields.length C.args).substC (R.csubst D K)) (.sort v)) :
    R.CtorTypeBridge D K e₁ :=
  (ctorTypeBridge_iff_substC hnoc).2 fun j T hT hK C hC =>
    substC_ctorType_bridge' hown he₁
      ((hD.ctors env₃ h₃ j T hT C hC).constant_wf henv₃ |>.substCD hσ)
      (hfld j T hT hK C hC) (hres j T hT hK C hC)

end
end VIndRestore

/-! ## §F Item (c): the arity-0 witness at `ntreeAux`

`ntreeAux` — `NTree α` with a `List (NTree α)` field, `uvars = 1`,
`params = [.sort (.succ (.param 0))]`, `recUvars = 2`, the block Lean's own kernel runs the nested
elimination on.  Deliberately **not** `nfnAux`, whose `uvars = 0` and `params = []` would make the
level instantiation invisible (§A would be vacuous: `ls = []`) and the parameter telescope empty.

What is exhibited, and it is the point of the round: `hbridgeD` at `ntreeAux` **through §A ∘ §B ∘ §C**,
i.e. from obligation (A)'s per-field β-step alone, rather than through
`InductiveDeclExamples.ntree_node_const_defeq`'s hand-built free-`U` defeq.  Both routes reach the same
statement; only this one is general.

Everything is existentially closed over the declaration history, so the witness has **arity 0** and no
hypothesis of §A/§B/§C is left unshown-satisfiable.  No `VEnv.HasArgs.of_mkApp`; no `PiInv`. -/

namespace InductiveDeclExamples

/-- §A is **non-vacuous at a positive `uvars`**: `ntreeAux.uvars = 1`, so the `ls` §A quantifies over
is a one-element list and the instantiation is real, not the empty rewrite `nfnAux` would give. -/
theorem ntreeAux_uvars_pos : 0 < ntreeAux.uvars := Nat.zero_lt_one

/-- …and `recUvars ≠ uvars` at this block, which is the mixed instantiation §6 of
`ValRestGeneral.lean` warned about: `hbridgeD` is consumed at `U = 2` with `ls.length = 1`. -/
theorem ntreeAux_recUvars_ne_uvars : ntreeAux.recUvars ≠ ntreeAux.uvars := by decide

/-- **THE WITNESS, ARITY 0.**  At `ntreeAux`, existentially closed over the three staging
environments:

* the staging itself (`addInduct' listDecl`, `addIndTypes`, `addConstList (typeConstsC K)`);
* **§B's whole-type ctor bridge** at the one declared constructor `NTree.node`, at `Γ = []` and
  `U = uvars = 1`, obtained from obligation (A)'s single β-step;
* **§C's `hbridgeD`** — the free-`U`/`Γ`/`ls` form — at every `U`, and in particular the instance
  `csubst_WFD` consumes, `U = recUvars = 2` with `ls.length = uvars = 1`;
* **§A's `↔`** at those two, so the equivalence is exhibited and not merely stated. -/
theorem ntreeAux_wholeTypeBridge_witness :
    ∃ (env₁ env₂ env₃ : VEnv),
      VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ ∧
      (∃ v, env₃.IsDefEq 1 []
        ((ntreeNode.typeR ntreeAux ntreeRestore 0).substC
          (ntreeRestore.csubstTy ntreeAux ntreeK))
        ((ntreeNode.type ntreeAux 0).substC (ntreeRestore.csubstTy ntreeAux ntreeK))
        (.sort v)) ∧
      (∀ (U : Nat) (j : Nat) (T : VIndType) (C : VIndCtor), ntreeAux.types[j]? = some T →
        T.name ∉ ntreeK → C ∈ T.ctors → ∀ {Γ : List VExpr} {ls : List VLevel},
        (∀ l ∈ ls, l.WF U) → ls.length = ntreeAux.uvars →
        ∃ v, env₃.IsDefEq U Γ
          (((C.typeR ntreeAux ntreeRestore j).substC
            (ntreeRestore.csubstTy ntreeAux ntreeK)).instL ls)
          (((C.type ntreeAux j).substC (ntreeRestore.csubstTy ntreeAux ntreeK)).instL ls)
          (.sort v)) ∧
      (∀ (Γ : List VExpr) (ls : List VLevel), (∀ l ∈ ls, l.WF ntreeAux.recUvars) →
        ls.length = ntreeAux.uvars →
        ∃ v, env₃.IsDefEq ntreeAux.recUvars Γ
          (((ntreeNode.typeR ntreeAux ntreeRestore 0).substC
            (ntreeRestore.csubstTy ntreeAux ntreeK)).instL ls)
          (((ntreeNode.type ntreeAux 0).substC
            (ntreeRestore.csubstTy ntreeAux ntreeK)).instL ls) (.sort v)) := by
  obtain ⟨env₁, h⟩ : ∃ e, VEnv.empty.addInduct' listDecl = some e := ⟨_, rfl⟩
  have henv₁ : env₁.Ordered := listEnv_ordered h
  have hfresh : ∀ n ∈ [``NTree, `_nested.List_1, ``NTree.node,
      `_nested.List_1.nil, `_nested.List_1.cons], env₁.constants n = none := by
    intro n hn
    rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
    rfl
  obtain ⟨env₂, h₂⟩ : ∃ e, env₁.addIndTypes ntreeAux = some e :=
    VEnv.addConstList_eq_some_iff.2
      ⟨fun n hn => hfresh n (by revert hn; revert n; decide), by decide⟩
  obtain ⟨env₃, h₃⟩ : ∃ e, env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some e :=
    VEnv.addConstList_eq_some_iff.2
      ⟨fun n hn => hfresh n (by revert hn; revert n; decide), by decide⟩
  have henv₂ : env₂.Ordered := VInductDecl'.addIndTypes_ordered henv₁ ntreeAux_WF' h₂
  have henv₃ : env₃.Ordered :=
    VEnv.addConstList_ordered henv₁ (VEnv.addInductR_typeConstsC_wf ntreeAux_WF') h₃
  have hL := list_const₃ h h₃
  have hN := ntree_const₃ h₃
  have hσ : (ntreeRestore.csubstTy ntreeAux ntreeK).WF env₂ env₃ ntreeAux.uvars :=
    ntree_csubstTy ▸ ntreeSubst_WF h henv₁ h₂ h₃
  -- obligation (A)'s per-field datum at `ntreeAux`: one `.beta`, at the second field of `NTree.node`
  have hfld : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), ntreeAux.types[j]? = some T →
      T.name ∉ ntreeK → C ∈ T.ctors →
      ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → ¬ VExpr.NoConsts ntreeK F.type →
        ∃ u : VLevel, env₃.IsDefEq ntreeAux.uvars
          ((((C.fields.map (·.type)).map
              (VExpr.substC · (ntreeRestore.csubstTy ntreeAux ntreeK))).take i).reverse
            ++ (C.params.map (VExpr.substC · (ntreeRestore.csubstTy ntreeAux ntreeK))).reverse)
          (F.type.substC (ntreeRestore.csubstTy ntreeAux ntreeK))
          ((ntreeRestore.restore ntreeAux i F.type).substC
            (ntreeRestore.csubstTy ntreeAux ntreeK)) (.sort u) := by
    rintro j T C hT hK hC i F r hF hr hnc
    match j, hT with
    | 0, hT =>
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      match i, hF with
      | 0, hF => cases hF; exact absurd hr nofun
      | 1, hF =>
        cases hF
        refine ⟨.succ (.param 0), ?_⟩
        rw [ntree_csubstTy]
        refine VEnv.IsDefEq.beta (A := .sort (.succ (.param 0)))
          (B := .sort (.succ (.param 0))) ?_ ?_ <;> type_tac
      | (_ + 2), hF => simp [ntreeNode] at hF
    | 1, hT => cases hT; exact absurd (by decide) hK
    | (_ + 2), hT => simp [ntreeAux] at hT
  have hnode : ntreeNode ∈ (ntreeAux.types.getD 0 default).ctors := by
    show ntreeNode ∈ [ntreeNode]; exact List.mem_cons_self
  have hbridge := VIndRestore.substC_ctorType_bridge ntreeRestore_ownId henv₃
    (T := ntreeAux.types.getD 0 default) (C := ntreeNode) (j := 0) rfl (by decide)
    ((ntreeAux_WF'.ctors env₂ h₂ 0 _ rfl ntreeNode hnode).constant_wf henv₂ |>.substC hσ)
    (hfld 0 _ ntreeNode rfl (by decide) hnode)
  have hD := VIndRestore.csubst_hbridgeD ntreeAux_WF' h₂ henv₂ henv₃ hσ ntreeRestore_ownId hfld
  exact ⟨env₁, env₂, env₃, h, h₂, h₃, hbridge, hD,
    fun Γ ls hls hlen => hD ntreeAux.recUvars 0 _ ntreeNode rfl (by decide) hnode hls hlen⟩

/-! ### §F.1 Anti-vacuity for §E: its σ-identity premise holds at `ntreeAux`, by computation

"Instantiate, don't admire".  §E's `hnoc` is the one thing separating `CtorTypeBridge` from the
symmetric shape, and it is *decidable* at a block: at `ntreeAux` the restored companion constructor
types are literally `csubst`-free, so `hnoc` is `decide`.  With it, §E.1's `↔` transports the existing
`InductiveDeclExamples.ntree_ctorTypeBridge` into the symmetric form, which is what §B/§C/§D speak —
so both sides of the `↔` are exhibited inhabited at a parameterised nested block. -/

/-- §E's σ-identity at `ntreeAux`: the restored companion constructor types are `csubst`-free. -/
theorem ntree_typeR_noCSubst : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T →
    T.name ∈ ntreeK → ∀ C ∈ T.ctors,
    (C.typeR ntreeAux ntreeRestore j).substC (ntreeRestore.csubst ntreeAux ntreeK)
      = C.typeR ntreeAux ntreeRestore j := by
  intro j T hT hK C hC
  match j, hT with
  | 0, hT => cases hT; exact absurd hK (by decide)
  | 1, hT =>
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain rfl | rfl := hC
    · decide
    · decide
  | (_ + 2), hT => simp [ntreeAux] at hT

section
variable {F : VEnv}
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)

include hL hN in
/-- **§E.1's `↔`, both sides inhabited at `ntreeAux`.**  The right-hand (symmetric) side, from
`ntree_ctorTypeBridge` through the `↔`. -/
theorem ntree_ctorTypeBridge_substC :
    ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → T.name ∈ ntreeK → ∀ C ∈ T.ctors,
      ∃ v, F.IsDefEq 1 []
        ((C.typeR ntreeAux ntreeRestore j).substC (ntreeRestore.csubst ntreeAux ntreeK))
        ((C.type ntreeAux j).substC (ntreeRestore.csubst ntreeAux ntreeK)) (.sort v) :=
  (VIndRestore.ctorTypeBridge_iff_substC ntree_typeR_noCSubst).1 (ntree_ctorTypeBridge hL hN)

end

end InductiveDeclExamples

end Lean4Lean

/-! ## §G What remains, and item (d)

After this file, the three whole-type consumers of `ValRestGeneral.lean` stand as follows at a
**parameterised** nested block.

| premise | general form | what is left |
|---|---|---|
| `hbridgeD` (§6 there) | §C `csubst_hbridgeD` | **nothing new** — it is obligation (A)'s `hfld` (`CtorBeta` §3), absorbed through §A |
| `RecTypeBridge` (§5 there) | §D `recTypeBridge_of_blocks` | `recConstsR_wf_of_blocks`' own `hM`, `hQ`, `hbody` — data (B) already carries |
| `CtorTypeBridge` (§4 there) | §E `ctorTypeBridge_of_entries` | `hfld` at the *companion* constructors, one σ-identity (`hnoc`, `decide`-able per block), and one **live** result-head defeq per companion constructor |

> **The free level context was not the obstacle.**  §A shows the free `U`, `Γ` and `ls` of `hbridgeD`
> cost two lemma applications and are recoverable (`↔`).  What is irreducible is the *single* defeq at
> `Γ = []`, and for the declared constructors that defeq is (A)'s per-field β-step — so §6 of
> `ValRestGeneral.lean` never introduced a second obligation.  What §E isolates is genuinely new
> relative to (A): the **result head** moves at a companion member, because `CtorBeta` §2's discharge of
> the result conjunct needs `T.name ∉ K`.

**Item (d): which of the project's thirteen holes this routes through — NONE.**  Measured with
`scripts/exists.lean` over the whole built population, not asserted.  Two were specifically at risk:

* **`VEnv.IsDefEq.uniq`** (unique typing).  It would be the natural route to §A's backward direction
  *if* one tried to read the bridge off two typings of the same term.  §A instead goes through
  `VExpr.LevelWF.instL_id` at `VLevel.params n`, which is syntactic, and §C's `↔` therefore carries a
  `LevelWF` premise rather than a typing.  **Recorded at `csubst_hbridgeD_iff` itself** so a successor
  does not "improve" the premise into the hole.
* **`VEnv.AxiomConservativityWF` / the restriction cycle.**  Absent; nothing here enters
  `RestrictStep`.

## §H Axiom audit, per declaration -/

#print axioms Lean4Lean.VExpr.BridgeD
#print axioms Lean4Lean.VExpr.bridgeD_of_bridge
#print axioms Lean4Lean.VExpr.bridge_of_bridgeD
#print axioms Lean4Lean.VExpr.bridgeD_iff
#print axioms Lean4Lean.VExpr.bridgeD_iff_of_isType
#print axioms Lean4Lean.VIndRestore.substC_ctorType_bridge'
#print axioms Lean4Lean.VIndRestore.substC_ctorType_bridge
#print axioms Lean4Lean.VIndRestore.csubst_hbridgeD
#print axioms Lean4Lean.VIndRestore.csubst_hbridgeD_iff
#print axioms Lean4Lean.VIndRestore.substC_recType_bridge
#print axioms Lean4Lean.VIndRestore.recTypeBridge_of_blocks
#print axioms Lean4Lean.VIndRestore.ctorTypeBridge_iff_substC
#print axioms Lean4Lean.VIndRestore.ctorTypeBridge_of_entries
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_uvars_pos
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_recUvars_ne_uvars
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_wholeTypeBridge_witness
#print axioms Lean4Lean.InductiveDeclExamples.ntree_typeR_noCSubst
#print axioms Lean4Lean.InductiveDeclExamples.ntree_ctorTypeBridge_substC
