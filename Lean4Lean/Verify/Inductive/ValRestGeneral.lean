import Lean4Lean.Verify.Inductive.FlipGeneral
import Lean4Lean.Theory.Inductive.HargsShared

/-!
# `ValRestC` in general: the two halves, the `↔`, and what each one really costs

`Verify/Inductive/FlipGeneral.lean` §2a named the residue of obligations (B) and (C) of
`VEnv.addInductR_ordered'` as

    `csubst`'s `val` clause  =  (the strengthening family's type-constant node)  ∧  `ValRestC`

and left `VIndRestore.ValRestC` — the *value typings for the companion members' constructors and
recursor* — as the missing piece.  This file settles it.

## What is proved

* **§1 the split, as an `↔`.**  `ValRestC` is *exactly* `ValRestCtor ∧ ValRestRec` — the
  companion constructors' half and the companion recursor's half — under nothing but the two
  nodup side conditions any addable block already satisfies.  No successor can hand the problem
  back: the `↔` pins the decomposition.
* **§2 the recursor half is already FREE at the pair obligation (B) uses.**  `ValRestRec` at
  `(E₂, F)` holds for *every* `F`, because `E₂ = E₁.addIndCtors D` has not declared
  `mkRecName T.name` yet and `val` is guarded by a source lookup.  So at the ctor stage
  `ValRestC ↔ ValRestCtor`, an `↔` again.  This half of the brief's residue was in fact
  **already in the tree** — `VIndRestore.csubst_val_cases` (`Theory/Inductive/NestedRules.lean`
  §8.5) discharges it inline — which §0 of `docs/handoff-valrestgeneral.md` records.
* **§3 the constructor half, in general, from the specification clause that already exists.**
  `VIndRestore.ctorVal_hasType_of_faithful` is the exact mirror of §8.7's
  `tyVal_hasType_of_faithful` at `Faithful.ctor_agree` instead of `ty_agree`, and it needs
  **one** datum: `HargsShared`'s `hargs` at the *constructor* head (which `HargsShared` §6
  already measured as the second of its two data).  Its `hsplit` is dropped outright:
  `VIndRestore.hsplit_free` makes it free.  So `ValRestC` needs **no new spec clause**.
* **§4 the type bridge, and the second `↔`.**  What separates
  `HasType … (R.ctorVal D j C) (C.typeR D R j)` — what §3 delivers — from `ValRestCtor`'s
  `HasType … (R.ctorVal D j C) ((C.type D j).substC (R.csubst D K))` is one defeq per companion
  constructor between the *restored* and the *substituted stored* constructor type.  That is the
  **same β-redex arithmetic as obligation (A)'s `hbridge`**, at the companion members instead of
  the declared ones.  Given the bridge the two are equivalent (`↔`).
* **§5 the recursor half at the pair obligation (C) uses.**  Live there, and it reduces to the
  **undecomposed form of (B)'s own `hbridge`**: one defeq between `(D.recType j).substC` and
  `(D.recTypeR R j).substC`.  So (C)'s extra residue over (B) is a datum (B) already carries.
* **§6 item (b): `WFD.const`'s defeq disjunct at every declared constructor, in general.**
  `VIndRestore.csubst_WFD_const` is `csubst_WF_const` with the bridge weakened from a syntactic
  **equation** to a `IsDefEq` — which is the whole point of `CSubst.WFD` over `CSubst.WF` — and
  it fires at the two non-constructor branches with the *same* proofs, so the disjunct is used
  in exactly one place.  Composed with §1–§5 this leaves obligations (B) and (C) standing on
  β-redex arithmetic alone.
* **§7 item (c): the arity-0 witness at `ntreeAux`**, `uvars = 1`,
  `params = [.sort (.succ (.param 0))]`, at both staging pairs, existentially closed, with the
  constructor half NON-vacuous (two live entries) and the recursor half live at `(E₃, F₃)`.

## What is NOT claimed

Nothing here produces `HargsShared`'s constructor-head `hargs` in general; §3 consumes it.
`HargsShared` §6 already measured that datum as irreducibly distinct from the type head's
(F3), and this file does not narrow that.  Nothing here touches the `ValAt` monotonicity step
between the type stage and the ctor stage (`FlipGeneral.lean` §2a caveat (i)).  No frozen file is
edited; no `sorry`; no `VEnv.HasArgs.of_mkApp` and no `PiInv` anywhere.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars instAll splitPis)

namespace VIndRestore

variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {E F : VEnv}

/-! ## §1 The split, as an `↔`

`ValRestC` quantifies over the names `csubst` has and `csubstTy` does not.  `csubst_dom` says
that domain is three kinds and `csubstTy_dom` says the first kind is precisely `csubstTy`'s, so
the guard `R.csubstTy D K c = none` selects kinds 2 and 3 and nothing else.  `FlipGeneral.lean`
§2 proved the two inclusions; here they become an equivalence with the two halves named. -/

/-- The **companion constructors'** half of `ValRestC`. -/
def ValRestCtor (R : VIndRestore) (D : VInductDecl') (K : List Name) (E F : VEnv) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
    ∀ ci : VConstant, E.constants C.name = some ci →
      F.HasType ci.uvars [] (R.ctorVal D j C) (ci.type.substC (R.csubst D K))

/-- The **companion recursor's** half of `ValRestC`. -/
def ValRestRec (R : VIndRestore) (D : VInductDecl') (K : List Name) (E F : VEnv) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ ci : VConstant, E.constants (Lean.mkRecName T.name) = some ci →
      F.HasType ci.uvars [] (R.recVal D (Lean.mkRecName T.name))
        (ci.type.substC (R.csubst D K))

/-- **THE SPLIT, AND IT IS AN EQUIVALENCE.**  Both side conditions are already required of any
addable block: `D.allNames.Nodup` by `VEnv.addConstList D.allConsts`, `D.blockNames.Nodup` by
`addIndTypes`' success, and `R.DomNodup D K` is the substitution's own key-nodup.

The `↔` is the point: a successor cannot re-open `ValRestC` as something larger than these two
halves, and cannot claim either half is not needed. -/
theorem valRestC_iff (hnd0 : D.allNames.Nodup) (hnd : R.DomNodup D K)
    (hbn : D.blockNames.Nodup) :
    R.ValRestC D K E F ↔ (R.ValRestCtor D K E F ∧ R.ValRestRec D K E F) := by
  refine ⟨fun h => ⟨fun j T hT hK C hC ci hc => ?_, fun j T hT hK ci hc => ?_⟩, ?_⟩
  · obtain ⟨hd, hs⟩ := csubst_ctor_off_csubstTy hnd0 hnd hT hK hC
    exact h hd hs hc
  · obtain ⟨hd, hs⟩ := csubst_rec_off_csubstTy hnd0 hnd hT hK
    exact h hd hs hc
  · rintro ⟨hctor, hrec⟩ c t ci hd hs hc
    obtain ⟨j, T, hT, hK, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨C, hC, rfl, rfl⟩⟩ := csubst_dom hs
    · rw [csubstTy_eq_some hbn hT hK] at hd; exact absurd hd nofun
    · exact hrec j T hT hK ci hc
    · exact hctor j T hT hK C hC ci hc

/-! ## §2 The recursor half is FREE at the ctor stage — obligation (B)'s residue shrinks

`CSubst.WFD.val` is guarded by `env₀.constants c = some ci`, and at
`E₂ = (env.addIndTypes D).addIndCtors D` the companion recursor's name is **not yet declared**:
`addIndRecs` is the layer that declares it, and its success is exactly the freshness of those
names in `E₂`.  So `ValRestRec` at `(E₂, F)` holds for *every* target `F`, with no typing content
at all.

This is not a vacuity defect in the sense of `docs/vacuity-ledger.md` §0: the *other* half of
`ValRestC` is live at the same pair, with two entries at `ntreeAux` (§7), so `ValRestC` itself is
not vacuous there.  What is vacuous is one of its two halves, at one of the two stages, for a
structural reason — and it is exactly the reason `NestedRules.lean` §8.5 gives. -/

/-- `ValRestRec` from freshness of the companion recursor names in the source environment. -/
theorem valRestRec_of_fresh
    (hfr : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      E.constants (Lean.mkRecName T.name) = none) : R.ValRestRec D K E F := by
  intro j T hT hK ci hc
  rw [hfr j T hT hK] at hc; exact absurd hc nofun

/-- **…AND THE STAGING SUPPLIES THAT FRESHNESS.**  `E₃`'s existence is what any run of the block
already has, so this costs the caller nothing beyond the staging it holds anyway. -/
theorem valRestRec_ctorStage {E₂ E₃ : VEnv} (h₃ : E₂.addIndRecs D = some E₃) :
    R.ValRestRec D K E₂ F :=
  valRestRec_of_fresh fun j T hT _ =>
    (VEnv.addConstList_fresh h₃).1 (Lean.mkRecName T.name)
      (by rw [D.recConsts_names]; exact List.mem_map.2 ⟨_, List.mem_of_getElem? hT, rfl⟩)

/-- **OBLIGATION (B)'s RESIDUE, EXACTLY.**  At the ctor-stage pair, `ValRestC` *is* its
constructor half — an `↔`, so this is a complete account and not a sufficient condition. -/
theorem valRestC_iff_ctorStage (hnd0 : D.allNames.Nodup) (hnd : R.DomNodup D K)
    (hbn : D.blockNames.Nodup) {E₂ E₃ : VEnv} (h₃ : E₂.addIndRecs D = some E₃) :
    R.ValRestC D K E₂ F ↔ R.ValRestCtor D K E₂ F :=
  (valRestC_iff hnd0 hnd hbn).trans
    ⟨And.left, fun h => ⟨h, valRestRec_ctorStage h₃⟩⟩

/-! ## §3 The constructor half, in general — and the spec clause for it already exists

`VIndRestore.Faithful.ctor_agree` (`Theory/Inductive/Restore.lean`) says: the presented
constructor `R.ctorName C.name` is a **declared constant** of the pre-block environment whose
stored type, instantiated at the presented levels and spine and re-abstracted over the block's
parameters, is the companion constructor's *restored* type `C.typeR D R j`.  That is a syntactic
equation; the `val` clause wants a typing derivation.  `tyVal_hasType_of_faithful`
(`Theory/Inductive/NestedRules.lean` §8.7) closes that gap for the **type** constant; this is the
same three steps at `ctor_agree`.

Two things are better here than in §8.7's statement.  `hsplit` is **gone** — `hsplit_free`
(`Theory/Inductive/HargsShared.lean` §2) makes it free at every head, `ci` and `np`, so it was
never data.  And the remaining datum is exactly `HargsShared`'s **constructor-head** `hargs`,
which that file's §6 already isolated and measured as genuinely distinct from the type head's
(F3): so this consumes a datum the tree has already named, and introduces none. -/

/-- **THE CONSTRUCTOR HALF's TYPING, AT THE RESTORED TYPE.**  The mirror of
`VIndRestore.tyVal_hasType_of_faithful` at `Faithful.ctor_agree`, with `hsplit` dropped. -/
theorem ctorVal_hasType_of_faithful {npJ : Nat → Nat} {env : VEnv}
    (hfa : R.Faithful D env K npJ) (hle : env ≤ F)
    (hparams : OnCtx D.params.reverse (F.IsType D.uvars))
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    {C : VIndCtor} (hC : C ∈ T.ctors)
    (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars)
    (hargs : ∀ ci : VConstant, env.constants (R.ctorName C.name) = some ci →
      F.HasArgs D.uvars D.params.reverse (R.declTele ci (npJ j) j) (R.tyArgs j)) :
    F.HasType D.uvars [] (R.ctorVal D j C) (C.typeR D R j) := by
  obtain ⟨ci, hci, huv, heq⟩ := hfa.ctor_agree j T hT hK C hC
  rw [← heq, VIndRestore.instAt, ctorVal]
  refine VEnv.HasType.mkLams (by simpa using hparams) ?_
  rw [List.append_nil]
  have hconst : F.HasType D.uvars D.params.reverse
      (.const (R.ctorName C.name) (R.tyLvls j)) (ci.type.instL (R.tyLvls j)) :=
    VEnv.HasType.const (hle.constants hci) hlvl huv.symm
  rw [hsplit_free R ci (npJ j) j] at hconst
  exact VEnv.HasType.mkApp' (hargs ci hci) hconst

/-! ## §4 From the restored type to `ValRestCtor`: one bridge, and the second `↔`

§3 types `R.ctorVal D j C` at `C.typeR D R j`; `ValRestCtor` wants it at
`(C.type D j).substC (R.csubst D K)`.  The difference between those two expressions is exactly
what obligation (A)'s `hbridge` is about at a *declared* constructor — the restoration's
`mkLams D.params` head becoming a saturated β-redex under `substC`
(`VIndRestore.substC_tyApp_defeq_tyAppR_comp`, `NestedRules.lean` §8.8) — evaluated at the
*companion* constructors instead.  So the two residues are one phenomenon at two families of
constructor, which is the sharpest thing this round has to say about (B)/(C). -/

/-- **THE BRIDGE.**  One defeq per companion constructor, between the restored constructor type
and the substituted stored one. -/
def CtorTypeBridge (R : VIndRestore) (D : VInductDecl') (K : List Name) (F : VEnv) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
    ∃ v, F.IsDefEq D.uvars [] (C.typeR D R j)
      ((C.type D j).substC (R.csubst D K)) (.sort v)

/-- The companion constructors' stored constants, at the ctor stage. -/
theorem ctorConst_ctorStage {E₁ E₂ : VEnv} (h₂ : E₁.addIndCtors D = some E₂)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors) :
    E₂.constants C.name = some ⟨D.uvars, C.type D j⟩ :=
  VEnv.addConstList_constants h₂ (C.name, ⟨D.uvars, C.type D j⟩)
    (by rw [VInductDecl'.ctorConsts, List.mem_map]
        exact ⟨(j, C), VInductDecl'.mem_ctorsAll_of hT hC, rfl⟩)

/-- **THE SECOND `↔`.**  Given the bridge, `ValRestCtor` at the ctor stage *is* the restored-type
typing §3 delivers.  Both directions are one `IsDefEq.defeq`, so nothing is lost either way and a
successor cannot claim the reduction was only sufficient. -/
theorem valRestCtor_iff_ctorTyped
    (hE : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      E.constants C.name = some ⟨D.uvars, C.type D j⟩)
    (hbr : R.CtorTypeBridge D K F) :
    R.ValRestCtor D K E F ↔
      ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
        F.HasType D.uvars [] (R.ctorVal D j C) (C.typeR D R j) := by
  constructor
  · intro h j T hT hK C hC
    obtain ⟨v, hv⟩ := hbr j T hT hK C hC
    exact hv.defeq' (h j T hT hK C hC _ (hE j T hT hK C hC))
  · rintro h j T hT hK C hC ci hc
    rw [hE j T hT hK C hC] at hc
    cases hc
    obtain ⟨v, hv⟩ := hbr j T hT hK C hC
    exact hv.defeq (h j T hT hK C hC)

/-- **OBLIGATION (B)'s RESIDUE, DISCHARGED DOWN TO `hargs` AND THE BRIDGE.**  Composing §1, §2,
§3 and §4: `ValRestC` at the pair obligation (B) uses follows from the specification clause
`Faithful.ctor_agree`, `HargsShared`'s constructor-head datum, and the bridge.  No new spec
clause; no hole. -/
theorem valRestC_ctorStage_of_faithful (hnd0 : D.allNames.Nodup) (hnd : R.DomNodup D K)
    (hbn : D.blockNames.Nodup) {npJ : Nat → Nat} {env E₁ E₂ E₃ : VEnv}
    (h₂ : E₁.addIndCtors D = some E₂) (h₃ : E₂.addIndRecs D = some E₃)
    (hfa : R.Faithful D env K npJ) (hle : env ≤ F)
    (hparams : OnCtx D.params.reverse (F.IsType D.uvars))
    (hlvl : ∀ j, ∀ l ∈ R.tyLvls j, l.WF D.uvars)
    (hargs : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      ∀ ci : VConstant, env.constants (R.ctorName C.name) = some ci →
        F.HasArgs D.uvars D.params.reverse (R.declTele ci (npJ j) j) (R.tyArgs j))
    (hbr : R.CtorTypeBridge D K F) : R.ValRestC D K E₂ F :=
  (valRestC_iff_ctorStage hnd0 hnd hbn h₃).2
    ((valRestCtor_iff_ctorTyped (fun _ _ hT _ _ hC => ctorConst_ctorStage h₂ hT hC) hbr).2
      fun j T hT hK C hC =>
      ctorVal_hasType_of_faithful hfa hle hparams hT hK hC (hlvl j) (hargs j T hT hK C hC))

/-! ## §5 The recursor half at the pair obligation (C) uses — and it is (B)'s own `hbridge`

At `E₃ = E₂.addIndRecs D` the companion recursor **is** declared, at `⟨D.recUvars, D.recType j⟩`,
so §2's freshness argument is gone and `ValRestRec` is live.  `R.recVal` is a **rename** — a
constant, with no `mkLams` and hence no β-redex of its own
(`VIndRestore.substC_recConst`) — so the typing is one `VEnv.HasType.const` against the entry
`D.recConstsR R K` declares, and the whole residue is the conversion between the *restored* and
the *stored* recursor type.  That conversion is exactly obligation (B)'s `hbridge`
(`InductiveDeclExamples.ntreeAux_recConstsR_wf_of_bridge`'s hypothesis) in undecomposed form:
(B) states it as a `mkPi` decomposition plus a `TeleDefEq` plus a body defeq, which is a
*presentation* of the same defeq.

So **(C)'s extra residue over (B) is a datum (B) already carries.** -/

/-- **THE RECURSOR BRIDGE** — (B)'s `hbridge` as a single defeq. -/
def RecTypeBridge (R : VIndRestore) (D : VInductDecl') (K : List Name) (F : VEnv) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∃ v, F.IsDefEq D.recUvars [] ((D.recTypeR R j).substC (R.csubst D K))
      ((D.recType j).substC (R.csubst D K)) (.sort v)

/-- The block's own recursor constants, at the rec stage. -/
theorem recConst_recStage {E₂ E₃ : VEnv} (h₃ : E₂.addIndRecs D = some E₃)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) :
    E₃.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ :=
  VEnv.addConstList_constants h₃ (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩)
    (by rw [VInductDecl'.recConsts, List.mem_map]
        exact ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hT, rfl⟩)

/-- …and the renamed recursor constants the step declares, at the restored type. -/
theorem recConstR_declared {F₂ F₃ : VEnv}
    (f₃ : F₂.addConstList (D.recConstsR R K) = some F₃)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) :
    F₃.constants (R.recName (Lean.mkRecName T.name))
      = some ⟨D.recUvars, (D.recTypeR R j).substC (R.csubst D K)⟩ :=
  VEnv.addConstList_constants f₃
    (R.recName (Lean.mkRecName T.name),
      ⟨D.recUvars, (D.recTypeR R j).substC (R.csubst D K)⟩)
    (by rw [VInductDecl'.recConstsR, List.mem_map]
        exact ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hT, rfl⟩)

/-- The recursor half spelled out at the stage-3 lookup: "the renamed recursor inhabits the
*stored* recursor type, substituted". -/
def RecValStored (R : VIndRestore) (D : VInductDecl') (K : List Name) (F : VEnv) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    F.HasType D.recUvars [] (R.recVal D (Lean.mkRecName T.name))
      ((D.recType j).substC (R.csubst D K))

/-- **THE THIRD `↔`.**  At the rec stage `ValRestRec` *is* `RecValStored`: the source lookup is
determined (`recConst_recStage`), so the quantifier over `ci` collapses and nothing else is
hiding in the clause.  This is the `↔` that stops a successor re-opening the recursor half as
something bigger. -/
theorem valRestRec_iff_recValStored {E₂ E₃ : VEnv} (h₃ : E₂.addIndRecs D = some E₃) :
    R.ValRestRec D K E₃ F ↔ R.RecValStored D K F := by
  refine ⟨fun h j T hT hK => h j T hT hK _ (recConst_recStage h₃ hT), ?_⟩
  rintro h j T hT hK ci hc
  rw [recConst_recStage h₃ hT] at hc
  cases hc
  exact h j T hT hK

/-- The renamed recursor at its **restored** type: free from the step's own declaration. -/
theorem recVal_hasType_recTypeR {F₂ F₃ : VEnv} {j : Nat}
    (f₃ : F₂.addConstList (D.recConstsR R K) = some F₃)
    (hlw : ((D.recTypeR R j).substC (R.csubst D K)).LevelWF D.recUvars)
    {T : VIndType} (hT : D.types[j]? = some T) :
    F₃.HasType D.recUvars [] (R.recVal D (Lean.mkRecName T.name))
      ((D.recTypeR R j).substC (R.csubst D K)) := by
  have h := VEnv.HasType.const (Γ := []) (U := D.recUvars) (recConstR_declared f₃ hT)
    (fun _ h => VLevel.params_wf h) (by simp)
  rwa [hlw.instL_id] at h

/-- **THE RECURSOR HALF, REDUCED TO (B)'s OWN `hbridge`, AND TO NOTHING ELSE.**  The level
side condition costs nothing: `VEnv.IsDefEq.levelWF` reads it straight off the bridge, so the
bridge is the *whole* premise.

**Why this direction only, and it is not a gap that can be closed here.**  The converse — reading
the bridge back off `ValRestRec` — is uniqueness of types applied to the two types `R.recVal`
inhabits, and `IsDefEq.uniq` is one of the project's thirteen holes.  So the `↔` above is stated
at `RecValStored`, where no uniqueness is needed, and the bridge is offered as the route into it.
That is deliberate: routing through the unique-typing hole to get a prettier `↔` would put a hole
in this file's cone, which item (d) forbids. -/
theorem recValStored_of_recBridge {F₂ F₃ : VEnv}
    (f₃ : F₂.addConstList (D.recConstsR R K) = some F₃)
    (hbr : R.RecTypeBridge D K F₃) : R.RecValStored D K F₃ := by
  intro j T hT hK
  obtain ⟨v, hv⟩ := hbr j T hT hK
  exact hv.defeq (recVal_hasType_recTypeR f₃ (hv.levelWF trivial).1 hT)

/-- **OBLIGATION (C)'s RESIDUE, WHOLE.**  `ValRestC` at the pair obligation (C) uses = the
constructor half (§3/§4, at the stage-3 source lookup) **and** (B)'s own recursor bridge.  Nothing
else. -/
theorem valRestC_recStage_of_bridges (hnd0 : D.allNames.Nodup) (hnd : R.DomNodup D K)
    (hbn : D.blockNames.Nodup) {E₂ E₃ F₂ F₃ : VEnv}
    (h₃ : E₂.addIndRecs D = some E₃)
    (f₃ : F₂.addConstList (D.recConstsR R K) = some F₃)
    (hctor : R.ValRestCtor D K E₃ F₃) (hbr : R.RecTypeBridge D K F₃) :
    R.ValRestC D K E₃ F₃ :=
  (valRestC_iff hnd0 hnd hbn).2
    ⟨hctor, (valRestRec_iff_recValStored h₃).2 (recValStored_of_recBridge f₃ hbr)⟩

/-! ## §6 Item (b): `WFD.const`'s defeq disjunct at every declared constructor, in general

`FlipGeneral.lean` recorded this and `hbridge` as "the same β-redex arithmetic, untouched".  This
section does the untouched part: `VIndRestore.csubst_WF_const` (`NestedRules.lean` §8.4) is the
`CSubst.WF` version and needs the bridge as a **syntactic equation**
`(C.type D j).substC (R.csubstTy D K) = (C.typeR D R j).substC (R.csubstTy D K)`, which the
parameterised block **refutes** (`InductiveDeclExamples.ntreeNode_substC_ne_typeR`).  `CSubst.WFD`
exists precisely to weaken that equation to a defeq, and this is `csubst_WF_const` with that
weakening performed: the disjunct is used at **exactly one** of the three branches, the other two
producing the left disjunct with `csubst_WF_const`'s own proofs unchanged.  That is the measurement
that `WFD` is a weakening applied in one place.

`D.recUvars ≠ D.uvars` bears here and not on `val` (`FlipGeneral.lean` §3): the disjunct's
`∀ ls, (∀ l ∈ ls, l.WF U)` ranges over more level lists at the larger `U`.  It is handled by
leaving `U` free and asking the bridge at the same `U` — so a caller at `D.recUvars` supplies a
`D.recUvars`-bridge, which is what `InductiveDeclExamples.ntree_node_const_defeq` (stated at free
`U`, used at `U = 2`) already is.  No `D.uvars`-only bridge is silently reused at `D.recUvars`. -/

/-- **THE DEFEQ DISJUNCT, GENERAL.**  `hbridgeD` is obligation (A)'s `hbridge` with the equation
weakened to a definitional equality, at a free `U` and under a free `Γ` and level instantiation —
i.e. exactly the shape `CSubst.WFD.const`'s right disjunct wants and exactly the shape
`ntree_node_const_defeq` has. -/
theorem csubst_WFD_const {env E₁ E₂ E₃ e₁ e₂ : VEnv} {U : Nat}
    (henv : env.Ordered) (hE₁ : E₁.Ordered) (hD : D.WF env)
    (hown : R.OwnId D K) (hdn : R.DomNodup D K)
    (h₁ : env.addIndTypes D = some E₁) (h₂ : E₁.addIndCtors D = some E₂)
    (h₃ : E₂.addIndRecs D = some E₃)
    (f₁ : env.addConstList (D.typeConstsC K) = some e₁)
    (f₂ : e₁.addConstList (D.ctorConstsCR R K) = some e₂)
    (hbridgeD : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors → ∀ {Γ : List VExpr} {ls : List VLevel},
      (∀ l ∈ ls, l.WF U) → ls.length = D.uvars →
      ∃ v, e₂.IsDefEq U Γ (((C.typeR D R j).substC (R.csubstTy D K)).instL ls)
        (((C.type D j).substC (R.csubstTy D K)).instL ls) (.sort v))
    {c : Name} {ci : VConstant} (hn : R.csubst D K c = none) (hc : E₂.constants c = some ci) :
    ∃ A, e₂.constants c = some ⟨ci.uvars, A⟩ ∧
      (A = ci.type.substC (R.csubst D K) ∨
        ∀ {Γ : List VExpr} {ls : List VLevel}, (∀ l ∈ ls, l.WF U) → ls.length = ci.uvars →
          ∃ v, e₂.IsDefEq U Γ (A.instL ls)
            ((ci.type.substC (R.csubst D K)).instL ls) (.sort v)) := by
  by_cases hct : c ∈ D.ctorConsts.map (·.1)
  · rw [VInductDecl'.ctorConsts, List.map_map, List.mem_map] at hct
    obtain ⟨⟨j, C⟩, hjC, hce⟩ := hct
    replace hce : C.name = c := hce
    obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hjC
    have hE : E₂.constants C.name = some ⟨D.uvars, C.type D j⟩ :=
      VEnv.addConstList_constants h₂ (C.name, ⟨D.uvars, C.type D j⟩)
        (by rw [VInductDecl'.ctorConsts, List.mem_map]; exact ⟨(j, C), hjC, rfl⟩)
    subst hce
    rw [hE] at hc; cases hc
    have hK : T.name ∉ K := fun hK => by
      rw [csubst_ctor_eq_some hdn hT hK hC] at hn; exact absurd hn nofun
    have hTe : D.types.getD j default = T := by rw [List.getD_eq_getElem?_getD, hT]; rfl
    have hmem :
        (R.ctorName C.name, (⟨D.uvars, (C.typeR D R j).substC (R.csubstTy D K)⟩ : VConstant))
          ∈ D.ctorConstsCR R K := by
      rw [VInductDecl'.ctorConstsCR, List.mem_filterMap]
      exact ⟨(j, C), hjC, by simp only []; rw [if_neg (by rw [hTe]; exact hK)]⟩
    have hlk := VEnv.addConstList_constants f₂ _ hmem
    rw [hown.ctorName j T hT hK C hC] at hlk
    refine ⟨_, hlk, .inr fun {Γ ls} hls hlen => ?_⟩
    rw [substC_ctorType_csubst_eq_csubstTy hE₁ hdn h₁ h₂ h₃ hD hT hC]
    exact hbridgeD j T C hT hK hC hls hlen
  · refine ⟨_, ?_, .inl rfl⟩
    by_cases hbn : c ∈ D.blockNames
    · rw [VInductDecl'.blockNames_eq, List.mem_map] at hbn
      obtain ⟨T, hTm, rfl⟩ := hbn
      obtain ⟨j, hT⟩ := List.getElem?_of_mem hTm
      have hK : T.name ∉ K := fun hK => by
        rw [csubst_ty_eq_some hdn hT hK] at hn; exact absurd hn nofun
      have hE : E₁.constants T.name = some ⟨D.uvars, T.type⟩ :=
        VEnv.addConstList_constants h₁ (T.name, ⟨D.uvars, T.type⟩)
          (by rw [VInductDecl'.typeConsts, List.mem_map]; exact ⟨T, hTm, rfl⟩)
      rw [VEnv.addConstList_constants_of_not_mem h₂ hct, hE] at hc
      cases hc
      have hl1 : e₁.constants T.name = some ⟨D.uvars, T.type⟩ :=
        VEnv.addConstList_constants f₁ (T.name, ⟨D.uvars, T.type⟩)
          (by rw [VInductDecl'.typeConstsC, List.mem_filterMap]
              exact ⟨(T.name, ⟨D.uvars, T.type⟩),
                by rw [VInductDecl'.typeConsts, List.mem_map]; exact ⟨T, hTm, rfl⟩,
                by rw [if_neg hK]⟩)
      rw [VEnv.addConstList_constants_of_not_mem f₂
        (fun hm => hct (mem_ctorConstsCR_names hown hm)), hl1]
      exact congrArg _ (by rw [substC_tyType_eq henv hD h₁ h₂ h₃ hTm])
    · rw [VEnv.addConstList_constants_of_not_mem h₂ hct,
        VEnv.addConstList_constants_of_not_mem h₁
          (by rw [VInductDecl'.typeConsts_names]; exact hbn)] at hc
      rw [VEnv.addConstList_constants_of_not_mem f₂
          (fun hm => hct (mem_ctorConstsCR_names hown hm)),
        VEnv.addConstList_constants_of_not_mem f₁ (fun hm => hbn (mem_typeConstsC_names hm)), hc]
      exact congrArg _ (by rw [(henv.noCSubstC (csubst_freshIn h₁ h₂ h₃) hc).substC_eq])

/-- **`(R.csubst D K).WFD E₂ e₂ U` IN GENERAL, AT A PARAMETERISED BLOCK.**  The `WFD` counterpart
of `VIndRestore.csubst_WF` (`NestedRules.lean` §8.6) — which is unavailable at `np ≥ 1`, since its
`hbridge` equation is refuted there — with the `val` clause supplied by §1–§4 rather than assumed.

This is obligation (B)'s `hσ` in general.  Everything left is β-redex arithmetic: `hbridgeD` (the
declared constructors' `const` disjunct, §6) and `hbr` (the companion constructors' `val` bridge,
§4), plus `HargsShared`'s two data (`hty` for the type constants, `hargs` for the constructor
head).  There is no strengthening premise and no new spec clause. -/
theorem csubst_WFD {npJ : Nat → Nat} {env E₁ E₂ E₃ e₁ e₂ : VEnv} {U : Nat}
    (henv : env.Ordered) (hE₁ : E₁.Ordered) (he₂ : e₂.Ordered) (hD : D.WF env)
    (hown : R.OwnId D K) (hdn : R.DomNodup D K)
    (h₁ : env.addIndTypes D = some E₁) (h₂ : E₁.addIndCtors D = some E₂)
    (h₃ : E₂.addIndRecs D = some E₃)
    (f₁ : env.addConstList (D.typeConstsC K) = some e₁)
    (f₂ : e₁.addConstList (D.ctorConstsCR R K) = some e₂)
    (hclp : VExpr.ClosedTele D.params 0)
    (hcla : ∀ j, ∀ a ∈ R.tyArgs j, a.ClosedN D.np)
    (hbridgeD : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors → ∀ {Γ : List VExpr} {ls : List VLevel},
      (∀ l ∈ ls, l.WF U) → ls.length = D.uvars →
      ∃ v, e₂.IsDefEq U Γ (((C.typeR D R j).substC (R.csubstTy D K)).instL ls)
        (((C.type D j).substC (R.csubstTy D K)).instL ls) (.sort v))
    (hty : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      e₂.HasType D.uvars [] (R.tyVal D j) (T.type.substC (R.csubst D K)))
    (hfa : R.Faithful D env K npJ) (hle : env ≤ e₂)
    (hparams : OnCtx D.params.reverse (e₂.IsType D.uvars))
    (hlvl : ∀ j, ∀ l ∈ R.tyLvls j, l.WF D.uvars)
    (hargs : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      ∀ ci : VConstant, env.constants (R.ctorName C.name) = some ci →
        e₂.HasArgs D.uvars D.params.reverse (R.declTele ci (npJ j) j) (R.tyArgs j))
    (hbr : R.CtorTypeBridge D K e₂) : (R.csubst D K).WFD E₂ e₂ U where
  closed := csubst_closed R D K hclp hcla
  const hn hc := csubst_WFD_const henv hE₁ hD hown hdn h₁ h₂ h₃ f₁ f₂ hbridgeD hn hc
  defeq hdf := csubst_WF_defeq henv h₁ h₂ h₃ f₁ f₂ hdf
  val hs hc h1 h2 h3 h4 :=
    CSubst.val_of_hasType he₂
      (csubst_val_cases h₁ h₂ h₃ hty
        (fun j T hT hK C hC =>
          (valRestCtor_iff_ctorTyped (E := E₂) (F := e₂)
            (fun _ _ hT _ _ hC => ctorConst_ctorStage h₂ hT hC) hbr).2
            (fun j' T' hT' hK' C' hC' =>
              ctorVal_hasType_of_faithful hfa hle hparams hT' hK' hC' (hlvl j')
                (hargs j' T' hT' hK' C' hC'))
            j T hT hK C hC _ (ctorConst_ctorStage h₂ hT hC))
        hs hc) h1 h2 h3 h4

end VIndRestore

/-! ## §7 Item (c): the arity-0 witness at `ntreeAux`

`ntreeAux`: `NTree α` with a `List (NTree α)` field, `uvars = 1`,
`params = [.sort (.succ (.param 0))]`, `lvl = .succ (.param 0)`, `recUvars = 2` — the block Lean's
own kernel runs the nested elimination on.  Deliberately **not** `nfnAux`, whose `uvars = 0` and
`params = []` would make both the parameter telescope and the β-redex invisible, and would make
`ctorVal`'s `mkLams` empty so §4's bridge would be `rfl`.

**Anti-vacuity is exhibited, not argued.**  The witness carries the two *instantiated* typings the
`∀` of `ValRestCtor` fires at — the companion's `nil` and `cons` — so the clause is not true by an
empty quantifier, and it carries `ValRestC` at **both** staging pairs, so the recursor half is
present in its live form at `(E₃, F₃)` and not only in the form §2 discharges.

No `VEnv.HasArgs.of_mkApp`; no `PiInv`. -/

namespace InductiveDeclExamples

/-- The two companion constructor values, as the restoration presents them — `rfl`, so §7 is not
matching against a hand-written term. -/
theorem ntree_ctorVal_nil : ntreeRestore.ctorVal ntreeAux 1 nlistNil
    = .lam (.sort (.succ (.param 0)))
      (.app (.const ``List.nil [.param 0])
        (.app (.const ``NTree [.param 0]) (.bvar 0))) := rfl

theorem ntree_ctorVal_cons : ntreeRestore.ctorVal ntreeAux 1 nlistCons
    = .lam (.sort (.succ (.param 0)))
      (.app (.const ``List.cons [.param 0])
        (.app (.const ``NTree [.param 0]) (.bvar 0))) := rfl

theorem ntreeAux_blockNames_nodup : ntreeAux.blockNames.Nodup := by decide

section
variable {E F : VEnv}
variable (hEc : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → T.name ∈ ntreeK →
  ∀ C ∈ T.ctors, E.constants C.name = some ⟨ntreeAux.uvars, C.type ntreeAux j⟩)
variable (hL : F.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
variable (hnil : F.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
variable (hcons : F.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)

include hEc hL hN hnil hcons in
/-- **`ValRestCtor` AT `ntreeAux`, AT ANY STAGE THAT HOLDS THE COMPANION CONSTRUCTORS.**  The two
live cases are `ConstSubstNested.lean` §D.3's `nlistNil_val_hasType`/`nlistCons_val_hasType` — the
concrete instances of what §3/§4 do in general. -/
theorem ntree_valRestCtor : ntreeRestore.ValRestCtor ntreeAux ntreeK E F := by
  intro j T hT hK C hC ci hc
  match j, hT with
  | 0, hT => cases hT; exact absurd hK (by decide)
  | 1, hT =>
    rw [hEc 1 T hT hK C hC] at hc
    cases hc
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain rfl | rfl := hC
    · rw [ntree_ctorVal_nil]; exact nlistNil_val_hasType hL hN hnil
    · rw [ntree_ctorVal_cons]; exact nlistCons_val_hasType hL hN hcons
  | (_ + 2), hT => simp [ntreeAux] at hT

/-! ### §7a Anti-vacuity for §4 and §6: the bridges are INHABITED at `ntreeAux`

"Instantiate, don't admire".  §4's `CtorTypeBridge` and §6's `hbridgeD` are hypotheses, so the
`↔`s and `csubst_WFD` would be worthless if they were unsatisfiable at a parameterised block.  They
are not, and the two β-steps are exhibited: at `ntreeAux` the companion's `nil` and `cons` types
differ from their restored forms by exactly one β-contraction of `ntreeVal` each, which is the same
step `ConstSubstNested.lean` §D.3 performs *inside* `nlistNil_val_hasType`/`nlistCons_val_hasType`
and never exposes. -/

include hL hN in
/-- The bridge at the companion's `nil`: one β-step. -/
theorem ntree_ctorTypeBridge_nil : ∃ v, F.IsDefEq 1 []
    (nlistNil.typeR ntreeAux ntreeRestore 1)
    ((nlistNil.type ntreeAux 1).substC (ntreeRestore.csubst ntreeAux ntreeK)) (.sort v) := by
  have hbeta : F.IsDefEq 1 [.sort (.succ (.param 0))]
      (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0)))
      (.app ntreeVal (.bvar 0)) (.sort (.succ (.param 0))) := by
    refine .symm (.beta (A := .sort (.succ (.param 0))) (B := .sort (.succ (.param 0))) ?_ ?_)
    · exact .appDF (ntree_ListC hL) (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero)))
    · exact .bvar (by exact .zero)
  exact ⟨_, .forallEDF (.sortDF (l := .succ (.param 0)) (l' := .succ (.param 0))
    Nat.zero_lt_one Nat.zero_lt_one rfl) hbeta⟩

include hL hN in
/-- …and at the companion's `cons`: two β-steps, one at the recursive companion field and one at
the result head.  The `NTree` field does **not** move — it is recursive into a *declared* member,
so `csubst` leaves it alone, which is why the bridge is not uniform in the field. -/
theorem ntree_ctorTypeBridge_cons : ∃ v, F.IsDefEq 1 []
    (nlistCons.typeR ntreeAux ntreeRestore 1)
    ((nlistCons.type ntreeAux 1).substC (ntreeRestore.csubst ntreeAux ntreeK)) (.sort v) := by
  have hb1 : F.IsDefEq 1 [.app (.const ``NTree [.param 0]) (.bvar 0), .sort (.succ (.param 0))]
      (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 1)))
      (.app ntreeVal (.bvar 1)) (.sort (.succ (.param 0))) := by
    refine .symm (.beta (A := .sort (.succ (.param 0))) (B := .sort (.succ (.param 0))) ?_ ?_)
    · exact .appDF (ntree_ListC hL) (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero)))
    · exact .bvar (by exact .succ .zero)
  have hb2 : F.IsDefEq 1
      [.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 1)),
        .app (.const ``NTree [.param 0]) (.bvar 0), .sort (.succ (.param 0))]
      (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 2)))
      (.app ntreeVal (.bvar 2)) (.sort (.succ (.param 0))) := by
    refine .symm (.beta (A := .sort (.succ (.param 0))) (B := .sort (.succ (.param 0))) ?_ ?_)
    · exact .appDF (ntree_ListC hL) (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero)))
    · exact .bvar (by exact .succ (.succ .zero))
  exact ⟨_, .forallEDF (.sortDF (l := .succ (.param 0)) (l' := .succ (.param 0))
      Nat.zero_lt_one Nat.zero_lt_one rfl)
    (.forallEDF (.appDF (ntree_NTreeC hN) (.bvar (by exact .zero))) (.forallEDF hb1 hb2))⟩

include hL hN in
/-- **§6's PREMISE, INHABITED AT A PARAMETERISED NESTED BLOCK.**  `hbridgeD` at `ntreeAux` is
`ConstSubstNested.lean` §B's `ntree_node_const_defeq` — the one place `ntree_csubst_WFD₂` uses the
`WFD` freedom — put in the shape §6 consumes.  The only declared constructor is `NTree.node`, and
`csubst` and `csubstTy` agree on its stored type (`decide`), which is
`substC_ctorType_csubst_eq_csubstTy` at the witness. -/
theorem ntree_hbridgeD (henv : F.Ordered) {U : Nat} :
    ∀ (j : Nat) (T : VIndType) (C : VIndCtor), ntreeAux.types[j]? = some T →
      T.name ∉ ntreeK → C ∈ T.ctors → ∀ {Γ : List VExpr} {ls : List VLevel},
      (∀ l ∈ ls, l.WF U) → ls.length = ntreeAux.uvars →
      ∃ v, F.IsDefEq U Γ
        (((C.typeR ntreeAux ntreeRestore j).substC
          (ntreeRestore.csubstTy ntreeAux ntreeK)).instL ls)
        (((C.type ntreeAux j).substC (ntreeRestore.csubstTy ntreeAux ntreeK)).instL ls)
        (.sort v) := by
  intro j T C hT hK hC Γ ls hls hlen
  match j, hT with
  | 0, hT =>
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC
    rw [show (ntreeNode.type ntreeAux 0).substC (ntreeRestore.csubstTy ntreeAux ntreeK)
      = (ntreeNode.type ntreeAux 0).substC (ntreeRestore.csubst ntreeAux ntreeK) from by decide]
    match ls, hlen with
    | [l], _ =>
      obtain ⟨v, hv⟩ := ntree_node_const_defeq (U := U) (l := l) hL hN
        (hls _ List.mem_cons_self)
      exact ⟨v, hv.weak0 henv⟩
  | 1, hT => cases hT; exact absurd (by decide) hK
  | (_ + 2), hT => simp [ntreeAux] at hT

include hL hN in
/-- **§4's PREMISE, INHABITED AT A PARAMETERISED NESTED BLOCK.** -/
theorem ntree_ctorTypeBridge : ntreeRestore.CtorTypeBridge ntreeAux ntreeK F := by
  intro j T hT hK C hC
  match j, hT with
  | 0, hT => cases hT; exact absurd hK (by decide)
  | 1, hT =>
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain rfl | rfl := hC
    · exact ntree_ctorTypeBridge_nil hL hN
    · exact ntree_ctorTypeBridge_cons hL hN
  | (_ + 2), hT => simp [ntreeAux] at hT

end

section
variable {F₃ : VEnv}
variable (hL : F₃.constants ``List = some ⟨1, listType.type⟩)
variable (hN : F₃.constants ``NTree
  = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
variable (hnil : F₃.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
variable (hcons : F₃.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)
variable (hnode : F₃.constants ``NTree.node
  = some ⟨1, (ntreeNode.typeR ntreeAux ntreeRestore 0).substC
      (ntreeRestore.csubstTy ntreeAux ntreeK)⟩)

include hL hN hnil hcons hnode in
/-- **`RecTypeBridge` AT `ntreeAux`** — §5's residue, which is `ConstSubstNested.lean` §H.2's
`rRecPi1` on the nose.  That is the machine-checked form of "(C)'s extra residue over (B) is a
datum (B) already carries": `rRecPi1` and `rRecPi0` are the two halves of (B)'s own `rhbridge`. -/
theorem ntree_recTypeBridge : ntreeRestore.RecTypeBridge ntreeAux ntreeK F₃ := by
  intro j T hT hK
  match j, hT with
  | 0, hT => cases hT; exact absurd hK (by decide)
  | 1, _ => exact rRecPi1 hL hN hnil hcons hnode
  | (_ + 2), hT => simp [ntreeAux] at hT

end

/-- **THE WITNESS, ARITY 0.**  Everything existentially closed over the declaration history and
all six staging environments, at the parameterised nested block:

* the two `ValRestC` halves at the ctor-stage pair `(E₂, F₂)` — obligation (B)'s residue — with the
  recursor half from §2 and the constructor half from §3/§4's concrete instances;
* `ValRestC` itself at `(E₂, F₂)`, through the `↔`;
* the **two instantiated typings** the constructor half fires at, so the clause is not vacuous;
* `ValRestC` at the rec-stage pair `(E₃, F₃)` — obligation (C)'s residue — where the recursor half
  is **live**, discharged through `RecTypeBridge`. -/
theorem ntreeAux_valRestC_both_stages :
    ∃ (env₁ E₁ E₂ E₃ F₁ F₂ F₃ : VEnv),
      VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some E₁ ∧
      E₁.addIndCtors ntreeAux = some E₂ ∧
      E₂.addIndRecs ntreeAux = some E₃ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁ ∧
      F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂ ∧
      F₂.addConstList (ntreeAux.recConstsR ntreeRestore ntreeK) = some F₃ ∧
      ntreeRestore.ValRestCtor ntreeAux ntreeK E₂ F₂ ∧
      ntreeRestore.ValRestRec ntreeAux ntreeK E₂ F₂ ∧
      ntreeRestore.ValRestC ntreeAux ntreeK E₂ F₂ ∧
      F₂.HasType 1 [] (ntreeRestore.ctorVal ntreeAux 1 nlistNil)
        ((nlistNil.type ntreeAux 1).substC (ntreeRestore.csubst ntreeAux ntreeK)) ∧
      F₂.HasType 1 [] (ntreeRestore.ctorVal ntreeAux 1 nlistCons)
        ((nlistCons.type ntreeAux 1).substC (ntreeRestore.csubst ntreeAux ntreeK)) ∧
      ntreeRestore.CtorTypeBridge ntreeAux ntreeK F₂ ∧
      (∀ (j : Nat) (T : VIndType) (C : VIndCtor), ntreeAux.types[j]? = some T →
        T.name ∉ ntreeK → C ∈ T.ctors → ∀ {Γ : List VExpr} {ls : List VLevel},
        (∀ l ∈ ls, l.WF ntreeAux.recUvars) → ls.length = ntreeAux.uvars →
        ∃ v, F₂.IsDefEq ntreeAux.recUvars Γ
          (((C.typeR ntreeAux ntreeRestore j).substC
            (ntreeRestore.csubstTy ntreeAux ntreeK)).instL ls)
          (((C.type ntreeAux j).substC (ntreeRestore.csubstTy ntreeAux ntreeK)).instL ls)
          (.sort v)) ∧
      ntreeRestore.RecTypeBridge ntreeAux ntreeK F₃ ∧
      ntreeRestore.ValRestRec ntreeAux ntreeK E₃ F₃ ∧
      ntreeRestore.ValRestC ntreeAux ntreeK E₃ F₃ := by
  obtain ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃⟩ := ntree_stage₃_exists
  have hEc₂ : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → T.name ∈ ntreeK →
      ∀ C ∈ T.ctors, E₂.constants C.name = some ⟨ntreeAux.uvars, C.type ntreeAux j⟩ :=
    fun _ _ hT _ _ hC => VIndRestore.ctorConst_ctorStage hE₂ hT hC
  have hEc₃ : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → T.name ∈ ntreeK →
      ∀ C ∈ T.ctors, E₃.constants C.name = some ⟨ntreeAux.uvars, C.type ntreeAux j⟩ :=
    fun _ _ hT _ _ hC =>
      (VEnv.addConstList_le hE₃).constants (VIndRestore.ctorConst_ctorStage hE₂ hT hC)
  have hL₂ := ntreeF₂_list h hF₁ hF₂
  have hN₂ := ntreeF₂_ntree hF₁ hF₂
  have hnil₂ := ntreeF₂_nil h hF₁ hF₂
  have hcons₂ := ntreeF₂_cons h hF₁ hF₂
  have hL₃ := ntreeF₃_list h hF₁ hF₂ hF₃
  have hN₃ := ntreeF₃_ntree hF₁ hF₂ hF₃
  have hnil₃ := ntreeF₃_nil h hF₁ hF₂ hF₃
  have hcons₃ := ntreeF₃_cons h hF₁ hF₂ hF₃
  have hnode₃ := ntreeF₃_node hF₂ hF₃
  have hctor₂ := ntree_valRestCtor hEc₂ hL₂ hN₂ hnil₂ hcons₂
  have hctor₃ := ntree_valRestCtor hEc₃ hL₃ hN₃ hnil₃ hcons₃
  have hrec₂ : ntreeRestore.ValRestRec ntreeAux ntreeK E₂ F₂ :=
    VIndRestore.valRestRec_ctorStage hE₃
  have hbr := ntree_recTypeBridge hL₃ hN₃ hnil₃ hcons₃ hnode₃
  have hrec₃ : ntreeRestore.ValRestRec ntreeAux ntreeK E₃ F₃ :=
    (VIndRestore.valRestRec_iff_recValStored hE₃).2
      (VIndRestore.recValStored_of_recBridge hF₃ hbr)
  refine ⟨env₁, E₁, E₂, E₃, F₁, F₂, F₃, h, hE₁, hE₂, hE₃, hF₁, hF₂, hF₃,
    hctor₂, hrec₂,
    (VIndRestore.valRestC_iff ntreeAux_allNames_nodup ntreeRestore_domNodup
      ntreeAux_blockNames_nodup).2 ⟨hctor₂, hrec₂⟩,
    ?_, ?_, ntree_ctorTypeBridge hL₂ hN₂,
    ntree_hbridgeD hL₂ hN₂ (ntreeF₂_ordered h hE₁ hF₁ hF₂), hbr, hrec₃,
    (VIndRestore.valRestC_iff ntreeAux_allNames_nodup ntreeRestore_domNodup
      ntreeAux_blockNames_nodup).2 ⟨hctor₃, hrec₃⟩⟩
  · have hmem : nlistNil ∈ (ntreeAux.types.getD 1 default).ctors := by
      show nlistNil ∈ [nlistNil, nlistCons]; exact List.mem_cons_self
    exact hctor₂ 1 _ rfl (by decide) nlistNil hmem _ (hEc₂ 1 _ rfl (by decide) _ hmem)
  · have hmem : nlistCons ∈ (ntreeAux.types.getD 1 default).ctors := by
      show nlistCons ∈ [nlistNil, nlistCons]; exact List.Mem.tail _ List.mem_cons_self
    exact hctor₂ 1 _ rfl (by decide) nlistCons hmem _ (hEc₂ 1 _ rfl (by decide) _ hmem)

end InductiveDeclExamples

end Lean4Lean

/-! ## §8 What remains of (B) and (C) after this round — and item (d)

Composing this file with `FlipGeneral.lean` §1, the three obligations of
`VEnv.addInductR_ordered'` stand as follows at a **parameterised** nested block.

| | obligation | what is left |
|---|---|---|
| (A) | restored **constructor** types | `hbridge` — one telescope defeq per *declared* constructor |
| (B) | renamed **recursor** types | `hσ.val`: the family's node (`FlipGeneral` §1) **and** the companion constructors' `hargs` + `CtorTypeBridge` (§3/§4); `hσ.const`: `hbridgeD` (§6) — and `csubst_WFD` assembles all of it |
| (C) | restored **ι-rules** | the same, **plus** `RecTypeBridge` (§5) — which is (B)'s own `rhbridge` — plus `IotaHargs` per rule |

So the honest statement after this round:

> **`ValRestC` needs no new specification clause.**  Its recursor half is free at obligation (B)'s
> staging pair and is (B)'s own recursor bridge at (C)'s; its constructor half is
> `Faithful.ctor_agree` — a clause the spec already has — plus `HargsShared`'s constructor-head
> `hargs` and one bridge defeq per companion constructor.  Every residue of (B) and (C) is now
> either one of `HargsShared`'s two data or β-redex arithmetic of the `hbridge` family.  Nothing
> that is left is a strengthening, an inhabitation, or a conservativity question.

**Item (d): which of the project's thirteen holes this routes through — NONE.**  Measured with
`scripts/exists.lean` over the whole built population, not asserted: every declaration of this
file reports `cone reaches sorryAx: false`.  In particular `IsDefEq.uniq` (unique typing) is
**not** in any cone: §5 states its `↔` at `RecValStored` precisely to avoid it, and the one place a
uniqueness-shaped step would have been convenient is recorded there as an implication instead.
`VEnv.StrengtheningTarget` / `VEnv.AxiomConservativityWF` are absent too — they were `FlipGeneral`
§1's concern and this file never enters the restriction cycle at all.

## §9 Axiom audit, per declaration -/

#print axioms Lean4Lean.VIndRestore.valRestC_iff
#print axioms Lean4Lean.VIndRestore.valRestRec_of_fresh
#print axioms Lean4Lean.VIndRestore.valRestRec_ctorStage
#print axioms Lean4Lean.VIndRestore.valRestC_iff_ctorStage
#print axioms Lean4Lean.VIndRestore.ctorVal_hasType_of_faithful
#print axioms Lean4Lean.VIndRestore.ctorConst_ctorStage
#print axioms Lean4Lean.VIndRestore.valRestCtor_iff_ctorTyped
#print axioms Lean4Lean.VIndRestore.valRestC_ctorStage_of_faithful
#print axioms Lean4Lean.VIndRestore.valRestRec_iff_recValStored
#print axioms Lean4Lean.VIndRestore.recConst_recStage
#print axioms Lean4Lean.VIndRestore.recConstR_declared
#print axioms Lean4Lean.VIndRestore.recVal_hasType_recTypeR
#print axioms Lean4Lean.VIndRestore.recValStored_of_recBridge
#print axioms Lean4Lean.VIndRestore.valRestC_recStage_of_bridges
#print axioms Lean4Lean.VIndRestore.csubst_WFD_const
#print axioms Lean4Lean.VIndRestore.csubst_WFD
#print axioms Lean4Lean.InductiveDeclExamples.ntree_ctorVal_nil
#print axioms Lean4Lean.InductiveDeclExamples.ntree_ctorVal_cons
#print axioms Lean4Lean.InductiveDeclExamples.ntree_valRestCtor
#print axioms Lean4Lean.InductiveDeclExamples.ntree_ctorTypeBridge_nil
#print axioms Lean4Lean.InductiveDeclExamples.ntree_ctorTypeBridge_cons
#print axioms Lean4Lean.InductiveDeclExamples.ntree_ctorTypeBridge
#print axioms Lean4Lean.InductiveDeclExamples.ntree_hbridgeD
#print axioms Lean4Lean.InductiveDeclExamples.ntree_recTypeBridge
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_valRestC_both_stages
