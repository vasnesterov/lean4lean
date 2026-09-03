import Lean4Lean.Verify.Inductive.WholeTypeBridge

/-!
# `FldDischarge`: the nested flip's per-field datum, named once and reduced

`docs/handoff-wholetypebridge.md` §6 leaves the nested `AddInduct` flip standing on three leaves, of
which the first is `CtorBeta` §3's `hfld` and the second is `ValRestGeneral` §6's `hbridgeD`.  This
file's first job is to check that those are **one** leaf and not two, and its second is to reduce it.

## What is proved

* **§A the collapse, machine-checked.**  `VIndRestore.FldD` is the datum written *once* and fed, with
  no glue, to both `VEnv.ctorConstsCR_wf_of_fieldsD`'s `hfld` and `VIndRestore.csubst_hbridgeD`'s.  Had
  the two propositions differed in any binder, in either context list, or in which `CSubst` they name,
  one of the two applications would have failed to elaborate.  Leaves (1) and (2) are **one leaf**.
* **§B the own-pointing fields are free, and it is an `↔`.**  `VIndRestore.fldD_iff_fldK`: `FldD` *is*
  its companion-pointing sub-family.  The content is the backward direction —
  `CtorBeta` §6b's `head_defeq_of_own` plus §6c's `ctorFieldEntry_onCtx`.
* **§C `FldK` from the head defeq alone**, one `mkPi` congruence per charged field.  Stated as
  sufficiency, deliberately: the converse is Π-injectivity for `IsDefEq`, i.e.
  `VEnv.IsDefEqU.forallE_inv_stratified`, one of the thirteen holes.  The reason is recorded at the
  statement.
* **§D `hbridgeD` from `NestedRules.lean` §8.8's β data** (`VIndRestore.csubst_hbridgeD_of_betaD`).
  This route did not exist: `CtorBeta` §7 stops at `∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2`, and
  `csubst_hbridgeD` wants `FldD`, which §7 consumes and does not emit.
* **§E the arity-0 witness at `ntreeAux`** with the inline `.beta` *removed*: `FldD` reached through
  `fldD_of_betaD`, so the β arithmetic is the general theorem's and `hbv` is `TeleMove2` §3's.
* **§F `RecTypeBridge` from the entrywise motive/minor defeqs** — the brief's leaf (2)'s `hM`/`hQ`
  reduced to what §T5/§T6 actually deliver.  `VInductDecl'.recTypeTele_teleDefEq` fuses the two blocks
  and so cannot supply `hM` and `hQ` separately; §F splits it.
* **§G §E's `hnoc` in general** (the brief's leaf (3)): the three `NoCSubst` families on `C.params`,
  `C.fieldTypesR` and `C.args`, plus `VIndRestore.SubstFree`, and nothing else.
* **§H §G exhibited non-vacuous at `ntreeAux`**, and its conclusion reproduced through the general
  route rather than by `decide` on the whole equation.

## What is NOT claimed

`hfld` is **not discharged**.  §D reduces it to `BetaD`, and `BetaD` is where it stops: its `hbody` is
§8.7's `hargs`, and `VIndRestore.instAt_indep_of_tyArgs` *proves* that no restoration-independent
argument produces that.  §F does not discharge `hmot`/`hmin`/`hbody`, and §G does not discharge §E's
**live** result-head defeq.  No frozen file was read for editing, let alone edited.  No `sorry`; no
`VEnv.HasArgs.of_mkApp`; no `PiInv`; no `VEnv.IsDefEq.uniq`; no `VEnv.AxiomConservativityWF`.

See `docs/handoff-flddischarge.md` for the pre-flight table, the measurements, and the reduction
diagram.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## §A The collapse, machine-checked

The claim under test: `VIndRestore.csubst_hbridgeD`'s `hfld` and
`VEnv.ctorConstsCR_wf_of_fieldsD`'s `hfld` are the same proposition.

Prose cannot settle that, and neither can `Iff.rfl` between two hand-retyped copies — a retyping
that drifts in a binder still elaborates.  What settles it is **one** definition fed to **both**
consumers with no glue: if `FldD` were not literally each hypothesis, one of the two theorems below
would fail to elaborate. -/

namespace VIndRestore

/-- **The per-recursive-field β datum, named once.**

Character for character the `hfld` of `VEnv.ctorConstsCR_wf_of_fieldsD` (`CtorBeta` §3) and of
`VIndRestore.csubst_hbridgeD` (`WholeTypeBridge` §C).  That it is both is not asserted here; it is
elaborated, by `fldD_ctorConstsCR` and `fldD_hbridgeD` below. -/
def FldD (R : VIndRestore) (D : VInductDecl') (K : List Name) (e₁ : VEnv) : Prop :=
  ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
    T.name ∉ K → C ∈ T.ctors →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → ¬ VExpr.NoConsts K F.type →
      ∃ u : VLevel, e₁.IsDefEq D.uvars
        ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
          ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse)
        (F.type.substC (R.csubstTy D K))
        ((R.restore D i F.type).substC (R.csubstTy D K)) (.sort u)

end VIndRestore

section
variable {env env₃ e₁ : VEnv} {D : VInductDecl'} {K : List Name} {R : VIndRestore}

/-- **`FldD` is obligation (A)'s residual.**  `CtorBeta` §3 verbatim. -/
theorem VEnv.ctorConstsCR_wf_of_fldD
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃) (henv₃ : env₃.Ordered)
    (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hfld : R.FldD D K e₁) :
    ∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2 :=
  VEnv.ctorConstsCR_wf_of_fieldsD hD h₃ henv₃ he₁ hσ hown hfld

/-- **…and `FldD` is `ValRestGeneral` §6's `hbridgeD`.**  `WholeTypeBridge` §C verbatim.

Together with `VEnv.ctorConstsCR_wf_of_fldD` this **is** the collapse: the same `FldD` term is
accepted, with no glue whatsoever, as both hypotheses.  Anything weaker than literal identity of the
two propositions would have made one of the two applications fail. -/
theorem VIndRestore.csubst_hbridgeD_of_fldD
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃) (henv₃ : env₃.Ordered)
    (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hfld : R.FldD D K e₁) :
    ∀ (U : Nat) (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors → ∀ {Γ : List VExpr} {ls : List VLevel},
      (∀ l ∈ ls, l.WF U) → ls.length = D.uvars →
      ∃ v, e₁.IsDefEq U Γ (((C.typeR D R j).substC (R.csubstTy D K)).instL ls)
        (((C.type D j).substC (R.csubstTy D K)).instL ls) (.sort v) :=
  VIndRestore.csubst_hbridgeD hD h₃ henv₃ he₁ hσ hown hfld

end


/-! ## §B `FldD` charges only the fields pointing at a **companion** — and that is an `↔`

`CtorBeta` §3's `hfld` is quantified over *every* recursive field whose stored type names a companion
constant anywhere.  That includes fields whose `recArg.idx` points back at the block's **own**
member — and those exist: a field may name a companion in a *binder* or an *index argument* while its
head is the block's own type, which is exactly the configuration
`VIndRestore.head_defeq_of_own`'s docstring describes, and it is also the shape of the β-redex fields
`ElimNestedInductive` manufactures.

At such a field the restoration does not move the head at all (`OwnId.tyAppR_eq`), so the datum is
free.  Below is that, as an **equivalence**: `FldD` is not merely *implied by* the companion-pointing
sub-family, it *is* it.  A successor that reduces the flip to `FldK` has therefore not weakened
anything, and a successor that re-derives `FldD` from scratch is doing strictly more work than the
problem requires. -/

namespace VIndRestore

/-- **`FldD` restricted to the fields whose `recArg` points at a COMPANION member.** -/
def FldK (R : VIndRestore) (D : VInductDecl') (K : List Name) (e₁ : VEnv) : Prop :=
  ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
    T.name ∉ K → C ∈ T.ctors →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → ¬ VExpr.NoConsts K F.type →
      ∀ T' : VIndType, D.types[r.idx]? = some T' → T'.name ∈ K →
      ∃ u : VLevel, e₁.IsDefEq D.uvars
        ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
          ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse)
        (F.type.substC (R.csubstTy D K))
        ((R.restore D i F.type).substC (R.csubstTy D K)) (.sort u)

end VIndRestore

/-- **The syntactic side condition both directions of §B and all of §C need.**

Exactly the canonicity half of `VEnv.ctorConstsCR_wf_of_betaD`'s `hcan`, with its
`∀ a ∈ r.args, a.NoCSubst …` conjunct *dropped*: that conjunct is used only by the β-step (§D), never
by the own-pointing branch, and carrying it here would make §B's `↔` hold under a hypothesis strictly
stronger than it needs.

**It does not mention `R` at all** — the linter said so before the docstring did.  So the canonicity
half of `hcan` is a property of the *declaration*, not of the restoration: it can be discharged once
per block, `decide`-ably, with no reference to what the block is being restored to. -/
def VInductDecl'.CanFld (D : VInductDecl') (K : List Name) : Prop :=
  ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
    T.name ∉ K → C ∈ T.ctors →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → ¬ VExpr.NoConsts K F.type →
      F.type = r.canonType D i ∧ (∀ B ∈ r.binders, VExpr.NoConsts K B) ∧
        ∃ T' : VIndType, D.types[r.idx]? = some T'

section
variable {env env₃ e₁ : VEnv} {D : VInductDecl'} {K : List Name} {R : VIndRestore}

/-- **Forward, and it costs nothing**: restricting the quantifier. -/
theorem VIndRestore.fldK_of_fldD (h : R.FldD D K e₁) : R.FldK D K e₁ :=
  fun j T C hT hK hC i F r hF hr hnc _ _ _ => h j T C hT hK hC i F r hF hr hnc

/-- **Backward: the own-pointing fields are FREE.**  `head_defeq_of_own` makes the two sides of such
a field's datum the *same expression*, and the typing that then closes it is `CtorBeta` §6c's
`ctorFieldEntry_onCtx`, which comes out of the source constructor's own well-formedness.

This is the direction with content, and it is what makes §B an equivalence rather than a
convenience. -/
theorem VIndRestore.fldD_of_fldK
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃) (henv₃ : env₃.Ordered)
    (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hnd : D.blockNames.Nodup) (hcan : D.CanFld K) (h : R.FldK D K e₁) :
    R.FldD D K e₁ := by
  intro j T C hT hK hC i F r hF hr hnc
  obtain ⟨hcanF, hb, T', hT'⟩ := hcan j T C hT hK hC i F r hF hr hnc
  have hs : VConstant.WF env₃ ⟨D.uvars, C.type D j⟩ :=
    (hD.ctors env₃ h₃ j T hT C hC).constant_wf henv₃
  have hfpi : F.type.substC (R.csubstTy D K)
      = VExpr.mkPi (r.binders.map (VExpr.substC · (R.csubstTy D K)))
          ((D.tyApp r.idx (r.binders.length + i) r.args).substC (R.csubstTy D K)) := by
    rw [hcanF, VIndRecArg.canonType, VExpr.substC_mkPi, VIndRecArg.canonResult]
  obtain ⟨hOnΔ, hCd⟩ := VIndRestore.ctorFieldEntry_onCtx he₁ hσ hs hF hfpi
  by_cases hK' : T'.name ∈ K
  · exact h j T C hT hK hC i F r hF hr hnc T' hT' hK'
  · exact VIndRestore.field_defeq_of_canonical hown hnd hr hcanF hT' hb hOnΔ
      (VIndRestore.head_defeq_of_own hown hT' hK' hCd)

/-- **THE `↔`.**  Under the ambient staging data, `hown`, `hnd` and the syntactic `CanFld`, the flip's
per-field leaf **is** its companion-pointing sub-family.  Nothing is handed back. -/
theorem VIndRestore.fldD_iff_fldK
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃) (henv₃ : env₃.Ordered)
    (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hnd : D.blockNames.Nodup) (hcan : D.CanFld K) :
    R.FldD D K e₁ ↔ R.FldK D K e₁ :=
  ⟨VIndRestore.fldK_of_fldD,
    VIndRestore.fldD_of_fldK hD h₃ henv₃ he₁ hσ hown hnd hcan⟩

end


/-! ## §C `FldK` from the **head** defeq alone

At a canonical recursive field the stored type is `mkPi r.binders (D.tyApp r.idx k r.args)` and its
restoration is the same with `tyAppR`, so the whole per-field datum is one `mkPi` congruence over an
**unchanged** binder telescope.  `CtorBeta` §6's `field_defeq_of_canonical` performs that congruence;
its `OnCtx` is free (§6c).  So `FldK` reduces to `FldHead`: one defeq **at the head**, in the field's
own context extended by its binders.

**Why this is an implication and not an `↔`, recorded at the statement.**  The converse — recovering
the head defeq from the whole-`mkPi` defeq over an identical telescope — is Π-injectivity for
`IsDefEq`, i.e. `VEnv.IsDefEqU.forallE_inv` / `VEnv.PiInv`.  Its only proof in the tree is
`VEnv.IsDefEqU.forallE_inv_stratified`, which is **one of the thirteen holes** (confirmed by
`scripts/exists.lean`: it is what taints `VEnv.IsDefEq.uniq`, cone 3472).  A weaker statement is
therefore chosen deliberately here, and the honest reading of §C is: *`FldHead` is sufficient, and
whether it is necessary is gated on a hole.*  §B's `↔` is where the equivalence lives; §C's
sufficiency is where the reduction lives. -/

namespace VIndRestore

/-- **The head defeq at a companion-pointing canonical field** — `FldK`'s content with the binder
telescope stripped off. -/
def FldHead (R : VIndRestore) (D : VInductDecl') (K : List Name) (e₁ : VEnv) : Prop :=
  ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
    T.name ∉ K → C ∈ T.ctors →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → ¬ VExpr.NoConsts K F.type →
      ∀ T' : VIndType, D.types[r.idx]? = some T' → T'.name ∈ K →
      ∃ v : VLevel, e₁.IsDefEq D.uvars
        ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse
          ++ ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
            ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse))
        ((D.tyApp r.idx (r.binders.length + i) r.args).substC (R.csubstTy D K))
        ((D.tyAppR R r.idx (r.binders.length + i) r.args).substC (R.csubstTy D K)) (.sort v)

end VIndRestore

section
variable {env env₃ e₁ : VEnv} {D : VInductDecl'} {K : List Name} {R : VIndRestore}

/-- **`FldK` from `FldHead`.**  One `mkPi` congruence per charged field; the `OnCtx` is free. -/
theorem VIndRestore.fldK_of_fldHead
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃) (henv₃ : env₃.Ordered)
    (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hnd : D.blockNames.Nodup) (hcan : D.CanFld K) (h : R.FldHead D K e₁) :
    R.FldK D K e₁ := by
  intro j T C hT hK hC i F r hF hr hnc T' hT' hK'
  obtain ⟨hcanF, hb, -⟩ := hcan j T C hT hK hC i F r hF hr hnc
  have hs : VConstant.WF env₃ ⟨D.uvars, C.type D j⟩ :=
    (hD.ctors env₃ h₃ j T hT C hC).constant_wf henv₃
  have hfpi : F.type.substC (R.csubstTy D K)
      = VExpr.mkPi (r.binders.map (VExpr.substC · (R.csubstTy D K)))
          ((D.tyApp r.idx (r.binders.length + i) r.args).substC (R.csubstTy D K)) := by
    rw [hcanF, VIndRecArg.canonType, VExpr.substC_mkPi, VIndRecArg.canonResult]
  obtain ⟨hOnΔ, -⟩ := VIndRestore.ctorFieldEntry_onCtx he₁ hσ hs hF hfpi
  exact VIndRestore.field_defeq_of_canonical hown hnd hr hcanF hT' hb hOnΔ
    (h j T C hT hK hC i F r hF hr hnc T' hT' hK')

/-- **…and therefore `FldD` from `FldHead`**: §C then §B's backward direction. -/
theorem VIndRestore.fldD_of_fldHead
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃) (henv₃ : env₃.Ordered)
    (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hnd : D.blockNames.Nodup) (hcan : D.CanFld K) (h : R.FldHead D K e₁) :
    R.FldD D K e₁ :=
  VIndRestore.fldD_of_fldK hD h₃ henv₃ he₁ hσ hown hnd hcan
    (VIndRestore.fldK_of_fldHead hD h₃ henv₃ he₁ hσ hown hnd hcan h)

end


/-! ## §D `FldHead` from the β-step's data — and hence `hbridgeD` from it, which was not reachable

`NestedRules.lean` §8.8 (`VIndRestore.substC_tyApp_defeq_tyAppR_comp`) is the typed β-step at a
companion head, and `CtorBeta` §6b (`head_defeq_of_beta`) is it with `substC` on both sides.  §7 of
`CtorBeta` already composes those down to obligation (A)'s **conclusion**
(`VEnv.ctorConstsCR_wf_of_betaD`).  What §7 does *not* do is expose `FldD` itself, and that is not a
presentational detail: `csubst_hbridgeD` consumes `FldD`, not `∀ c ∈ ctorConstsCR …`.  So before this
section **`hbridgeD` could not be reached from §8.8's data at all** — the only route to it was a
`FldD` produced by hand, block by block.

§D closes that: `BetaD → FldHead → FldK → FldD → hbridgeD`.

`BetaD` below is `VEnv.ctorConstsCR_wf_of_betaD`'s `hbeta` verbatim, and `ArgsNoC` is the one
remaining conjunct of its `hcan`.  `hbv` is **not** a hypothesis — it is discharged inside, from
`VIndCtor.WF.hasArgs_params_bvars_of_wf`, exactly as §7 does it. -/

namespace VIndRestore

/-- **§8.8's data at the charged companion-pointing fields** — `ctorConstsCR_wf_of_betaD`'s `hbeta`,
named.  Four typed components and one syntactic one; `hbv` is absent because it is a theorem. -/
def BetaD (R : VIndRestore) (D : VInductDecl') (K : List Name) (e₁ : VEnv) : Prop :=
  ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
    T.name ∉ K → C ∈ T.ctors →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → ¬ VExpr.NoConsts K F.type →
      ∀ T' : VIndType, D.types[r.idx]? = some T' → T'.name ∈ K →
      ∃ (As : List VExpr) (B B' : VExpr) (v : VLevel),
        OnCtx (D.params.reverse ++
            ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
              ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
                ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse)))
          (e₁.IsType D.uvars) ∧
        e₁.HasType D.uvars
            (D.params.reverse ++
              ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
                ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
                  ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse)))
            (R.tyBody D r.idx) B ∧
        VExpr.instAll B (VExpr.bvars (r.binders.length + i) D.np) = VExpr.mkPi As B' ∧
        e₁.HasArgs D.uvars
            ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
              ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
                ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse))
            As r.args ∧
        VExpr.instAll B' r.args = VExpr.sort v

/-- **The index arguments are `σ`-invariant** — the fourth conjunct of
`ctorConstsCR_wf_of_betaD`'s `hcan`, split out because §B and §C do not need it. -/
def ArgsNoC (R : VIndRestore) (D : VInductDecl') (K : List Name) : Prop :=
  ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
    T.name ∉ K → C ∈ T.ctors →
    ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → ¬ VExpr.NoConsts K F.type →
      ∀ a ∈ r.args, a.NoCSubst (R.csubstTy D K)

end VIndRestore

section
variable {env env₃ e₁ : VEnv} {D : VInductDecl'} {K : List Name} {R : VIndRestore}

/-- **`FldHead` from §8.8's data.**  `head_defeq_of_beta` per charged companion-pointing field, with
`hbv` discharged from the constructor's own well-formedness (`TeleMove2` §3) rather than assumed. -/
theorem VIndRestore.fldHead_of_betaD
    (henv : env.Ordered) (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃)
    (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars)
    (hnd : D.blockNames.Nodup) (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np)
    (hnn : ∀ i, R.csubstTy D K (R.tyName i) = none)
    (hna : ∀ i, ∀ a ∈ R.tyArgs i, a.NoCSubst (R.csubstTy D K))
    (hargs : R.ArgsNoC D K) (h : R.BetaD D K e₁) :
    R.FldHead D K e₁ := by
  intro j T C hT hK hC i F r hF hr hnc T' hT' hK'
  obtain ⟨As, B, B', v, hOn, hbody, hpi, hAs, hsort⟩ :=
    h j T C hT hK hC i F r hF hr hnc T' hT' hK'
  have hCwf : VIndCtor.WF env₃ D j T C := hD.ctors env₃ h₃ j T hT C hC
  have hbv : e₁.HasArgs D.uvars
      ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
        ((((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse
          ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse))
      D.params (VExpr.bvars (r.binders.length + i) D.np) := by
    have hi : i ≤ C.fields.length := Nat.le_of_lt (by
      simpa using (List.getElem?_eq_some_iff.1 hF).1)
    have hb := hCwf.hasArgs_params_bvars_of_wf henv he₁ hD h₃ hσ
      ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
        (((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse)
    rw [List.append_assoc] at hb
    simpa [Nat.min_eq_left hi] using hb
  exact VIndRestore.head_defeq_of_beta hnd hlw hcl he₁ hnn hna hT' hK'
    (hargs j T C hT hK hC i F r hF hr hnc) hOn hbv hbody hpi hAs hsort

/-- **`FldD` from §8.8's data**, i.e. obligation (A)'s residual reduced to the β-step's four
components. -/
theorem VIndRestore.fldD_of_betaD
    (henv : env.Ordered) (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃)
    (henv₃ : env₃.Ordered) (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars)
    (hown : R.OwnId D K) (hnd : D.blockNames.Nodup)
    (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np)
    (hnn : ∀ i, R.csubstTy D K (R.tyName i) = none)
    (hna : ∀ i, ∀ a ∈ R.tyArgs i, a.NoCSubst (R.csubstTy D K))
    (hcan : D.CanFld K) (hargs : R.ArgsNoC D K) (h : R.BetaD D K e₁) :
    R.FldD D K e₁ :=
  VIndRestore.fldD_of_fldHead hD h₃ henv₃ he₁ hσ hown hnd hcan
    (VIndRestore.fldHead_of_betaD henv hD h₃ he₁ hσ hnd hlw hcl hnn hna hargs h)

/-- **THE COMPOSITION, AND THE POINT OF THE FILE.**  `ValRestGeneral` §6's `hbridgeD` — free `U`,
free `Γ`, free `ls` — from `NestedRules.lean` §8.8's β data alone.

Before §D this conclusion had no general route: `CtorBeta` §7 stops at
`∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2`, and `csubst_hbridgeD` wants `FldD`, which §7 consumes
and does not emit. -/
theorem VIndRestore.csubst_hbridgeD_of_betaD
    (henv : env.Ordered) (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃)
    (henv₃ : env₃.Ordered) (he₁ : e₁.Ordered) (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars)
    (hown : R.OwnId D K) (hnd : D.blockNames.Nodup)
    (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np)
    (hnn : ∀ i, R.csubstTy D K (R.tyName i) = none)
    (hna : ∀ i, ∀ a ∈ R.tyArgs i, a.NoCSubst (R.csubstTy D K))
    (hcan : D.CanFld K) (hargs : R.ArgsNoC D K) (h : R.BetaD D K e₁) :
    ∀ (U : Nat) (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T →
      T.name ∉ K → C ∈ T.ctors → ∀ {Γ : List VExpr} {ls : List VLevel},
      (∀ l ∈ ls, l.WF U) → ls.length = D.uvars →
      ∃ v, e₁.IsDefEq U Γ (((C.typeR D R j).substC (R.csubstTy D K)).instL ls)
        (((C.type D j).substC (R.csubstTy D K)).instL ls) (.sort v) :=
  VIndRestore.csubst_hbridgeD_of_fldD hD h₃ henv₃ he₁ hσ hown
    (VIndRestore.fldD_of_betaD henv hD h₃ henv₃ he₁ hσ hown hnd hlw hcl hnn hna hcan hargs h)

end


/-! ## §E Item (c): the arity-0 witness at `ntreeAux`, and the route is the value

`ntreeAux` — `NTree α` with a `List (NTree α)` field, `uvars = 1`,
`params = [.sort (.succ (.param 0))]`, `recUvars = 2`, `np = 1`.  Deliberately **not** `nfnAux`, whose
`uvars = 0` makes the level instantiation invisible and whose `params = []` empties the parameter
telescope — and, more to the point here, whose `np = 0` makes the β-step §D routes through trivial.

**What makes this witness different from `ntreeAux_wholeTypeBridge_witness` (arity 0, cone 3659).**
That one supplies `FldD` by hand — one inline `VEnv.IsDefEq.beta` — and then runs §A ∘ §B ∘ §C.  This
one supplies **`BetaD`** and reaches `FldD` through `fldD_of_betaD`, i.e. through
`NestedRules.lean` §8.8's general typed β-step and `CtorBeta` §6b/§6c, with `hbv` discharged by
`TeleMove2` §3 rather than assumed.  So the inline `.beta` is *gone* from this witness: the β
arithmetic is done by the general theorem and the block supplies only §8.8's four components.

Everything is existentially closed over the declaration history, so the witness has arity 0.  It
exhibits, at one block: `BetaD`, `FldHead`, `FldK`, `FldD`, §B's `↔` between the last two, and
`hbridgeD` at every `U` including the mixed instance `csubst_WFD` consumes
(`U = recUvars = 2`, `ls.length = uvars = 1`). -/

namespace InductiveDeclExamples

/-- §D's canonicity side condition at `ntreeAux`.  Restoration-independent, as `CanFld`'s docstring
says: nothing below mentions `ntreeRestore`. -/
theorem ntreeAux_canFld : ntreeAux.CanFld ntreeK := by
  rintro j T C hT hK hC i F r hF hr hnc
  match j, hT with
  | 0, hT =>
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC
    match i, hF with
    | 0, hF => cases hF; exact absurd hr nofun
    | 1, hF => cases hF; cases hr; exact ⟨rfl, nofun, _, rfl⟩
    | (_ + 2), hF => simp [ntreeNode] at hF
  | 1, hT => cases hT; exact absurd (by decide) hK
  | (_ + 2), hT => simp [ntreeAux] at hT

/-- §D's `ArgsNoC` at `ntreeAux`: the charged field's index-argument list is empty. -/
theorem ntreeAux_argsNoC : ntreeRestore.ArgsNoC ntreeAux ntreeK := by
  rintro j T C hT hK hC i F r hF hr hnc
  match j, hT with
  | 0, hT =>
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    subst hC
    match i, hF with
    | 0, hF => cases hF; exact absurd hr nofun
    | 1, hF => cases hF; cases hr; exact nofun
    | (_ + 2), hF => simp [ntreeNode] at hF
  | 1, hT => cases hT; exact absurd (by decide) hK
  | (_ + 2), hT => simp [ntreeAux] at hT

/-- **THE WITNESS, ARITY 0.**  At `ntreeAux`, existentially closed over the three staging
environments, with `hbridgeD` reached through §D — `BetaD → FldHead → FldK → FldD → hbridgeD` — and
not through an inline β-step. -/
theorem ntreeAux_fldDischarge_witness :
    ∃ (env₁ env₂ env₃ : VEnv),
      VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ ∧
      ntreeRestore.BetaD ntreeAux ntreeK env₃ ∧
      ntreeRestore.FldHead ntreeAux ntreeK env₃ ∧
      ntreeRestore.FldK ntreeAux ntreeK env₃ ∧
      ntreeRestore.FldD ntreeAux ntreeK env₃ ∧
      (ntreeRestore.FldD ntreeAux ntreeK env₃ ↔ ntreeRestore.FldK ntreeAux ntreeK env₃) ∧
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
  -- §8.8's four components at the one charged field, and nothing else about the β-step
  have hbeta : ntreeRestore.BetaD ntreeAux ntreeK env₃ := by
    rintro j T C hT hK hC i F r hF hr hnc T' hT' hK'
    match j, hT with
    | 0, hT =>
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      match i, hF with
      | 0, hF => cases hF; exact absurd hr nofun
      | 1, hF =>
        cases hF; cases hr; cases hT'
        refine ⟨[], .sort (.succ (.param 0)), .sort (.succ (.param 0)), .succ (.param 0),
          ?_, ?_, rfl, .nil, rfl⟩
        · show OnCtx [VExpr.sort (.succ (.param 0)), VExpr.bvar 0,
              VExpr.sort (.succ (.param 0))] (env₃.IsType 1)
          exact ⟨⟨⟨trivial, ⟨_, by type_tac⟩⟩, ⟨_, by type_tac⟩⟩, ⟨_, by type_tac⟩⟩
        · show env₃.HasType 1 [VExpr.sort (.succ (.param 0)), VExpr.bvar 0,
              VExpr.sort (.succ (.param 0))]
              (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0)))
              (.sort (.succ (.param 0)))
          type_tac
      | (_ + 2), hF => simp [ntreeNode] at hF
    | 1, hT => cases hT; exact absurd (by decide) hK
    | (_ + 2), hT => simp [ntreeAux] at hT
  have hhead : ntreeRestore.FldHead ntreeAux ntreeK env₃ :=
    VIndRestore.fldHead_of_betaD henv₁ ntreeAux_WF' h₂ henv₃ hσ (by decide)
      ntreeRestore_tyVal_levelWF ntreeRestore_tyArgs_closed
      ntreeRestore_csubstTy_tyName ntreeRestore_tyArgs_noCSubst ntreeAux_argsNoC hbeta
  have hK' : ntreeRestore.FldK ntreeAux ntreeK env₃ :=
    VIndRestore.fldK_of_fldHead ntreeAux_WF' h₂ henv₂ henv₃ hσ ntreeRestore_ownId (by decide)
      ntreeAux_canFld hhead
  have hfld : ntreeRestore.FldD ntreeAux ntreeK env₃ :=
    VIndRestore.fldD_of_fldK ntreeAux_WF' h₂ henv₂ henv₃ hσ ntreeRestore_ownId (by decide)
      ntreeAux_canFld hK'
  have hiff := VIndRestore.fldD_iff_fldK (R := ntreeRestore) ntreeAux_WF' h₂ henv₂ henv₃ hσ
    ntreeRestore_ownId (by decide) ntreeAux_canFld
  have hD := VIndRestore.csubst_hbridgeD_of_betaD henv₁ ntreeAux_WF' h₂ henv₂ henv₃ hσ
    ntreeRestore_ownId (by decide) ntreeRestore_tyVal_levelWF ntreeRestore_tyArgs_closed
    ntreeRestore_csubstTy_tyName ntreeRestore_tyArgs_noCSubst ntreeAux_canFld
    ntreeAux_argsNoC hbeta
  have hnode : ntreeNode ∈ (ntreeAux.types.getD 0 default).ctors := by
    show ntreeNode ∈ [ntreeNode]; exact List.mem_cons_self
  exact ⟨env₁, env₂, env₃, h, h₂, h₃, hbeta, hhead, hK', hfld, hiff, hD,
    fun Γ ls hls hlen => hD ntreeAux.recUvars 0 _ ntreeNode rfl (by decide) hnode hls hlen⟩

end InductiveDeclExamples


/-! ## §F Brief item (2): `RecTypeBridge` from the **entrywise** data §T5/§T6 deliver

`WholeTypeBridge` §D's `recTypeBridge_of_blocks` takes `hM`/`hQ` as *block-level* `TeleDefEq`s, which is
the form `VEnv.recConstsR_wf_of_blocks` states them in.  But the producers —
`NestedTele.lean` §T5 `substC_motiveType_defeq'` and §T6 `substC_minorType_defeq` — deliver one entry at
a time, and `VEnv.recConstsR_wf_of_entries` / `VInductDecl'.recTypeTele_teleDefEq` are where that gap is
bridged **for the `VConstant.WF` form only**: `recTypeTele_teleDefEq` fuses the two blocks into the
single appended telescope, so neither `hM` nor `hQ` can be extracted from it.

So the two halves are restated here as separate entrywise-to-block lemmas, and `RecTypeBridge` is then
reachable from `hmot`/`hmin`/`hbody` directly.  The proofs are the two bullets of
`recTypeTele_teleDefEq`'s, split apart; nothing is new mathematics, and the reason they are here is
that the fused form is unusable for the bridge. -/

namespace VInductDecl'
section
variable {e : VEnv} {D : VInductDecl'} {R : VIndRestore} {σ : CSubst}

/-- **The motive block's `TeleDefEq` from its entry defeqs** — `recTypeTele_teleDefEq`'s first bullet,
on its own. -/
theorem motives_teleDefEq_of_entries
    (hmot : ∀ t : Nat, t < D.nm → ∃ u, e.IsDefEq D.recUvars
      (((D.motives.map (VExpr.substC · σ)).take t).reverse
        ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)
      ((D.motiveType t).substC σ) ((D.motiveTypeR R t).substC σ) (.sort u)) :
    e.TeleDefEq D.recUvars (((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)
      (D.motives.map (VExpr.substC · σ)) ((D.motivesR R).map (VExpr.substC · σ)) := by
  refine VEnv.TeleDefEq.of_entries (by simp) ?_
  intro i A A' hA hA'
  rw [List.getElem?_map] at hA hA'
  obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.1 hA
  obtain ⟨B', hB', rfl⟩ := Option.map_eq_some_iff.1 hA'
  have hi : i < D.nm := by
    have := List.getElem?_eq_some_iff.1 hB; simpa using this.1
  rw [VInductDecl'.motives, List.getElem?_map, List.getElem?_range hi] at hB
  rw [VInductDecl'.motivesR, List.getElem?_map, List.getElem?_range hi] at hB'
  cases hB; cases hB'
  exact hmot i hi

/-- **The minor block's `TeleDefEq` from its entry defeqs** — `recTypeTele_teleDefEq`'s second bullet,
on its own. -/
theorem minors_teleDefEq_of_entries
    (hmin : ∀ (q t : Nat) (C : VIndCtor), D.ctorsAll[q]? = some (t, C) → ∃ u,
      e.IsDefEq D.recUvars
        (((D.minors.map (VExpr.substC · σ)).take q).reverse
          ++ ((D.motives.map (VExpr.substC · σ)).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
        ((D.minorType q t C).substC σ) ((D.minorTypeR R q t C).substC σ) (.sort u)) :
    e.TeleDefEq D.recUvars ((D.motives.map (VExpr.substC · σ)).reverse
        ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)
      (D.minors.map (VExpr.substC · σ)) ((D.minorsR R).map (VExpr.substC · σ)) := by
  refine VEnv.TeleDefEq.of_entries (by simp) ?_
  intro q A A' hA hA'
  rw [List.getElem?_map] at hA hA'
  obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.1 hA
  obtain ⟨B', hB', rfl⟩ := Option.map_eq_some_iff.1 hA'
  rw [VInductDecl'.minors_getElem?] at hB
  rw [VInductDecl'.minorsR_getElem?] at hB'
  obtain ⟨⟨t, C⟩, hq, rfl⟩ := Option.map_eq_some_iff.1 hB
  obtain ⟨⟨t', C'⟩, hq', rfl⟩ := Option.map_eq_some_iff.1 hB'
  rw [hq] at hq'
  cases hq'
  exact hmin q t C hq

end
end VInductDecl'

section
variable {E₂ e₂ : VEnv} {D : VInductDecl'} {K : List Name} {R : VIndRestore}

/-- **`RecTypeBridge` from the entrywise motive/minor defeqs.**  `WholeTypeBridge` §D fed by §F's two
lemmas — i.e. `ValRestGeneral` §5's premise reduced to exactly the data §T5 and §T6 produce, with no
block-level repackaging left for the caller. -/
theorem VIndRestore.recTypeBridge_of_entries
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : (R.csubst D K).WFD E₂ e₂ D.recUvars) (he₂ : e₂.Ordered)
    (hmot : ∀ t : Nat, t < D.nm → ∃ u, e₂.IsDefEq D.recUvars
      (((D.motives.map (VExpr.substC · (R.csubst D K))).take t).reverse
        ++ ((D.atRecTele D.params).map (VExpr.substC · (R.csubst D K))).reverse)
      ((D.motiveType t).substC (R.csubst D K))
      ((D.motiveTypeR R t).substC (R.csubst D K)) (.sort u))
    (hmin : ∀ (q t : Nat) (C : VIndCtor), D.ctorsAll[q]? = some (t, C) → ∃ u,
      e₂.IsDefEq D.recUvars
        (((D.minors.map (VExpr.substC · (R.csubst D K))).take q).reverse
          ++ ((D.motives.map (VExpr.substC · (R.csubst D K))).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · (R.csubst D K))).reverse))
        ((D.minorType q t C).substC (R.csubst D K))
        ((D.minorTypeR R q t C).substC (R.csubst D K)) (.sort u))
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
    R.RecTypeBridge D K e₂ :=
  VIndRestore.recTypeBridge_of_blocks hsrc hσ he₂
    (VInductDecl'.motives_teleDefEq_of_entries hmot)
    (VInductDecl'.minors_teleDefEq_of_entries hmin) hbody

end

/-! ## §G Brief item (3): §E's `hnoc` in general

`WholeTypeBridge` §E is gated on one σ-identity per companion constructor,
`(C.typeR D R j).substC (R.csubst D K) = C.typeR D R j`, and §6 note 3 of that handoff records it as
discharged at `ntreeAux` by `decide` but **not proved in general**, wanting
"`substC_tyAppR_free`-style `NoCSubst` facts on `C.params`, `C.fieldTypesR` and `C.args`".

That is exactly right, and here it is.  `VIndCtor.typeR` is
`mkPi (C.params ++ C.fieldTypesR D R) (D.tyAppR R j C.fields.length C.args)`, so the identity is:
the two telescope blocks are `σ`-invariant, and the restored head is.  The head needs
`VIndRestore.substC_tyAppR_free` at a **general** `σ` rather than at `R.csubstTy D K`; the general form
is `VIndRestore.SubstFree` (`NestedRules.lean` §7.4), whose `tyName`/`tyArgs` clauses are precisely
`substC_tyAppR_free`'s `hnn`/`hna`.  So §G costs one restatement and one `mkPi` computation. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {C : VIndCtor} {j : Nat}

/-- **`substC_tyAppR_free` at a general `σ`**, from `SubstFree` instead of the two `csubstTy`-specific
clauses.  The unprimed twin of `NestedRules.lean` §7.4's `substC_tyAppR'`. -/
theorem substC_tyAppR_of_substFree (hfr : R.SubstFree D σ) (j k : Nat) (args : List VExpr) :
    (D.tyAppR R j k args).substC σ = D.tyAppR R j k (args.map (VExpr.substC · σ)) := by
  rw [VInductDecl'.tyAppR, VInductDecl'.tyAppH, VExpr.substC_mkApp,
    VExpr.substC_const_none (hfr.tyName j), List.map_append, List.map_map]
  congr 2
  exact List.map_congr_left fun a ha =>
    ((hfr.tyArgs j a ha).liftN (n := k) (k := 0)).substC_eq

/-- **§E's `hnoc` AT ONE CONSTRUCTOR, IN GENERAL.**  The three `NoCSubst` families the handoff named,
and nothing else. -/
theorem substC_typeR_eq_of_noCSubst (hfr : R.SubstFree D σ)
    (hp : ∀ p ∈ C.params, p.NoCSubst σ)
    (hf : ∀ A ∈ C.fieldTypesR D R, A.NoCSubst σ)
    (ha : ∀ a ∈ C.args, a.NoCSubst σ) :
    (C.typeR D R j).substC σ = C.typeR D R j := by
  have htele : (C.params ++ C.fieldTypesR D R).map (VExpr.substC · σ)
      = C.params ++ C.fieldTypesR D R := by
    rw [show (C.params ++ C.fieldTypesR D R).map (VExpr.substC · σ)
        = (C.params ++ C.fieldTypesR D R).map id from
      List.map_congr_left fun A hA => by
        rcases List.mem_append.1 hA with h | h
        · exact (hp A h).substC_eq
        · exact (hf A h).substC_eq, List.map_id]
  have hargs : C.args.map (VExpr.substC · σ) = C.args := by
    rw [show C.args.map (VExpr.substC · σ) = C.args.map id from
      List.map_congr_left fun a h => (ha a h).substC_eq, List.map_id]
  rw [VIndCtor.typeR, VExpr.substC_mkPi, htele, substC_tyAppR_of_substFree hfr, hargs]

/-- **…and §E's whole `hnoc` family**, in the shape `ctorTypeBridge_iff_substC` and
`ctorTypeBridge_of_entries` consume. -/
theorem ctorTypeBridge_hnoc_of_noCSubst (hfr : R.SubstFree D (R.csubst D K))
    (hdata : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      (∀ p ∈ C.params, p.NoCSubst (R.csubst D K)) ∧
        (∀ A ∈ C.fieldTypesR D R, A.NoCSubst (R.csubst D K)) ∧
        (∀ a ∈ C.args, a.NoCSubst (R.csubst D K))) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      (C.typeR D R j).substC (R.csubst D K) = C.typeR D R j := by
  intro j T hT hK C hC
  obtain ⟨hp, hf, ha⟩ := hdata j T hT hK C hC
  exact substC_typeR_eq_of_noCSubst hfr hp hf ha

end
end VIndRestore

section
variable {env env₃ e₁ : VEnv} {D : VInductDecl'} {K : List Name} {R : VIndRestore}

/-- **`CtorTypeBridge` with §E's σ-identity discharged in general**, so the only per-block data left in
`WholeTypeBridge` §E.2 are its `hfld` at the companions and its **live** result-head defeq.  The three
`NoCSubst` families are syntactic and `decide`-able per block (see §H). -/
theorem VIndRestore.ctorTypeBridge_of_entries_noCSubst
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃)
    (henv₃ : env₃.Ordered) (he₁ : e₁.Ordered)
    (hσ : (R.csubst D K).WFD env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hfr : R.SubstFree D (R.csubst D K))
    (hdata : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ∀ C ∈ T.ctors,
      (∀ p ∈ C.params, p.NoCSubst (R.csubst D K)) ∧
        (∀ A ∈ C.fieldTypesR D R, A.NoCSubst (R.csubst D K)) ∧
        (∀ a ∈ C.args, a.NoCSubst (R.csubst D K)))
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
  VIndRestore.ctorTypeBridge_of_entries hD h₃ henv₃ he₁ hσ hown
    (VIndRestore.ctorTypeBridge_hnoc_of_noCSubst hfr hdata) hfld hres

end


/-! ## §H §G is not vacuous: its three `NoCSubst` families hold at `ntreeAux`, and the general route
reproduces the `decide`

`WholeTypeBridge` §F.1's `InductiveDeclExamples.ntree_typeR_noCSubst` establishes §E's σ-identity at
`ntreeAux` by a bare `decide` on the whole equation.  That is evidence the *conclusion* holds; it is not
evidence §G's premises are satisfiable, and "instantiate, don't admire" asks for the second.  So the
three families are discharged separately here and §G's general theorem is run on them, reproducing the
same conclusion **through the general route**. -/

namespace InductiveDeclExamples

/-- §G's three `NoCSubst` families at `ntreeAux`'s companion constructors. -/
theorem ntreeAux_typeR_noCSubst_data :
    ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → T.name ∈ ntreeK → ∀ C ∈ T.ctors,
      (∀ p ∈ C.params, p.NoCSubst (ntreeRestore.csubst ntreeAux ntreeK)) ∧
        (∀ A ∈ C.fieldTypesR ntreeAux ntreeRestore,
          A.NoCSubst (ntreeRestore.csubst ntreeAux ntreeK)) ∧
        (∀ a ∈ C.args, a.NoCSubst (ntreeRestore.csubst ntreeAux ntreeK)) := by
  intro j T hT hK C hC
  match j, hT with
  | 0, hT => cases hT; exact absurd hK (by decide)
  | 1, hT =>
    cases hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain rfl | rfl := hC
    · exact ⟨by decide, by decide, by decide⟩
    · exact ⟨by decide, by decide, by decide⟩
  | (_ + 2), hT => simp [ntreeAux] at hT

/-- **§E's σ-identity at `ntreeAux`, through §G rather than by `decide` on the whole equation.**  Same
statement as `InductiveDeclExamples.ntree_typeR_noCSubst`; different value, and the value is the
point. -/
theorem ntreeAux_typeR_noCSubst_general :
    ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → T.name ∈ ntreeK → ∀ C ∈ T.ctors,
      (C.typeR ntreeAux ntreeRestore j).substC (ntreeRestore.csubst ntreeAux ntreeK)
        = C.typeR ntreeAux ntreeRestore j :=
  VIndRestore.ctorTypeBridge_hnoc_of_noCSubst ntreeRestore_substFree ntreeAux_typeR_noCSubst_data

end InductiveDeclExamples

end Lean4Lean

/-! ## §Z Axiom lines -/
#print axioms Lean4Lean.VEnv.ctorConstsCR_wf_of_fldD
#print axioms Lean4Lean.VIndRestore.csubst_hbridgeD_of_fldD
#print axioms Lean4Lean.VIndRestore.fldK_of_fldD
#print axioms Lean4Lean.VIndRestore.fldD_of_fldK
#print axioms Lean4Lean.VIndRestore.fldD_iff_fldK
#print axioms Lean4Lean.VIndRestore.fldK_of_fldHead
#print axioms Lean4Lean.VIndRestore.fldD_of_fldHead
#print axioms Lean4Lean.VIndRestore.fldHead_of_betaD
#print axioms Lean4Lean.VIndRestore.fldD_of_betaD
#print axioms Lean4Lean.VIndRestore.csubst_hbridgeD_of_betaD
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_canFld
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_argsNoC
#print axioms Lean4Lean.VInductDecl'.motives_teleDefEq_of_entries
#print axioms Lean4Lean.VInductDecl'.minors_teleDefEq_of_entries
#print axioms Lean4Lean.VIndRestore.recTypeBridge_of_entries
#print axioms Lean4Lean.VIndRestore.substC_tyAppR_of_substFree
#print axioms Lean4Lean.VIndRestore.substC_typeR_eq_of_noCSubst
#print axioms Lean4Lean.VIndRestore.ctorTypeBridge_hnoc_of_noCSubst
#print axioms Lean4Lean.VIndRestore.ctorTypeBridge_of_entries_noCSubst
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_fldDischarge_witness
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_typeR_noCSubst_data
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_typeR_noCSubst_general
