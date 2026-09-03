/-
# `TeleCongr`: `HasArgs.congr_tele` **consumed**

`Theory/Inductive/NestedTele.lean` §T11/§T12.1/§T15 name `VEnv.HasArgs.congr_tele` and
`VEnv.TeleDefEq.instN` as the outstanding obstruction to obligation (B)'s assembly, and
`Theory/Inductive/CtorBeta.lean` §6d names the same pair as what stands between obligation (A)'s
`hbv` and a *derivation* of it.  **Both lemmas are already proved** (`NestedTele.lean:1516`,
`:1553`); what had no users was the composition.  This file supplies it.

Two things had to be built first, and neither is in the tree:

* `VEnv.TeleDefEq.of_isDefEqCtx` — `VIndCtor.WF.params_eq` (`Decl.lean:670`) is an
  **`IsDefEqCtx`**, and `congr_tele` consumes a **`TeleDefEq`**.  The two relations agree
  entrywise but recurse from *opposite ends* (`IsDefEqCtx` outward from its base, `TeleDefEq`
  from the telescope's front), so the bridge is not `induction` on either alone: it is an
  induction on the `IsDefEqCtx` with a `TeleDefEq` **accumulator**.
* `VEnv.TeleDefEq.substC` — `params_eq` lives in the source environment, `hbv` in the
  substituted one.

`docs/handoff-telecongr.md` records what is and is not claimed, and in particular that the
`Faithful` shortcut the relayed brief offered is **unavailable at (A)** (`Faithful`'s three
clauses are all guarded by `T.name ∈ K`, and (A)'s field β-step sits at `T.name ∉ K`).
-/
import Lean4Lean.Theory.Inductive.CtorBeta
import Lean4Lean.Theory.Inductive.RecTyped

namespace Lean4Lean

/-! ## §1 `IsDefEqCtx` → `TeleDefEq`, and `TeleDefEq` under `substC`

Neither is in the tree, and the first is the load-bearing one: without it
`VIndCtor.WF.params_eq` cannot reach `congr_tele` at all. -/

namespace VEnv
variable {env env₀ env₁ : VEnv} {U : Nat} {σ : CSubst}

/-- **`IsDefEqCtx` is a `TeleDefEq`, read from the other end.**  The accumulator `Bs`/`Bs'` is
what makes the two recursion directions meet: `IsDefEqCtx.succ` adds its entry at the *outside*
(so at the *front* of the reversed telescope's tail), and `TeleDefEq.cons` consumes it at the
front, typed in exactly the context `IsDefEqCtx.succ` types it in. -/
theorem TeleDefEq.of_isDefEqCtx_aux :
    ∀ {Γ₁ Γ₂ : List VExpr}, env.IsDefEqCtx U [] Γ₁ Γ₂ →
      ∀ {Bs Bs' : List VExpr}, env.TeleDefEq U Γ₁ Bs Bs' →
        env.TeleDefEq U [] (Γ₁.reverse ++ Bs) (Γ₂.reverse ++ Bs')
  | _, _, .zero, _, _, h => by simpa using h
  | _, _, .succ hC hA, _, _, h => by
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact TeleDefEq.of_isDefEqCtx_aux hC (.cons hA h)

/-- **The bridge, at the shape `VIndCtor.WF.params_eq` has it.** -/
theorem TeleDefEq.of_isDefEqCtx {As As' : List VExpr}
    (h : env.IsDefEqCtx U [] As.reverse As'.reverse) : env.TeleDefEq U [] As As' := by
  have := TeleDefEq.of_isDefEqCtx_aux h (Bs := []) (Bs' := []) .nil
  simpa using this

/-- **`TeleDefEq` under constant substitution.**  `IsDefEq.substC` per entry; the `rfl` case
survives because a syntactically unchanged entry stays unchanged after `substC`. -/
theorem TeleDefEq.substC (hσ : σ.WF env₀ env₁ U) :
    ∀ {Γ As As' : List VExpr}, env₀.TeleDefEq U Γ As As' →
      env₁.TeleDefEq U (Γ.map (VExpr.substC · σ)) (As.map (VExpr.substC · σ))
        (As'.map (VExpr.substC · σ))
  | _, _, _, .nil => .nil
  | _, _, _, .rfl h => by
    simpa using TeleDefEq.rfl (TeleDefEq.substC hσ h (Γ := _ :: _))
  | _, _, _, .cons hA h => by
    simpa using TeleDefEq.cons (hA.substC hσ) (TeleDefEq.substC hσ h (Γ := _ :: _))

/-- **Weakening a closed telescope's `TeleDefEq` from `[]` into any context.**
`TeleDefEq.weakN` at `Ctx.LiftN Γ.length 0 [] Γ`, with both `liftTele`s removed by closedness —
which is the form both consumers need, since `hbv` and `hAs` name their telescopes *unlifted*. -/
theorem TeleDefEq.weak0 (henv : env.Ordered) {As As' : List VExpr} (Γ : List VExpr)
    (hcl : VExpr.ClosedTele As 0) (hcl' : VExpr.ClosedTele As' 0)
    (h : env.TeleDefEq U [] As As') : env.TeleDefEq U Γ As As' := by
  have := TeleDefEq.weakN (n := Γ.length) (k := 0) henv (Ctx.LiftN.zero Γ (by simp)) h
  rwa [hcl.liftTele_eq (Nat.le_refl 0), hcl'.liftTele_eq (Nat.le_refl 0), List.append_nil] at this

end VEnv

/-! ## §2 `csubstTy` is fresh in the **pre-block** environment

`VIndRestore.csubst_freshIn` (`NestedRules.lean:1260`) needs all three staging successes because
`csubst`'s domain includes the companions' constructor and recursor names.  `csubstTy`'s domain is
only the companion *type* names, so its first branch alone suffices: **one** staging equation, and
`ctorConstsCR_wf_of_betaD` already carries exactly that one (`h₃`).

The environment matters and is easy to get wrong: this is freshness in `env`, the environment
*before* `addIndTypes`.  `(R.csubstTy D K).FreshIn env₃` is **false** whenever `K` names a member
of `D`, because `env₃` declares precisely the names `csubstTy` substitutes. -/

namespace VIndRestore

/-- **`csubstTy` is fresh in the pre-block environment**, from the type-staging success alone. -/
theorem csubstTy_freshIn {env E₁ : VEnv} {R : VIndRestore} {D : VInductDecl'}
    {K : List Lean.Name} (h₁ : env.addIndTypes D = some E₁) :
    (R.csubstTy D K).FreshIn env := by
  intro c ci hc
  cases hn : R.csubstTy D K c with
  | none => rfl
  | some v =>
    obtain ⟨j, T, hT, rfl, -, -⟩ := csubstTy_dom hn
    have := (VEnv.addConstList_fresh h₁).1 T.name (by
      rw [VInductDecl'.typeConsts_names]
      exact List.mem_map.2 ⟨_, List.mem_of_getElem? hT, rfl⟩)
    rw [this] at hc; exact absurd hc nofun

end VIndRestore

/-! ## §3 Obligation (A)'s `hbv`, **derived**

`CtorBeta.lean` §7's `hbeta` asks for five data at every companion-pointing recursive field, and
its second component is

    e₁.HasArgs D.uvars Γfld D.params (VExpr.bvars (r.binders.length + i) D.np)

where `Γfld` carries the constructor's **own** parameter copy, substituted:
`(C.params.map (·.substC σ)).reverse` at its bottom.  §6d proves the spine is in scope and says
in as many words that supplying `hbv` "still needs the conversion between the substituted
`C.params` that sits in the context and the `D.params` §8.8 asks for".

That conversion is now available, and `hbv` is a **theorem**.  What it costs: no `Faithful`, no
`PiInv`, no `np` bound, no new datum.  `hclD` and `hσD` are the two facts about `D.params` alone,
and `..._of_wf` derives both from `D.WF env` plus one staging equation.

The statement is generic in the block `Δ` sitting above the parameters, so the same theorem serves
§7 (`Δ` = the field's binders and the earlier fields) and any other field-context shape. -/

namespace VIndCtor
variable {env env₃ e₁ : VEnv} {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {j : Nat}
  {σ : CSubst}

/-- **The parameter spine of a constructor's field context, typed against `D.params`.**

`HasArgs.bvars` types it against the constructor's own substituted copy; `params_eq` +
§1's three bridges + `congr_tele` move it to the block's.  `Δ` is any block of binders sitting
above the parameters. -/
theorem WF.hasArgs_params_bvars (he₁ : e₁.Ordered) (hσ : σ.WF env₃ e₁ D.uvars)
    (hCwf : VIndCtor.WF env₃ D j T C)
    (hclD : VExpr.ClosedTele D.params 0)
    (hσD : D.params.map (VExpr.substC · σ) = D.params) (Δ : List VExpr) :
    e₁.HasArgs D.uvars (Δ ++ (C.params.map (VExpr.substC · σ)).reverse)
      D.params (VExpr.bvars Δ.length D.np) := by
  have hCp : OnCtx C.params.reverse (env₃.IsType D.uvars) := hCwf.params_eq.isType
  have hclC : VExpr.ClosedTele (C.params.map (VExpr.substC · σ)) 0 := by
    refine VExpr.ClosedTele.of_onCtx (U := D.uvars) (Γ := []) he₁ ?_
    have := VEnv.OnCtx.substC hσ hCp
    rw [List.map_reverse] at this; simpa using this
  -- the telescope conversion, moved into `e₁` and then into the field context
  have h0 : e₁.TeleDefEq D.uvars [] (C.params.map (VExpr.substC · σ)) D.params := by
    have := (VEnv.TeleDefEq.of_isDefEqCtx (As := C.params) (As' := D.params)
      (by simpa using hCwf.params_eq)).substC hσ (σ := σ)
    rwa [List.map_nil, hσD] at this
  have hΓ := VEnv.TeleDefEq.weak0 he₁ (Δ ++ (C.params.map (VExpr.substC · σ)).reverse)
    hclC hclD h0
  -- the spine, typed against the constructor's own copy, then converted
  have hbv := VEnv.HasArgs.bvars (env := e₁) (U := D.uvars) (Δ := Δ)
    (As := C.params.map (VExpr.substC · σ)) (Γ₀ := [])
  rw [List.append_nil, hclC.liftTele_eq (Nat.le_refl 0), List.length_map,
    hCwf.params_len] at hbv
  exact hbv.congr_tele he₁ hΓ

/-- …with the two `D.params` facts discharged from the block's own well-formedness and the
type-staging equation.  **No hypothesis here that `ctorConstsCR_wf_of_betaD` does not already
carry, except `env.Ordered`** — which every caller has, since it is what `env₃.Ordered` is
derived from. -/
theorem WF.hasArgs_params_bvars_of_wf {R : VIndRestore} {K : List Lean.Name}
    (henv : env.Ordered) (he₁ : e₁.Ordered) (hD : D.WF env)
    (h₃ : env.addIndTypes D = some env₃)
    (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hCwf : VIndCtor.WF env₃ D j T C)
    (Δ : List VExpr) :
    e₁.HasArgs D.uvars
      (Δ ++ (C.params.map (VExpr.substC · (R.csubstTy D K))).reverse)
      D.params (VExpr.bvars Δ.length D.np) :=
  WF.hasArgs_params_bvars he₁ hσ hCwf
    (VExpr.ClosedTele.of_onCtx (U := D.uvars) (Γ := []) henv (by simpa using hD.params))
    (VEnv.OnCtx.substC_eq_tele henv (VIndRestore.csubstTy_freshIn h₃) (Δ := [])
      (by simpa using hD.params)) Δ

end VIndCtor

/-! ## §4 …and therefore §7's datum bundle is **four** components, not five

`VEnv.ctorConstsCR_wf_of_betaD` (`CtorBeta.lean:544`) asks for five things at each
companion-pointing recursive field.  The restatement below asks for **four** — `hbv` deleted —
and is proved by feeding §3 into the original.  The only hypothesis it adds is `henv`
(`env.Ordered`), which every caller already has: it is what `henv₃` is derived from
(`CtorBeta.lean:625` computes `henv₂` from `henv₁`).  `hfresh` is **not** added: §2 derives it
from `h₃`, which the original already takes.

This is what makes §3 a **discharge** rather than a reduction: the component is gone from the
bundle, and no datum was added in its place.  §5 checks that the resulting premise set is still
jointly inhabited at a real parameterised block. -/

/-- **Obligation (A) at `D.np > 0`, with `hbv` derived rather than assumed.**

Identical to `VEnv.ctorConstsCR_wf_of_betaD` except that `hbeta`'s second component — the
parameter spine `hbv` — has been deleted, and `henv : env.Ordered` added. -/
theorem VEnv.ctorConstsCR_wf_of_betaD₄ {env env₃ e₁ : VEnv} {D : VInductDecl'}
    {K : List Lean.Name} {R : VIndRestore}
    (henv : env.Ordered) (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃)
    (henv₃ : env₃.Ordered) (he₁ : e₁.Ordered)
    (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars) (hown : R.OwnId D K)
    (hnd : D.blockNames.Nodup) (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np)
    (hnn : ∀ i, R.csubstTy D K (R.tyName i) = none)
    (hna : ∀ i, ∀ a ∈ R.tyArgs i, a.NoCSubst (R.csubstTy D K))
    (hcan : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T → T.name ∉ K →
      C ∈ T.ctors → ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
        F.recArg = some r → ¬ VExpr.NoConsts K F.type →
        F.type = r.canonType D i ∧ (∀ B ∈ r.binders, VExpr.NoConsts K B) ∧
          (∀ a ∈ r.args, a.NoCSubst (R.csubstTy D K)) ∧
          ∃ T' : VIndType, D.types[r.idx]? = some T')
    (hbeta : ∀ (j : Nat) (T : VIndType) (C : VIndCtor), D.types[j]? = some T → T.name ∉ K →
      C ∈ T.ctors → ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
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
          VExpr.instAll B' r.args = VExpr.sort v) :
    ∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2 := by
  refine VEnv.ctorConstsCR_wf_of_betaD hD h₃ henv₃ he₁ hσ hown hnd hlw hcl hnn hna hcan ?_
  intro j T C hT hK hCT i F r hF hr hnc T' hT' hK'
  obtain ⟨As, B, B', v, hOn, hbody, hpi, hAs, hsort⟩ :=
    hbeta j T C hT hK hCT i F r hF hr hnc T' hT' hK'
  refine ⟨As, B, B', v, hOn, ?_, hbody, hpi, hAs, hsort⟩
  have hCwf : VIndCtor.WF env₃ D j T C := hD.ctors env₃ h₃ j T hT C hCT
  have hi : i ≤ C.fields.length := Nat.le_of_lt (by
    simpa using (List.getElem?_eq_some_iff.1 hF).1)
  have h := hCwf.hasArgs_params_bvars_of_wf henv he₁ hD h₃ hσ
    ((r.binders.map (VExpr.substC · (R.csubstTy D K))).reverse ++
      (((C.fields.map (·.type)).map (VExpr.substC · (R.csubstTy D K))).take i).reverse)
  rw [List.append_assoc] at h
  simpa [Nat.min_eq_left hi] using h

/-! ## §5 Anti-vacuity: §4's premise set is still jointly inhabited at `ntreeAux`

`docs/vacuity-ledger.md` rows 195/199b/205 are three instances of the same failure: a statement
compiling with a clean axiom line while its hypothesis set is empty, twice because a
*strengthening* silently emptied a premise.  Deleting `hbv` from `hbeta` **weakens** the premise
(the bundle asks for less), so it cannot empty it — but adding `henv` could, and the check is
cheap, so it is run rather than argued.

§4 is instantiated at `ntreeAux` — `NTree`/`List`, `D.np = 1`, a real nested block with a
companion-pointing recursive field — at the same standard as `CtorBeta.lean` §7b: the four
staging equations hypothesised, everything else supplied.  The `hbeta` witness is now **four**
components; the `HasArgs` line §7b had to build by hand is gone. -/

namespace InductiveDeclExamples

section
variable {env₁ env₂ env₃ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁) (henv₁ : env₁.Ordered)
variable (h₂ : env₁.addIndTypes ntreeAux = some env₂)
variable (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃)

include h henv₁ h₂ h₃ in
/-- **Obligation (A) at `ntreeAux` through §4** — the four-component bundle, at a real
parameterised nested block.  Compare `ntreeAux_ctorConstsCR_wf_of_betaD` (`CtorBeta.lean:626`):
the `hbv` component is gone from the witness, and nothing replaced it. -/
theorem ntreeAux_ctorConstsCR_wf_of_betaD₄ :
    ∀ c ∈ ntreeAux.ctorConstsCR ntreeRestore ntreeK, VConstant.WF env₃ c.2 := by
  have henv₂ : env₂.Ordered :=
    VInductDecl'.addIndTypes_ordered henv₁ (ntreeAux_WF h) h₂
  have henv₃ : env₃.Ordered :=
    VEnv.addConstList_ordered henv₁ (VEnv.addInductR_typeConstsC_wf (ntreeAux_WF h)) h₃
  have hL := list_const₃ h h₃
  have hN := ntree_const₃ h₃
  refine VEnv.ctorConstsCR_wf_of_betaD₄ henv₁ (ntreeAux_WF h) h₂ henv₂ henv₃
    (ntree_csubstTy ▸ ntreeSubst_WF h henv₁ h₂ h₃) ntreeRestore_ownId (by decide)
    ntreeRestore_tyVal_levelWF ntreeRestore_tyArgs_closed
    ntreeRestore_csubstTy_tyName ntreeRestore_tyArgs_noCSubst ?_ ?_
  · rintro j T C hT hK hC i F r hF hr hnc
    match j, hT with
    | 0, hT =>
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      match i, hF with
      | 0, hF => cases hF; exact absurd hr nofun
      | 1, hF => cases hF; cases hr; exact ⟨rfl, nofun, nofun, _, rfl⟩
      | (_ + 2), hF => simp [ntreeNode] at hF
    | 1, hT => cases hT; exact absurd (by decide) hK
    | (_ + 2), hT => simp [ntreeAux] at hT
  · rintro j T C hT hK hC i F r hF hr hnc T' hT' hK'
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

end

end InductiveDeclExamples

/-! ## §6 Obligation (B)'s `hAs`, **derived** — §T12.1's chain, composed

`NestedTele.lean` §T12.1 sets out the de Bruijn arithmetic and §T13 closes its two side
conditions, and both sections say in as many words that the composition is not performed there.
This is it.

Reading the chain off §T12.1, with `nf := C.fields.length`, `nr := (D.ihTypes q C).length`,
`off := D.nm + q` and `k := nr + nf + off`:

1. `instAt_ctor_hpi` (§T10) fixes `As = instAllTele (D.atRecTele (C.fieldTypesR D R)) (bvars k D.np) 0`;
2. `instAllTele_bvars_lift` + `atRecTele_fieldTypesR_closedTele` turn that into `liftTele k … 0`;
3. `HasArgs.bvars` types the spine against `liftTele (nr+nf) (liftTele off srcF 0) 0`, which
   `liftTele_collapse₂` collapses to `liftTele (off+(nr+nf)) srcF 0` — **the same offset**, as
   §T12.1 predicted;
4. `TeleDefEq.weakN` lifts `MinorFldDefEq` over the field/ih block and
   `atRecTele_fieldTypesR_substC_eq` identifies its right endpoint with the *unsubstituted*
   restored telescope;
5. `congr_tele` closes it.

The σ-identity on `D.atRecTele D.params` is needed because `MinorFldDefEq` states its context
with the parameter block **substituted** and `MinorCtorHargs` states it **raw**. -/

namespace VIndRestore
variable {e : VEnv} {R : VIndRestore} {D : VInductDecl'} {C : VIndCtor} {σ : CSubst} {q : Nat}

/-- **`MinorCtorHargs`'s `hAs` conjunct, at the `As` `instAt_ctor_hpi` delivers.**

`hfld` is `MinorFldDefEq`, which obligation (B)'s closure already demands at *every* entry — so
this consumes nothing new from the caller.  The other three inputs are §T13's two side conditions
plus the parameter-block σ-identity. -/
theorem minorCtor_hAs (he : e.Ordered) (hfld : R.MinorFldDefEq D σ e q C)
    (hσp : (D.atRecTele D.params).map (VExpr.substC · σ) = D.atRecTele D.params)
    (hσf : (D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ)
      = D.atRecTele (C.fieldTypesR D R))
    (hclF : VExpr.ClosedTele (D.atRecTele (C.fieldTypesR D R)) D.np) :
    e.HasArgs D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      (VExpr.instAllTele (D.atRecTele (C.fieldTypesR D R))
        (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np) 0)
      (VExpr.bvars (D.ihTypes q C).length C.fields.length) := by
  -- lengths: the substituted source field telescope has `C.fields.length` entries
  have hlensrc : ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)).length
      = C.fields.length := by
    simp [VInductDecl'.length_atRecTele]
  -- step 2: the existential `As` is a `liftTele`
  rw [VExpr.instAllTele_bvars_lift
    (n := D.np) (j := (D.ihTypes q C).length + C.fields.length + (D.nm + q)) (m := 0)
    (by simpa using hclF)]
  -- step 3: the spine, typed against the source field telescope
  have hbv := VEnv.HasArgs.bvars (env := e) (U := D.recUvars)
    (Δ := ((D.ihTypes q C).map (VExpr.substC · σ)).reverse)
    (As := VExpr.liftTele (D.nm + q)
      ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)) 0)
    (Γ₀ := ((D.minors.map (VExpr.substC · σ)).take q).reverse
      ++ ((D.motives.map (VExpr.substC · σ)).reverse ++ (D.atRecTele D.params).reverse))
  rw [List.length_reverse, List.length_map, VExpr.length_liftTele, hlensrc,
    VExpr.liftTele_collapse₂] at hbv
  -- step 4: `MinorFldDefEq`, lifted over the field/ih block, right endpoint desubstituted
  rw [VIndRestore.MinorFldDefEq, hσp, hσf] at hfld
  have hw := VEnv.TeleDefEq.weakN (n := (D.ihTypes q C).length + C.fields.length) (k := 0) he
    (Ctx.LiftN.zero (((D.ihTypes q C).map (VExpr.substC · σ)).reverse
      ++ (VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)) 0).reverse) (by
        simp [VExpr.length_liftTele, hlensrc])) hfld
  rw [VExpr.liftTele_collapse₂, VExpr.liftTele_collapse₂] at hw
  -- step 5
  have hcong := hbv.congr_tele he hw
  rw [show D.nm + q + ((D.ihTypes q C).length + C.fields.length)
      = (D.ihTypes q C).length + C.fields.length + (D.nm + q) from by omega] at hcong
  simpa [List.reverse_append, List.append_assoc] using hcong

/-! ### §6b …and `MinorCtorHargs` from **two** components, not four

`instAt_ctor_hpi` (§T10) fixes `B`, `As` and `B'` outright, so `hpi` is not data; §6 then closes
`hAs`.  What is left of `MinorCtorHargs` is `hcbody` and `hfun` — the two `hargs`-shaped data
`RecTyped.lean` §5 already names as the open obligation.

The `Faithful` cost is real and is **available here**, unlike at (A): `hminD` is demanded only at
`T.name ∈ K`, which is exactly `Faithful.ctor_agree`'s guard. -/

/-- **`MinorCtorHargs` with `hpi` and `hAs` both derived.**

`hlen`/`hagree` are `Faithful.ctor_agree` read through `VIndCtor.WF.params_len`; `hfld` is the
`MinorFldDefEq` obligation (B)'s closure already demands at every entry; `hσp`/`hσf`/`hclF` are
§T16.2's parameter σ-identity and §T13's two side conditions.  `hcbody` and `hfun` are the only
data left. -/
theorem minorCtorHargs_of_hargs (he : e.Ordered) {t npJ : Nat} {ci : VConstant}
    (hlen : D.params.length = C.params.length)
    (hagree : R.instAt D npJ t ci.type = C.typeR D R t)
    (hfld : R.MinorFldDefEq D σ e q C)
    (hσp : (D.atRecTele D.params).map (VExpr.substC · σ) = D.atRecTele D.params)
    (hσf : (D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ)
      = D.atRecTele (C.fieldTypesR D R))
    (hclF : VExpr.ClosedTele (D.atRecTele (C.fieldTypesR D R)) D.np)
    (hcbody : e.HasType D.recUvars ((D.atRecTele D.params).reverse)
      (D.atRec (R.ctorBody D t C))
      (D.atRec (VExpr.instAll (VExpr.splitPis npJ (ci.type.instL (R.tyLvls t))).2
        (R.tyArgs t))))
    (hfun : e.HasType D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      ((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a)).map (VExpr.substC · σ)))
      (.forallE (VExpr.instAll
          (VExpr.instAll (D.tyAppR' R t C.fields.length (D.atRecTele C.args))
            (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)
            (C.fieldTypesR D R).length)
          (VExpr.bvars (D.ihTypes q C).length C.fields.length))
        (.sort D.elimLvl))) :
    R.MinorCtorHargs D σ e q t C :=
  ⟨_, _, _, hcbody, VIndRestore.instAt_ctor_hpi hlen hagree,
    minorCtor_hAs he hfld hσp hσf hclF, hfun⟩

/-- **…and with §T13's two side conditions CALLED rather than hypothesised.**

`minorCtorHargs_of_hargs` takes `hσf` and `hclF` as facts; this takes their producers' inputs
instead, so the chain `§T13 → §T12.1 → §6 → MinorCtorHargs` is composed end to end and nothing is
asserted.  `atRecTele_fieldTypesR_closedTele` and `atRecTele_fieldTypesR_substC_eq` were the two
declarations in the relayed zero-user list that stayed zero-user after §6b; they are consumed here.

Every hypothesis is either one `recConstsR_wf_of_recHargsD` already carries (`henv`, `hD`, `hcl`),
a `Faithful` clause (available at `T.name ∈ K`, which is where `hminD` is demanded), or a side
condition on the restoration data that is `decide`-able at a witness (`hargsF`). -/
theorem minorCtorHargs_of_hargs' {env : VEnv} {env₃ : VEnv} {t npJ : Nat} {T : VIndType}
    {ci : VConstant} (he : e.Ordered) (henv : env.Ordered) (henv₃ : env₃.Ordered)
    (hD : D.WF env) (hfresh : σ.FreshIn env)
    (hCwf : VIndCtor.WF env₃ D t T C)
    (hci : env.constants (R.ctorName C.name) = some ci)
    (hagree : R.instAt D npJ t ci.type = C.typeR D R t)
    (hcl : ∀ j, ∀ a ∈ R.tyArgs j, a.ClosedN D.np)
    (hargsF : ∀ a ∈ R.tyArgs t, a.NoCSubst σ)
    (hfld : R.MinorFldDefEq D σ e q C)
    (hcbody : e.HasType D.recUvars ((D.atRecTele D.params).reverse)
      (D.atRec (R.ctorBody D t C))
      (D.atRec (VExpr.instAll (VExpr.splitPis npJ (ci.type.instL (R.tyLvls t))).2
        (R.tyArgs t))))
    (hfun : e.HasType D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      ((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a)).map (VExpr.substC · σ)))
      (.forallE (VExpr.instAll
          (VExpr.instAll (D.tyAppR' R t C.fields.length (D.atRecTele C.args))
            (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)
            (C.fieldTypesR D R).length)
          (VExpr.bvars (D.ihTypes q C).length C.fields.length))
        (.sort D.elimLvl))) :
    R.MinorCtorHargs D σ e q t C := by
  have hlen : D.params.length = C.params.length := by rw [hCwf.params_len]
  refine minorCtorHargs_of_hargs he hlen hagree hfld
    (VInductDecl'.atRecTele_params_substC_eq henv hD hfresh)
    (VIndRestore.atRecTele_fieldTypesR_substC_eq henv hfresh hci hargsF hlen hagree)
    (VIndCtor.atRecTele_fieldTypesR_closedTele hcl ?_) hcbody hfun
  have hsrc := VExpr.closedTele_append.1 (hCwf.tele_closed henv₃)
  rw [Nat.zero_add, hCwf.params_len] at hsrc
  exact hsrc.2

end VIndRestore

/-! ## §7 Anti-vacuity for (B): the side conditions hold where the telescope MOVES

Row 205's failure is the one to guard against here, and it is specific: the (B) stream's first
closure took a hypothesis that was **jointly unsatisfiable at every real nested block**, and it
compiled with a clean axiom line.  §6b's five non-data hypotheses are all *about* the entry
`(q, t, C)`, so the question is whether they hold together at an entry that actually carries
content — not at the degenerate one.

`ntreeAux.ctorsAll = [(0, ntreeNode), (1, nlistNil), (1, nlistCons)]`.  The entry at `q = 1` is
`nlistNil`, which has **no fields** — `RecTyped.lean`'s `ntree_minorFld_nil` supplies
`MinorFldDefEq` there for free and discloses it as degenerate, and at no fields `hAs` is `.nil`
and §6 says nothing.  So the check is run at **`q = 2`, `nlistCons`**, the companion-member
constructor with two recursive fields, where the restored telescope genuinely differs from the
source one (`ntree_nlistCons_fieldTypesR_ne`).

**What is established** (`ntree_minorCtorHargs_sides_at_cons`): all five non-data hypotheses of
§6b hold *simultaneously* there, at `npJ = 1` from the block's own `Faithful` witness.
**What is not**: `hfld`, `hcbody` and `hfun`.  `hfld` is `MinorFldDefEq`, a bundle member (B)'s
closure demands and which is open at the moving entry; `hcbody`/`hfun` are `hargs`.  So §6b is a
**reduction of `MinorCtorHargs` from four components to two**, not a discharge of (B) — graded the
way `RecTyped.lean` §6c grades its own. -/

namespace InductiveDeclExamples

/-- **The entry the check is run at is not the degenerate one**: at `nlistCons` the restored field
telescope differs from the source one, so `MinorFldDefEq` there is not `TeleDefEq.refl` and §6's
`congr_tele` step is doing real work. -/
theorem ntree_nlistCons_fieldTypesR_ne :
    nlistCons.fieldTypesR ntreeAux ntreeRestore ≠ nlistCons.fields.map (·.type) := by
  decide

/-- **§6b's five non-data hypotheses, jointly, at `q = 2` / `nlistCons`.**

`hfld`, `hcbody` and `hfun` are deliberately absent — they are the open data.  Everything §6b
needs *besides* them is exhibited at one block, one `R`, one `σ`, one entry. -/
theorem ntree_minorCtorHargs_sides_at_cons {env₁ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁) :
    ntreeAux.ctorsAll[2]? = some (1, nlistCons) ∧
      (∃ T : VIndType, ntreeAux.types[1]? = some T ∧ T.name ∈ ntreeK) ∧
      ntreeAux.params.length = nlistCons.params.length ∧
      (∃ ci : VConstant, env₁.constants (ntreeRestore.ctorName nlistCons.name) = some ci ∧
        ntreeRestore.instAt ntreeAux 1 1 ci.type = nlistCons.typeR ntreeAux ntreeRestore 1) ∧
      (ntreeAux.atRecTele ntreeAux.params).map
          (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK))
        = ntreeAux.atRecTele ntreeAux.params ∧
      (ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore)).map
          (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK))
        = ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore) ∧
      VExpr.ClosedTele
        (ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore)) ntreeAux.np ∧
      (∀ a ∈ ntreeRestore.tyArgs 1,
        a.NoCSubst (ntreeRestore.csubst ntreeAux ntreeK)) ∧
      (∀ j, ∀ a ∈ ntreeRestore.tyArgs j, a.ClosedN ntreeAux.np) := by
  refine ⟨rfl, ⟨_, rfl, by decide⟩, rfl, ?_, rfl, rfl,
    ⟨⟨trivial, Nat.zero_lt_one⟩, ⟨trivial, trivial, Nat.one_lt_two⟩, trivial⟩, ?_,
    ntree_tyArgs_closedN_np⟩
  · obtain ⟨ci, hci, -, hagree⟩ :=
      (ntreeRestore_faithful h).ctor_agree 1 _ rfl (by decide) nlistCons
        (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨ci, hci, hagree⟩
  · intro a ha
    simp only [ntreeRestore] at ha
    simp only [List.mem_singleton, if_pos] at ha
    subst ha
    exact ⟨rfl, trivial⟩

end InductiveDeclExamples

end Lean4Lean

/-! ## §8 Axiom lines

Read off the declarations' own namespaces, not composed from the path. -/
#print axioms Lean4Lean.VEnv.TeleDefEq.of_isDefEqCtx_aux
#print axioms Lean4Lean.VEnv.TeleDefEq.of_isDefEqCtx
#print axioms Lean4Lean.VEnv.TeleDefEq.substC
#print axioms Lean4Lean.VEnv.TeleDefEq.weak0
#print axioms Lean4Lean.VIndRestore.csubstTy_freshIn
#print axioms Lean4Lean.VIndCtor.WF.hasArgs_params_bvars
#print axioms Lean4Lean.VIndCtor.WF.hasArgs_params_bvars_of_wf
#print axioms Lean4Lean.VEnv.ctorConstsCR_wf_of_betaD₄
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_ctorConstsCR_wf_of_betaD₄
#print axioms Lean4Lean.VIndRestore.minorCtor_hAs
#print axioms Lean4Lean.VIndRestore.minorCtorHargs_of_hargs
#print axioms Lean4Lean.InductiveDeclExamples.ntree_nlistCons_fieldTypesR_ne
#print axioms Lean4Lean.InductiveDeclExamples.ntree_minorCtorHargs_sides_at_cons
#print axioms Lean4Lean.VIndRestore.minorCtorHargs_of_hargs'
