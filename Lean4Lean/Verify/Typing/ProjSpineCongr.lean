import Lean4Lean.Verify.Typing.ProjSpineInv

/-!
# `VEnv.ProjSpineCongr`, the last residual of `TrProj.uniq`

`Verify/Typing/ProjSpineInv.lean` reduces `TrProj.uniq` to `VEnv.ProjSpineCongr`: congruence
of `VInductDecl'.projTerm` in its parameter and index spines, at one record, one level list
and one subject.  This file attacks that residual.
-/

namespace Lean4Lean

open VExpr

/-! ## 1. Substituting definitionally equal spines into an arbitrary term

`VEnv.IsDefEq.instAllCongrSort` (`Theory/Inductive/StructureClosed.lean`) proves this for a
term whose type is a sort, and its docstring says the general statement is out of reach:
"the general statement would need `instAll B as ≡ instAll B as'` to even state its
conclusion — the same congruence one level up".

**That is a fact about `IsDefEq`, not about the theorem.**  At `IsDefEqU` the type is
existentially quantified, so the two β-steps are allowed to land at *different* types and
`VEnv.IsDefEqU.trans` glues them anyway.  The general version costs the same three lines and
one extra `VEnv.WF` (which `trans` needs and `IsDefEq.trans_l` does not). -/
theorem VEnv.IsDefEqU.instAllCongr {env : VEnv} {U : Nat} (henv : env.WF)
    {Γ As as as' : List VExpr} {b B : VExpr}
    (hDF : env.HasArgsDF U Γ As as as') (hr : env.HasArgs U Γ As as')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx (As.reverse ++ Γ) (env.IsType U))
    (hb : env.HasType U (As.reverse ++ Γ) b B) :
    env.IsDefEqU U Γ (VExpr.instAll b as) (VExpr.instAll b as') := by
  have hL : env.IsDefEqU U Γ ((mkLams As b).mkApp as) (VExpr.instAll b as) :=
    ⟨_, VEnv.IsDefEq.betaMkLams henv.ordered hΓ' hDF.left hb⟩
  have hR : env.IsDefEqU U Γ ((mkLams As b).mkApp as') (VExpr.instAll b as') :=
    ⟨_, VEnv.IsDefEq.betaMkLams henv.ordered hΓ' hr hb⟩
  have hmid : env.IsDefEqU U Γ ((mkLams As b).mkApp as) ((mkLams As b).mkApp as') :=
    ⟨_, VEnv.IsDefEq.mkAppDF hDF (VEnv.HasType.mkLams hΓ' hb)⟩
  exact (hL.symm.trans henv hΓ hmid).trans henv hΓ hR

/-! ## 2. `projTerm` as a substitution instance of one generic term

`VInductDecl'.projTerm_instAll` (`Theory/Inductive/Structure.lean`) already says `projTerm`
commutes with a whole substitution spine.  Read right-to-left at a spine of *variables* it
says something stronger: every `projTerm` is one fixed term — the projection of the last
variable, at the parameter and index variables — with `ps ++ ιs ++ [e]` substituted in.

That is what turns §1 into spine congruence: the two sides of `ProjSpineCongr` are `instAll`
of *the same* `b` at two spines, so nothing about `projTerm`'s internal structure (motives,
minor premises, `projArgs`) is ever unfolded again. -/

/-- The projection term at generic arguments: parameters at de Bruijn indices
`ni+np, …, ni+1`, indices at `ni, …, 1`, and the major premise at `0`. -/
def VInductDecl'.projGeneric (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (np ni i : Nat) : VExpr :=
  D.projTerm T C us (bvars (ni+1) np) (bvars 1 ni) i (.bvar 0)

theorem VInductDecl'.projTerm_eq_instAll_generic (D : VInductDecl') (T : VIndType)
    (C : VIndCtor) (us : List VLevel) (hcl : D.ProjClosed T C) {i : Nat}
    (hi : i < C.fields.length) {ps ιs : List VExpr} {e : VExpr}
    (hps : ps.length = D.np) (his : ιs.length = T.indices.length) :
    D.projTerm T C us ps ιs i e
      = VExpr.instAll (D.projGeneric T C us ps.length ιs.length i) (ps ++ ιs ++ [e]) 0 := by
  have hlen : (ιs ++ [e]).length = ιs.length + 1 := by simp
  have key : ∀ lo n : Nat, (bvars lo n).map (VExpr.instAll · (ps ++ ιs ++ [e]) 0)
      = ((bvars lo n).map (VExpr.instAll · ps (ιs.length + 1))).map
          (VExpr.instAll · (ιs ++ [e]) 0) := by
    intro lo n
    simp only [List.append_assoc, List.map_map, Function.comp_def]
    refine List.map_congr_left fun x _ => ?_
    rw [show ιs.length + 1 = 0 + (ιs ++ [e]).length from by simp]
    exact VExpr.instAll_append
  rw [VInductDecl'.projGeneric,
    D.projTerm_instAll T C us hcl hi (by simp [hps]) (by simp [his])]
  congr 1
  · -- the parameter block
    rw [key, VExpr.map_instAll_bvars_top (k := ιs.length + 1) (Nat.le_refl _) (by simp)]
    have hcancel : ∀ p : VExpr, VExpr.instAll (liftN (ιs.length + 1) p) (ιs ++ [e]) 0 = p := by
      intro p
      rw [show ιs.length + 1 = (ιs ++ [e]).length from hlen.symm]
      exact VExpr.instAll_liftN _ _ _
    simp [List.map_map, Function.comp_def, hcancel]
  · -- the index block
    rw [key, VExpr.map_instAll_bvars_lt (by omega), VExpr.map_instAll_bvars_mid rfl]
  · -- the major premise
    exact VExpr.instAll_bvar_zero.symm

/-! ## 3. The generic projection telescope, and the generic term's typing

`projGeneric` lives over the context `params ++ indices ++ [major]`.  This section shows that
context is well formed and that the generic term is well typed over it — the two hypotheses
§1 needs — from `projTerm_hasType` (`Verify/Typing/Lemmas.lean`) applied at a *variable*
spine.  `projTerm_hasType` is passed as a parameter (`hgen`) because it lives downstream. -/

/-- The generic projection telescope: the parameter telescope, the index telescope, and the
major premise `S.{us} p̄ ῑ` at the block's own variables. -/
def VInductDecl'.projTele (D : VInductDecl') (T : VIndType) (S : Lean.Name)
    (us : List VLevel) : List VExpr :=
  D.params.map (VExpr.instL us) ++ T.indices.map (VExpr.instL us) ++
    [(VExpr.const S us).mkApp (bvars T.indices.length D.np ++ bvars 0 T.indices.length)]

theorem VInductDecl'.projTele_reverse (D : VInductDecl') (T : VIndType) (S : Lean.Name)
    (us : List VLevel) :
    (D.projTele T S us).reverse =
      (VExpr.const S us).mkApp (bvars T.indices.length D.np ++ bvars 0 T.indices.length)
        :: ((T.indices.map (VExpr.instL us)).reverse ++ (D.params.map (VExpr.instL us)).reverse) := by
  simp [VInductDecl'.projTele]

/-- **The generic projection telescope is a context, and the generic projection term is well
typed over it.**  Everything is an instance of machinery that already exists: the parameter
block's context-hood is `onCtxParams_instL`, the index block's and the major premise's is
`motiveCtx_wf` at the identity spine `bvars 0 D.np`, the two variable spines are
`HasArgs.bvars`, and the typing itself is `projTerm_hasType` at those spines. -/
theorem VInductDecl'.projGeneric_wf {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : VEnv.WF env) (H : env.IsStructure S D T C)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} (hgen : ProjHasType env U S D T C us i)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    OnCtx ((D.projTele T S us).reverse ++ Γ) (env.IsType U) ∧
      VExpr.WF env U ((D.projTele T S us).reverse ++ Γ)
        (D.projGeneric T C us D.np T.indices.length i) := by
  have hord := henv.ordered
  have hI := H.iotaCtx hord
  have hcl := H.projClosed hord
  have hPs : VExpr.ClosedTele (D.params.map (VExpr.instL us)) 0 :=
    VExpr.ClosedTele.map_instL hcl.params
  have hIs : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) D.np :=
    VExpr.ClosedTele.map_instL hcl.indices
  -- the parameter block is a context
  have hOnP0 : OnCtx (D.params.map (VExpr.instL us)).reverse (env.IsType U) :=
    onCtxParams_instL hord hI h7
  have hOnP : OnCtx ((D.params.map (VExpr.instL us)).reverse ++ Γ) (env.IsType U) :=
    OnCtx.appendR hord hΓ (OnCtx.ctxClosed hord hOnP0) hOnP0
  -- the identity parameter spine, over the parameter block
  have hidP : env.HasArgs U ((D.params.map (VExpr.instL us)).reverse ++ Γ)
      (D.params.map (VExpr.instL us)) (bvars 0 D.np) := by
    have h := VEnv.HasArgs.bvars (env := env) (U := U) (Δ := [])
      (As := D.params.map (VExpr.instL us)) (Γ₀ := Γ)
    simpa [hPs.liftTele_eq (Nat.le_refl 0)] using h
  -- the index block and the major premise, from `motiveCtx_wf` at that spine
  obtain ⟨hOnI, hMaj⟩ := motiveCtx_wf hord hI H h3 h7 hOnP (by simp) hidP
  rw [VExpr.instAllTele_bvars_shift (by simpa using hIs), VExpr.liftTele_zero] at hOnI hMaj
  rw [VExpr.map_liftN_bvars_lo (Nat.zero_le _), Nat.add_zero, H.name] at hMaj
  rw [VInductDecl'.projTele_reverse, List.cons_append, List.append_assoc]
  refine ⟨⟨hOnI, hMaj⟩, ?_⟩
  -- the two generic spines and the generic major premise
  have hpsA : env.HasArgs U
      ((VExpr.const S us).mkApp (bvars T.indices.length D.np ++ bvars 0 T.indices.length)
        :: ((T.indices.map (VExpr.instL us)).reverse
            ++ ((D.params.map (VExpr.instL us)).reverse ++ Γ)))
      (D.params.map (VExpr.instL us)) (bvars (T.indices.length + 1) D.np) := by
    have h := VEnv.HasArgs.bvars (env := env) (U := U)
      (Δ := (VExpr.const S us).mkApp (bvars T.indices.length D.np ++ bvars 0 T.indices.length)
        :: (T.indices.map (VExpr.instL us)).reverse)
      (As := D.params.map (VExpr.instL us)) (Γ₀ := Γ)
    simp only [List.cons_append, List.length_cons, List.length_reverse, List.length_map,
      List.append_assoc] at h
    rw [hPs.liftTele_eq (Nat.le_refl 0)] at h
    simpa [Nat.add_comm 1 T.indices.length] using h
  have hιsA : env.HasArgs U
      ((VExpr.const S us).mkApp (bvars T.indices.length D.np ++ bvars 0 T.indices.length)
        :: ((T.indices.map (VExpr.instL us)).reverse
            ++ ((D.params.map (VExpr.instL us)).reverse ++ Γ)))
      (VExpr.instAllTele (T.indices.map (VExpr.instL us))
        (bvars (T.indices.length + 1) D.np))
      (bvars 1 T.indices.length) := by
    have h := VEnv.HasArgs.bvars (env := env) (U := U)
      (Δ := [(VExpr.const S us).mkApp
        (bvars T.indices.length D.np ++ bvars 0 T.indices.length)])
      (As := T.indices.map (VExpr.instL us))
      (Γ₀ := (D.params.map (VExpr.instL us)).reverse ++ Γ)
    rw [VExpr.instAllTele_bvars_shift (by simpa using hIs)]
    simpa [Nat.add_comm 1 T.indices.length] using h
  have hMajLift : ((VExpr.const S us).mkApp
        (bvars T.indices.length D.np ++ bvars 0 T.indices.length)).lift
      = (VExpr.const S us).mkApp
          (bvars (T.indices.length + 1) D.np ++ bvars 1 T.indices.length) := by
    rw [VExpr.lift, VExpr.liftN_mkApp]
    simp only [VExpr.liftN, List.map_append, VExpr.map_liftN_bvars_lo (Nat.zero_le _),
      Nat.add_comm 1 T.indices.length, Nat.add_zero]
  have he : env.HasType U
      ((VExpr.const S us).mkApp (bvars T.indices.length D.np ++ bvars 0 T.indices.length)
        :: ((T.indices.map (VExpr.instL us)).reverse
            ++ ((D.params.map (VExpr.instL us)).reverse ++ Γ)))
      (.bvar 0) ((VExpr.const S us).mkApp
        (bvars (T.indices.length + 1) D.np ++ bvars 1 T.indices.length)) :=
    .bvar (hMajLift ▸ Lookup.zero)
  exact ⟨_, hgen ⟨hOnI, hMaj⟩ he (by simp) (by simp) hpsA hιsA⟩

/-! ## 4. The spine congruence

Everything composes: §3 supplies §1's two context hypotheses, §2 rewrites both sides of the
goal into `instAll` of the *same* generic term, and the two spines' own `TrProj` data supplies
the two `HasArgs` chains §1 needs.

Note which hypotheses are used and which are not.  `VEnv.IsStructure` and the level side
conditions are used **only** to build the generic term's typing; no `PatWF`, no `Params`, no
unique typing, no injectivity.  And the F17 clause enters only through `hgen`, i.e. through
`projTerm_hasType`, exactly as in `TrProj.wf`. -/

/-- `HasArgs`, with the spine moved along pointwise definitional equality. -/
theorem VEnv.HasArgs.toDF' {env : VEnv} {U : Nat} {Γ : List VExpr} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {As as as' : List VExpr}
    (h : env.HasArgs U Γ As as) (hd : List.Forall₂ (env.IsDefEqU U Γ) as as') :
    env.HasArgsDF U Γ As as as' := by
  induction h generalizing as' with
  | nil => cases hd; exact .nil
  | cons ha h ih =>
    cases hd with
    | cons hd0 hds => exact .cons (hd0.of_l henv hΓ ha) (ih hds)

/-- The major premise's binder type, at a concrete parameter/index spine. -/
theorem VInductDecl'.instAll_major {D : VInductDecl'} {T : VIndType} {S : Lean.Name}
    {us : List VLevel} {ps ιs : List VExpr}
    (hp : ps.length = D.np) (hι : ιs.length = T.indices.length) :
    VExpr.instAll ((VExpr.const S us).mkApp
        (bvars T.indices.length D.np ++ bvars 0 T.indices.length)) (ps ++ ιs) 0
      = (VExpr.const S us).mkApp (ps ++ ιs) := by
  rw [VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append,
    VExpr.map_instAll_bvars_top (Nat.zero_le _) (by simp [hp, hι]; omega),
    VExpr.map_instAll_bvars_bot hι]
  simp [← hp, List.take_left']

/-- **`projTerm` is congruent in its parameter and index spines**, at one record, one level
list and one subject.  This is `VEnv.ProjSpineCongr` (`Verify/Typing/ProjSpineInv.lean`) with
the derivations' own data spelled out on **both** sides instead of one — which
`ProjSpineInv.lean` explicitly authorises ("the residual may be weakened freely: at the only
use site both sides come from real `TrProj` derivations at the same record").

The second side's `HasArgs`/`HasType` are what make the right-hand β-step available; that is
the one thing `VEnv.IsDefEqU.instAllCongr` needs and cannot manufacture. -/
theorem VInductDecl'.projTerm_congr_spines {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : VEnv.WF env) (H : env.IsStructure S D T C)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} (hi : i < C.fields.length) (hgen : ProjHasType env U S D T C us i)
    {Γ ps₁ ps₂ ιs₁ ιs₂ : List VExpr} {e : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hp₁ : ps₁.length = D.np) (hι₁ : ιs₁.length = T.indices.length)
    (hp₂ : ps₂.length = D.np) (hι₂ : ιs₂.length = T.indices.length)
    (hA₁ : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps₁)
    (hB₁ : env.HasArgs U Γ
      (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps₁) ιs₁)
    (ht₁ : env.HasType U Γ e ((VExpr.const S us).mkApp (ps₁ ++ ιs₁)))
    (hA₂ : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps₂)
    (hB₂ : env.HasArgs U Γ
      (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps₂) ιs₂)
    (ht₂ : env.HasType U Γ e ((VExpr.const S us).mkApp (ps₂ ++ ιs₂)))
    (hps : List.Forall₂ (env.IsDefEqU U Γ) ps₁ ps₂)
    (hιs : List.Forall₂ (env.IsDefEqU U Γ) ιs₁ ιs₂) :
    env.IsDefEqU U Γ (D.projTerm T C us ps₁ ιs₁ i e) (D.projTerm T C us ps₂ ιs₂ i e) := by
  have hcl := H.projClosed henv.ordered
  obtain ⟨hOn, X, hX⟩ := D.projGeneric_wf henv H h3 h7 hgen hΓ
  -- the two `HasArgs` chains over the generic telescope
  have hmk : ∀ {ps ιs : List VExpr}, ps.length = D.np → ιs.length = T.indices.length →
      env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
      env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs →
      env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ ιs)) →
      env.HasArgs U Γ (D.projTele T S us) (ps ++ ιs ++ [e]) := by
    intro ps ιs hp hι hA hB ht
    refine VEnv.HasArgs.append (VEnv.HasArgs.append hA hB) ?_
    rw [VExpr.instAllTele, VExpr.instAllTele, VInductDecl'.instAll_major hp hι]
    exact .cons ht .nil
  have hr : env.HasArgs U Γ (D.projTele T S us) (ps₂ ++ ιs₂ ++ [e]) := hmk hp₂ hι₂ hA₂ hB₂ ht₂
  -- the left chain, with the spine varying
  have hDF : env.HasArgsDF U Γ (D.projTele T S us) (ps₁ ++ ιs₁ ++ [e]) (ps₂ ++ ιs₂ ++ [e]) := by
    refine VEnv.HasArgsDF.append (VEnv.HasArgsDF.append (hA₁.toDF' henv hΓ hps)
      (hB₁.toDF' henv hΓ hιs)) ?_
    rw [VExpr.instAllTele, VExpr.instAllTele, VInductDecl'.instAll_major hp₁ hι₁]
    exact .cons ht₁ .nil
  have key := VEnv.IsDefEqU.instAllCongr henv hDF hr hΓ hOn hX
  rw [D.projTerm_eq_instAll_generic T C us hcl hi hp₁ hι₁,
    D.projTerm_eq_instAll_generic T C us hcl hi hp₂ hι₂, hp₁, hι₁, hp₂, hι₂]
  exact key

/-! ## 5. Moving a `HasArgs` chain across the level slack

`VEnv.IsStructure.projData_uniq` hands the two derivations' spines over as pointwise
`IsDefEqU`, but each derivation's *telescope* is written at its own `us`, and the two `us`
agree only up to `≈`.  §4 needs both spines against **one** telescope, so one of them has to
cross that slack.

`EqUpToLevels` is the right relation and everything it needs is already in
`Verify/Typing/ProjLvlCongr.lean` and `Theory/Typing/Strong.lean`; what is missing is the
`HasArgs` transport itself, which is this section. -/

theorem VEnv.EqUpToLevels.instTele {U : Nat} {a a' : VExpr} (ha : EqUpToLevels U a a') :
    ∀ {As As' : List VExpr} {k : Nat}, List.Forall₂ (EqUpToLevels U) As As' →
      List.Forall₂ (EqUpToLevels U) (VExpr.instTele a As k) (VExpr.instTele a' As' k)
  | [], [], _, .nil => .nil
  | _ :: _, _ :: _, k, .cons h hs => .cons (VEnv.EqUpToLevels.instN ha h) (ha.instTele (k := k+1) hs)

/-- **A `HasArgs` chain crosses the universe slack.**  If the telescope is replaced by one
that differs only in its universe arguments (pointwise `EqUpToLevels`), the same spine still
inhabits it.

Each step is `IsDefEq.eqUpToLevels` at the binder type — which is a *type*, so its own typing
is `HasType.isType` — plus `EqUpToLevels.instTele` to keep the induction going. -/
theorem VEnv.HasArgs.eqUpToLevels {env : VEnv} {U : Nat} {Γ : List VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {As As' as : List VExpr}, env.HasArgs U Γ As as →
      List.Forall₂ (VEnv.EqUpToLevels U) As As' → env.HasArgs U Γ As' as := by
  intro As As' as h
  induction h generalizing As' with
  | nil => intro hEq; cases hEq; exact .nil
  | @cons A As a as ha h ih =>
    intro hEq
    cases hEq with
    | cons hA hAs =>
      obtain ⟨u, hAu⟩ := ha.isType henv.ordered hΓ
      have hAA' : env.IsDefEqU U Γ A _ :=
        ⟨_, VEnv.IsDefEq.eqUpToLevels henv.ordered hΓ hAu hA⟩
      refine .cons (ha.defeqU_r henv hΓ hAA') (ih ?_)
      exact VEnv.EqUpToLevels.instTele
        (VEnv.eqUpToLevels_refl_of_hasType henv.ordered hΓ ha) hAs

/-! ## 6. `VEnv.ProjDataCongr`, discharged

The last obligation of `TrProj.uniq` (`Verify/Typing/ProjSpineInv.lean`'s obligation 3) is
`VEnv.ProjDataCongr`.  It is proved here from one hypothesis, `VEnv.ProjTypingAll` — which is
*exactly* the statement of `projTerm_hasType` (`Verify/Typing/Lemmas.lean`), passed as a
parameter only because that file is downstream.  So this is not a residual: the composite
theorem `TrProj.uniq` is closed at the use site, with no `sorry` and no new assumption. -/

/-- `projTerm_hasType`'s statement, as a predicate on `env`.  Its F17 premise is `TrProj`'s
own recorded clause verbatim, so a `TrProj` derivation supplies it with no case analysis at
the call sites here (the `isLE` split lives in `TrProj.wf`, which is where the two forms are
reconciled). -/
def VEnv.ProjTypingAll (env : VEnv) (U : Nat) : Prop :=
  ∀ {S : Lean.Name} {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    {i : Nat}, env.IsStructure S D T C → us.length = D.uvars → (∀ l ∈ us, l.WF U) →
    i < C.fields.length →
    (D.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    ProjHasType env U S D T C us i

/-- **`TrProj` is a function up to definitional equality.**  Two derivations at the same
subject and the same structure name give definitionally equal targets.

Three moves: `projData_uniq` bounds the difference; `projTerm_defeq_of_levels` absorbs the
records and the universe arguments at the *first* spine; then `projTerm_congr_spines` moves the
spines at the *second* record.  The join between the last two is `HasArgs.eqUpToLevels` (§5),
which carries the first derivation's telescope data across the universe slack. -/
theorem VEnv.ProjTypingAll.projDataCongr {env : VEnv} {U : Nat} (henv : VEnv.WF env)
    (hgen : env.ProjTypingAll U) : env.ProjDataCongr U := by
  intro Γ S i e e₁' e₂' hΓ H1 H2
  obtain @⟨_, D₁, T₁, C₁, us₁, ps₁, ιs₁, _, _, _, HS₁, hty₁, h3₁, hnp₁, hni₁, hi₁, hu₁,
    hA₁, hB₁, hF₁⟩ := H1
  obtain @⟨_, D₂, T₂, C₂, us₂, ps₂, ιs₂, _, _, _, HS₂, hty₂, h3₂, hnp₂, hni₂, hi₂, hu₂,
    hA₂, hB₂, hF₂⟩ := H2
  obtain ⟨-, hag, hlv, hus, hps, hιs⟩ :=
    HS₁.projData_uniq henv hΓ HS₂ hty₁ hty₂ hnp₁ hnp₂ (.refl ⟨_, hty₁⟩)
  -- the level side conditions, read off the first derivation's own typing
  have hlwf := hty₁.levelWF (VEnv.CtxStrong.strong henv.ordered hΓ).levelWF
  have hspine := (VExpr.levelWF_mkApp.1 hlwf.2.2).2
  have hps₁wf : ∀ p ∈ ps₁, p.LevelWF U :=
    fun p hp => hspine _ (List.mem_append.2 (.inl hp))
  have hιs₁wf : ∀ x ∈ ιs₁, x.LevelWF U :=
    fun x hx => hspine _ (List.mem_append.2 (.inr hx))
  -- step 1: the records and the universe arguments, at the first spine
  have step1 : env.IsDefEqU U Γ (D₁.projTerm T₁ C₁ us₁ ps₁ ιs₁ i e)
      (D₂.projTerm T₂ C₂ us₂ ps₁ ιs₁ i e) :=
    D₁.projTerm_defeq_of_levels henv hΓ hag hlv hu₁ hu₂ hus hps₁wf hιs₁wf hlwf.1
      (hgen HS₁ h3₁ hu₁ hi₁ hF₁ hΓ hty₁ hnp₁ hni₁ hA₁ hB₁)
  -- the first derivation's telescope data, moved onto the second record
  have hrefl : ∀ {l : List VExpr}, (∀ x ∈ l, x.LevelWF U) →
      List.Forall₂ (VEnv.EqUpToLevels U) l l :=
    fun h => List.Forall₂.rfl fun x hx => VEnv.EqUpToLevels.refl_levelWF (h x hx)
  have hA₁' : env.HasArgs U Γ (D₂.params.map (VExpr.instL us₂)) ps₁ := by
    rw [hag.params] at hA₁
    exact hA₁.eqUpToLevels henv hΓ (VEnv.EqUpToLevels.map_instL hu₁ hu₂ hus _)
  have hB₁' : env.HasArgs U Γ
      (VExpr.instAllTele (T₂.indices.map (VExpr.instL us₂)) ps₁) ιs₁ := by
    rw [hag.indices] at hB₁
    exact hB₁.eqUpToLevels henv hΓ (VEnv.EqUpToLevels.instAllTele
      (VEnv.EqUpToLevels.map_instL hu₁ hu₂ hus _) (hrefl hps₁wf))
  have hty₁' : env.HasType U Γ e ((VExpr.const S us₂).mkApp (ps₁ ++ ιs₁)) := by
    obtain ⟨u, hTy⟩ := hty₁.isType henv.ordered hΓ
    refine hty₁.defeqU_r henv hΓ ⟨_, VEnv.IsDefEq.eqUpToLevels henv.ordered hΓ hTy ?_⟩
    exact VEnv.EqUpToLevels.mkApp (hrefl (fun x hx => hspine x hx))
      (.const hu₁ hu₂ hus)
  -- step 2: the spines, at the second record
  refine step1.trans henv hΓ (D₂.projTerm_congr_spines henv HS₂ h3₂ hu₂ hi₂
    (hgen HS₂ h3₂ hu₂ hi₂ hF₂) hΓ ?_ ?_ hnp₂ hni₂ hA₁' hB₁' hty₁' hA₂ hB₂ hty₂ hps hιs)
  · rw [hnp₁, VInductDecl'.np, VInductDecl'.np, hag.params]
  · rw [hni₁, hag.indices]

end Lean4Lean
