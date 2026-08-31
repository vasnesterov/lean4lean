import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Typing.StructureUniq
import Lean4Lean.Theory.Typing.SpineInv
import Lean4Lean.Theory.Typing.PatWFIota

/-!
# `TrProj.weak'_inv` reduced to a strengthening residual — **not** to rigidity

`Verify/Typing/Lemmas.lean`'s `TrProj.weak'_inv` is the last `Verify/`-side census hole with
transitive users (30+).  Its docstring there, through six updates, concludes: the only route on
offer is fact (C) *rigidity* — `VEnv.ConstRigidPat` (`Verify/Typing/Rigidity.lean`) — whose only
producer, `constRigidPat_of_weakNorm`, is **unusable**, because `VEnv.WeakNorm` is refuted
sorry-free (`Verify/Typing/WeakNormRefute.lean`).  Both halves of that verdict were re-checked
here and are **correct as facts**: `ConstRigidPat` occurs nowhere in the tree as the conclusion
of a theorem other than `constRigidPat_of_weakNorm`, and the two refutations
(`VEnv.PropLoopWeakNorm.not_weakNorm`, `.not_forall_weakNorm`) carry only
`[propext, Classical.choice, Quot.sound]`.

**What is wrong is the inference "so this lemma is blocked on rigidity".**  Rigidity is
*sufficient* for the shape step, and it was the only route *stated*; it is not necessary.  What
`TrProj.weak'_inv` actually needs is weaker in two ways at once — it needs a **definitional
equation in the smaller context**, not a weak-head *reduction*, and it needs it only for a
subject that is a **lift**:

    `VEnv.ConstAppTypeStrengthen` — if `Γ' ⊢ e.lift' l : (const c us).mkApp as` then
    `Γ ⊢ e : (const c us').mkApp as'` for some `us' ≈ us` pointwise and some `as'` of the
    same length.

Rigidity asks for a whnf reduct of an arbitrary subject convertible with a `c`-spine; this asks
only that a *typing* survive strengthening with its head intact.  The counterexample that kills
`WeakNorm` — a δ-cycle `A : Prop := B`, `B : Prop := A` with no weak-head normal form — says
nothing about it: at that environment neither constant is inhabited, so the hypothesis above is
unsatisfiable there, and the two constants are not structures.

## What this file proves

* `TrProj.weak'_inv_of_strengthen` — **`TrProj.weak'_inv`'s exact statement**, from
  `ConstAppTypeStrengthen` as a hypothesis.  Nothing else is added and nothing is narrowed.
* `TrProj.weak'_inv_of_strengthen_onCtx` — the same with `OnCtx Γ` taken rather than recovered,
  which localises the strengthening hole (below).
* the residual bounded both ways, per `docs/vacuity-ledger.md` §5: it **holds** at every
  depth-zero lift (`constAppTypeStrengthen_depth_zero`), its hypotheses are **jointly
  satisfiable at a lift of depth one** in every environment declaring a `Sort 0`-valued
  constant (`constAppTypeStrengthen_fires`), and it is **not trivially true** — drop the
  "subject is a lift" hypothesis and the conclusion is false at that same witness
  (`constAppTypeStrengthen_needs_lift`).

## Measured hole cones (`deps`, transitive over type *and* value, `allowOpaque := true`)

    TrProj.weak'_inv_of_strengthen        cone 3661   weakN_iff, forallE_inv_stratified,
                                                     rigidShapeUniqNS
    TrProj.weak'_inv_of_strengthen_onCtx cone 3628   forallE_inv_stratified, rigidShapeUniqNS
    TrProj.wf                            cone 5054   weakN_iff, forallE_inv_stratified
    TrProj.uniq                          cone 8199   weakN_iff, forallE_inv_stratified,
                                                     rigidShapeUniqNS, NormalEq.descend

Three things to read off, none of which was on the record before:

1. **No `ConstRigidPat`, no `WeakNorm`, no `NormalEq.descend`.**  The reduction is not routed
   through Church--Rosser at all, so it does not inherit `descend` — which is *false*
   (`Theory/Typing/DescendRefute.lean`), not merely open.  Every hole it does carry is one
   `TrProj.uniq` (closed) and `TrProj.wf` (proved) already carry.
2. **The strengthening hole enters through exactly one step.**  Dropping to the `_onCtx`
   version removes `IsDefEqU.weakN_iff` from the cone: its only appeal is `OnCtx.weak'_inv`,
   recovering well-formedness of the smaller context.  Nothing in the projection data needs it.
   (The sole consumer, `TrExprS.weakFV'_inv`, cannot supply `OnCtx Γ` today: it carries
   `VLCtx.WF` for the *larger* context only.  So gate 1 is real — but it is one bookkeeping
   step, not a mathematical obstruction inside the projection.)
3. **`rigidShapeUniqNS` is new to this family's `weak'_inv` route** and arrives with
   `HasArgs.of_mkApp` (`Theory/Typing/SpineInv.lean`), i.e. with Π-injectivity, not with
   anything about constants.

## What is left, stated exactly

`ConstAppTypeStrengthen` itself.  It is not proved here and it is **not** claimed to be easy.
The route that does not go through whnf-existence, sketched so the next round does not have to
re-derive it: `IsDefEq.church_rosser` gives reducts with `NormalEq X' Y'`, `Y'` stays
`c`-headed (`ParRed.constApp_inv`), `X'` stays a lift (`ParRed.weakN_inv`), and a `NormalEq`
between a lift and a `c`-spine is inverted by `appDF` descent — where each *argument* of the
spine is defeq to a lift because the corresponding argument on the left is one, so the
pre-image is read off directly instead of being recovered.  The `etaL` clause, which is what
blocks (C) at a proper sub-spine (`Verify/Typing/ConstSpine.lean`), is **not** fatal for this
weaker conclusion: there the left side is a λ that *is* definitionally a `c`-spine, and a
definitional equation is all that is wanted.  Two costs are known in advance and neither is
paid here: that route re-imports `NormalEq.descend` (false, so it needs `KDescend.lean`'s
repair first), and its `ParRed.weakN_inv` step is the cycle entry `Theory/Typing/ParRedKWeakN.lean`
analyses.  A direct proof avoiding both is the open question.
-/

namespace Lean4Lean
open Lean4Lean VEnv Lean VExpr

/-- **The residual.** -/
def VEnv.ConstAppTypeStrengthen (env : VEnv) (U : Nat) : Prop :=
  ∀ {l : Lift} {Γ Γ' : List VExpr} {e : VExpr} {c : Lean.Name} {us : List VLevel}
    {as : List VExpr},
    OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' → (∀ u ∈ us, u.WF U) →
    env.HasType U Γ' (e.lift' l) ((VExpr.const c us).mkApp as) →
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.HasType U Γ e ((VExpr.const c us').mkApp as')

/-- **The reduction, with `OnCtx Γ` taken rather than recovered.**  Stated separately because
it is what pins down where each gate enters: this version's measured hole cone is
`{forallE_inv_stratified, rigidShapeUniqNS}` and does **not** contain `IsDefEqU.weakN_iff`.
The strengthening hole enters `TrProj.weak'_inv` through exactly one step — `OnCtx.weak'_inv`,
used below to recover the well-formedness of the smaller context — and through nothing in the
projection data itself. -/
theorem TrProj.weak'_inv_of_strengthen_onCtx {env : VEnv} {U : Nat} {Γ Γ' : List VExpr}
    {l : Lift} {s : Lean.Name} {i : Nat} {e e' : VExpr}
    (henv : VEnv.WF env) (hst : env.ConstAppTypeStrengthen U)
    (hΓ' : OnCtx Γ' (env.IsType U)) (hΓ : OnCtx Γ (env.IsType U)) (W : Ctx.Lift' l Γ Γ')
    (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' := by
  cases H with
  | @mk S D T C us ps ιs _ _ _ hS hty hus hps hιs hi hlv hargs hιargs hF17 =>
    obtain ⟨us', as', hlv', huseq, hlen, hty'⟩ := hst hΓ' W hlv hty
    have hus' : us'.length = D.uvars := huseq.length_eq.trans hus
    -- the structure's declared type, at `Γ`
    have hconst : env.HasType U Γ (.const s us') (T.type.instL us') :=
      .constDF hS.const_ty hlv' hlv' hus' (List.Forall₂.rfl fun _ _ => rfl)
    -- F1: the declared type is only *definitionally* the canonical Π-telescope
    obtain ⟨env₀, env₁, hWF, hadd, hle⟩ := hS.decl
    have hle₀ : env₀ ≤ env := (VEnv.addInduct'_le hadd).trans hle
    have hT : T ∈ D.types := by rw [hS.types]; exact List.mem_singleton_self _
    obtain ⟨u₀, hcanon⟩ := (hWF.types T hT).canon
    have hcanonD : env.IsDefEqU U Γ (T.type.instL us') ((T.canonType D).instL us') := by
      have := ((hcanon.mono hle₀).instL (U' := U) hlv').weak0 henv.ordered (Γ := Γ)
      exact ⟨_, by simpa using this⟩
    have hcanon' : env.HasType U Γ (.const s us') ((T.canonType D).instL us') :=
      VEnv.HasType.defeqU_r henv hΓ hcanonD hconst
    -- the canonical telescope, in the shape `HasArgs.of_mkApp` wants
    have hAs : (T.canonType D).instL us'
        = mkPi (List.map (VExpr.instL us') D.params ++ List.map (VExpr.instL us') T.indices)
            (.sort (VLevel.inst us' D.lvl)) := by
      simp [VIndType.canonType, VExpr.instL_mkPi, VExpr.instL]
    rw [hAs] at hcanon'
    -- split `as'` at the parameter/index boundary
    obtain ⟨ps', ιs', rfl, hps', hιs'⟩ :
        ∃ ps' ιs', as' = ps' ++ ιs' ∧ ps'.length = ps.length ∧ ιs'.length = ιs.length := by
      refine ⟨as'.take ps.length, as'.drop ps.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
      · simp [hlen]
      · simp [hlen]
    obtain ⟨u₁, hspine⟩ := hty'.isType henv hΓ
    have hargs' := VEnv.HasArgs.of_mkApp henv hΓ (ps' ++ ιs')
      (by simp [hps', hιs', hps, hιs, VInductDecl'.np]) hcanon' hspine
    obtain ⟨hP, hI⟩ := VEnv.HasArgs.append_inv
      (by simp [hps', hps, VInductDecl'.np]) hargs'
    -- F17 transports along the level equivalence
    have hF17' : D.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
        VLevel.inst us' (C.fields.getD k default).lvl ≈ .zero :=
      hF17.imp_right fun h k hk hu =>
        (VLevel.equiv_congr_left (VLevel.inst_congr rfl huseq)).2 (h k hk hu)
    exact ⟨_, .mk hS hty' hus' (hps'.trans hps) (hιs'.trans hιs) hi hlv' hP hI hF17'⟩

/-- **`TrProj.weak'_inv` from the residual.**  Same statement as the `sorry` in
`Verify/Typing/Lemmas.lean`, with `VEnv.ConstAppTypeStrengthen` added as a hypothesis. -/
theorem TrProj.weak'_inv_of_strengthen {env : VEnv} {U : Nat} {Γ Γ' : List VExpr}
    {l : Lift} {s : Lean.Name} {i : Nat} {e e' : VExpr}
    (henv : VEnv.WF env) (hst : env.ConstAppTypeStrengthen U)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' l Γ Γ')
    (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' :=
  TrProj.weak'_inv_of_strengthen_onCtx henv hst hΓ' (hΓ'.weak'_inv henv W) W H

/-! ## The residual, bounded both ways -/

/-- **Not false: it holds at every lift of depth zero**, with `us' = us`, `as' = as`. -/
theorem constAppTypeStrengthen_depth_zero {env : VEnv} {U : Nat} {l : Lift}
    {Γ Γ' : List VExpr} {e : VExpr} {c : Lean.Name} {us : List VLevel} {as : List VExpr}
    (hd : l.depth = 0) (W : Ctx.Lift' l Γ Γ') (hlv : ∀ u ∈ us, u.WF U)
    (H : env.HasType U Γ' (e.lift' l) ((VExpr.const c us).mkApp as)) :
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.HasType U Γ e ((VExpr.const c us').mkApp as') := by
  cases W.depth_zero hd
  rw [VExpr.lift'_depth_zero hd] at H
  exact ⟨us, as, hlv, .rfl fun _ _ => rfl, rfl, H⟩

/-- A `Sort 0`-valued constant is a type in every context — the one environment fact the two
witnesses below need. -/
theorem hasType_const_sortZero {env : VEnv} {U : Nat} {c : Lean.Name} {Γ : List VExpr}
    (hc : env.constants c = some ⟨0, .sort .zero⟩) :
    env.HasType U Γ (VExpr.const c []) (.sort .zero) :=
  VEnv.IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) (ls := []) (ls' := [])
    hc (by simp) (by simp) (by simp) (List.Forall₂.rfl fun _ _ => rfl)

/-- **Not vacuous: the hypotheses are jointly satisfiable at a lift of depth one**, in every
environment declaring a `Sort 0`-valued constant — so the residual is not true for the
uninteresting reason that nothing satisfies it.  (`c` need not be a structure: the residual is
about constant-headed *types*, and `TrProj.weak'_inv` supplies `IsStructure` separately.) -/
theorem constAppTypeStrengthen_fires {env : VEnv} {U : Nat} {c : Lean.Name}
    (hc : env.constants c = some ⟨0, .sort .zero⟩) :
    OnCtx [VExpr.const c [], VExpr.const c []] (env.IsType U) ∧
      Ctx.Lift' (.skip .refl) [VExpr.const c []] [VExpr.const c [], VExpr.const c []] ∧
      env.HasType U [VExpr.const c [], VExpr.const c []]
        ((VExpr.bvar 0).lift' (.skip .refl)) ((VExpr.const c []).mkApp []) ∧
      -- …and the conclusion holds there, so the residual is not false at this instance either
      ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' ([] : List VLevel) ∧
        as'.length = ([] : List VExpr).length ∧
        env.HasType U [VExpr.const c []] (.bvar 0) ((VExpr.const c us').mkApp as') := by
  refine ⟨⟨⟨trivial, _, hasType_const_sortZero hc⟩, _, hasType_const_sortZero hc⟩,
    .skip .refl, ?_, [], [], (by simp), .nil, rfl, ?_⟩
  · have := VEnv.HasType.bvar (env := env) (U := U)
      (Γ := [VExpr.const c [], VExpr.const c []]) (i := 1) (A := _) (.succ .zero)
    simpa [VExpr.lift, VExpr.liftN] using this
  · have := VEnv.HasType.bvar (env := env) (U := U) (Γ := [VExpr.const c []]) (i := 0)
      (A := _) .zero
    simpa [VExpr.lift, VExpr.liftN] using this

/-- **Not trivially true: the "subject is a lift" hypothesis is load-bearing.**  Drop it and
the conclusion is false at a witness the previous lemma's environment already provides: the
context is well formed, the subject is typed at a constant-headed type in `Γ'`, and it has no
type at all in `Γ`. -/
theorem constAppTypeStrengthen_needs_lift {env : VEnv} {U : Nat} {c : Lean.Name}
    (henv : env.Ordered) (hc : env.constants c = some ⟨0, .sort .zero⟩) :
    OnCtx [VExpr.const c []] (env.IsType U) ∧
      env.HasType U [VExpr.const c []] (.bvar 0) ((VExpr.const c []).mkApp []) ∧
      ¬ ∃ (us' : List VLevel) (as' : List VExpr),
        env.HasType U [] (.bvar 0) ((VExpr.const c us').mkApp as') := by
  refine ⟨⟨trivial, _, hasType_const_sortZero hc⟩, ?_, ?_⟩
  · have := VEnv.HasType.bvar (env := env) (U := U) (Γ := [VExpr.const c []]) (i := 0)
      (A := _) .zero
    simpa [VExpr.lift, VExpr.liftN] using this
  · rintro ⟨us', as', h⟩
    have := h.closedN henv (Γ := []) trivial
    simp [VExpr.ClosedN] at this
