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
   **But that reduction does not survive contact with the consumer, and the parenthesis this
   docstring used to carry here was false** — see §"Gate 1 is not a bookkeeping gap" below.
   `TrExprS.weakFV'_inv` *can* supply `OnCtx Γ`, via `VLCtx.FVLift'.wf`, which it already
   calls; and doing so re-imports `weakN_iff`, because `FVLift'.wf` is proved from
   `VLocalDecl.weak'_iff`.  Measured: `TrProj.weakFV'_inv_of_strengthen`, the consumer-shaped
   reduction, has cone 3729 with holes `{weakN_iff, forallE_inv_stratified,
   rigidShapeUniqNS}`.  So 3628 is an artefact of looking at `weak'_inv` in isolation.
3. **`rigidShapeUniqNS` is new to this family's `weak'_inv` route** and arrives with
   `HasArgs.of_mkApp` (`Theory/Typing/SpineInv.lean`), i.e. with Π-injectivity, not with
   anything about constants.  It is *not* new to anything downstream: `IsDefEqU.forallE_inv`
   itself carries it (cone 3537), and it already reaches the sole consumer without passing
   through `weak'_inv` at all —
   `weakFV'_inv → TrExprS.uniq → TrProj.uniq → TrProj.uniq_of_projTermCongr →
   IsStructure.spine_inv → constApp_inv_of_wf → patWF_of_wf → piInv_axiom →
   IsDefEqU.forallE_inv → rigidShapeUniqNS`
   (breadth-first search with `TrProj.weak'_inv` deleted from the graph).  `NormalEq.descend`
   likewise reaches it, via `constApp_inv_of_patWF → IsDefEq.constApp_inv → church_rosser`.
   So discharging the residual **does not widen the blocking set** of anything that consumes
   this lemma; all four holes are already there.

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

## Round 2 (2026-09-01): the residual localised to one uninhabited binder

Neither cost above needs to be paid to shrink the residual substantially.  Two results, both
hole-free (`[propext, Classical.choice, Quot.sound]` only), both avoiding Church--Rosser,
`NormalEq.descend`, `ParRed.weakN_inv`, `OnCtx.weak'_inv` and `IsDefEqU.weakN_iff` entirely:

* `constAppTypeStrengthen_inhab` (cone 1156, no holes) — the residual **holds at every depth**
  across any lift each of whose inserted binders is inhabited in the context below it
  (`Ctx.InhabLift`), and then with `us' = us` on the nose and `as'` an explicit substitution
  instance of `as`.  Mechanism: `VExpr.inst_liftN` undoes the lift, `VExpr.inst_mkApp` keeps the
  head.  `Ctx.InhabLift.sorts` exhibits such lifts at **every** depth in **every** environment
  (a `Sort 1` binder is inhabited by `Sort 0`), so this strictly extends
  `constAppTypeStrengthen_depth_zero`, and `constAppTypeStrengthen_inhab_fires` shows the bound
  is not vacuous at depth one.
* `constAppTypeStrengthen_of_skipUninhab` (cone 1207, no holes) — the converse half of the same
  case split, and a genuine **reduction**: `VEnv.ConstAppSkipUninhab`, which strips the
  arbitrary `Ctx.Lift'` to a **single** binder `Ctx.LiftN 1 k` *and* lets that binder be assumed
  **uninhabited in its own prefix**, implies the full residual.
  `VEnv.ConstAppTypeStrengthen.skip_step` is the other direction pointwise, so nothing beyond
  the residual's own `OnCtx Γ'` premise is given away.

This is the move `Theory/Typing/Strengthen.lean` §12 already ran for `IsDefEqU.weakN_iff`
(`Strengthening1Uninhab.strengthening1`, `strengtheningTarget_of_allInhabited`); what is new is
that it applies to the projection residual as well.  The honest consequence is the same as there:
the residual carries content exactly to the extent that **uninhabited** types over a `VEnv.WF`
environment exist, and exhibiting one is itself open in this tree (`VEnv.Consistent` is a
definition; `leanTTConsistent` is proved nowhere).  So "no witness exhibited" is not evidence
either way — but any future attack may now assume one binder and no inhabitant.
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

/-! ## Gate 1 is not a bookkeeping gap: the sole consumer *can* supply `OnCtx Γ`

`TrProj.weak'_inv_of_strengthen_onCtx` was described as localising the `IsDefEqU.weakN_iff`
gate to one step, `OnCtx.weak'_inv`, on the ground that the sole consumer
`TrExprS.weakFV'_inv` "cannot supply `OnCtx Γ`, it carries `VLCtx.WF` for the larger context
only".  **That is false.**  `VLCtx.FVLift'.wf` (`Verify/Typing/Lemmas.lean:314`) turns
`VLCtx.WF` for the larger context into `VLCtx.WF` for the smaller one, and
`TrExprS.weakFV'_inv` *already calls it* — its `app` case reads
`this.app_inv henv (W.wf henv hΔ₂).toCtx`.  So the consumer-shaped reduction below needs no
`OnCtx.weak'_inv` at all.

It also buys nothing, and that is the point worth recording.  `VLCtx.FVLift'.wf` is itself
proved by `VLocalDecl.weak'_iff`, so its own measured hole cone is 3542 with holes
`{IsDefEqU.weakN_iff, IsDefEqU.forallE_inv_stratified}`.  `weakN_iff` therefore reaches
`TrExprS.weakFV'_inv` by a path that never touches `TrProj.weak'_inv`:

    weakFV'_inv → VExpr.WF.weak'_iff → IsDefEqU.weak'_iff → IsDefEqU.weakN_iff

(measured by breadth-first search with `TrProj.weak'_inv` deleted from the graph).  Closing
"gate 1" inside the projection therefore removes `weakN_iff` from `weak'_inv`'s cone and from
nothing that consumes it. -/
theorem TrProj.weakFV'_inv_of_strengthen {env : VEnv} {U : Nat} {Δ Δ₂ : VLCtx}
    {dk : Nat} {n : Lift} {k : Nat} {s : Lean.Name} {i : Nat} {e e' : VExpr}
    (henv : VEnv.WF env) (hst : env.ConstAppTypeStrengthen U)
    (W : VLCtx.FVLift' Δ Δ₂ dk n k) (hΔ₂ : VLCtx.WF env U Δ₂)
    (H : TrProj env U Δ₂.toCtx s i (e.lift' (n.consN k)) e') :
    ∃ e'', TrProj env U Δ.toCtx s i e e'' :=
  TrProj.weak'_inv_of_strengthen_onCtx henv hst hΔ₂.toCtx
    (W.wf henv hΔ₂).toCtx W.toCtx H

/-! ## The residual holds across every *inhabited* lift, at every depth

`constAppTypeStrengthen_depth_zero` bounds the residual from below at depth 0 only.  The bound
below is at **every** depth: the residual holds, sorry-free, whenever each binder the lift
inserts is inhabited in the context below it — and then with `us' = us` on the nose, not merely
up to `≈`, and with `as'` an explicit substitution instance of `as`.

The mechanism is the one the strengthening literature calls "substituting the strengthened
variables away": a lift is undone by instantiating each inserted variable, `inst` after
`liftN 1 k` is the identity (`VExpr.inst_liftN`), and `inst` commutes with `mkApp` while fixing
`const` (`VExpr.inst_mkApp`).  So the *whole* difficulty of `ConstAppTypeStrengthen` — and, by
`TrProj.weak'_inv_of_strengthen`, of `TrProj.weak'_inv` — is concentrated in lifts over
**uninhabited** binders.  Nothing here goes through Church--Rosser, `NormalEq.descend`, or
`ParRed.weakN_inv`. -/

/-- A single-binder insertion, inverted.  `Ctx.LiftN 1 k Γ Γ'` inserts one type `A` at cut `k`;
everything of `Γ'` above the cut is a lift, so instantiating the inserted variable with *any*
term `t` returns `Γ` on the nose.  The `Γ₀`/`A` produced are the context below the cut and the
inserted type. -/
theorem Ctx.LiftN.one_split : ∀ {k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN 1 k Γ Γ' →
    ∃ Γ₀ A, ∀ t, Ctx.InstN Γ₀ t A k Γ' Γ := by
  intro k Γ Γ' W
  induction W with
  | @zero Γ As h =>
    match As, h with
    | [A], _ => exact ⟨Γ, A, fun _ => .zero⟩
  | @succ k Γ Γ' B W ih =>
    obtain ⟨Γ₀, A, ih⟩ := ih
    refine ⟨Γ₀, A, fun t => ?_⟩
    have := Ctx.InstN.succ (A := B.liftN 1 k) (ih t)
    rwa [VExpr.inst_liftN] at this

/-- `Ctx.Lift'` refined: a chain of single-binder insertions, each carrying an **inhabitant** of
the inserted type in the context below it.  `Lift.consN (.skip .refl) k` is the lift of a single
binder at cut `k`, i.e. `liftN 1 k`. -/
inductive Ctx.InhabLift (env : VEnv) (U : Nat) : Lift → List VExpr → List VExpr → Prop where
  | refl {Γ} : Ctx.InhabLift env U .refl Γ Γ
  | step {l : Lift} {k : Nat} {Γ Γ₂ Γ₃ Γ₀ : List VExpr} {t A : VExpr} :
    Ctx.InhabLift env U l Γ Γ₂ → Ctx.LiftN 1 k Γ₂ Γ₃ →
    env.HasType U Γ₀ t A → Ctx.InstN Γ₀ t A k Γ₃ Γ₂ →
    Ctx.InhabLift env U (Lift.comp l (Lift.consN (.skip .refl) k)) Γ Γ₃

/-- An inhabited lift *is* a lift: `Ctx.InhabLift` refines `Ctx.Lift'`, so the theorem below
really is an instance of `VEnv.ConstAppTypeStrengthen` and not a different statement. -/
theorem Ctx.InhabLift.toLift' {env : VEnv} {U : Nat} :
    ∀ {l : Lift} {Γ Γ' : List VExpr}, Ctx.InhabLift env U l Γ Γ' → Ctx.Lift' l Γ Γ'
  | _, _, _, .refl => .refl
  | _, _, _, .step H W _ _ => H.toLift'.comp (Ctx.liftN_iff_lift'.1 W)

/-- The convenient form of `step`: the caller supplies the insertion and an inhabitant, and the
context below the cut is computed by `Ctx.LiftN.one_split`. -/
theorem Ctx.InhabLift.step' {env : VEnv} {U : Nat} {l : Lift} {k : Nat} {Γ Γ₂ Γ₃ : List VExpr}
    (H : Ctx.InhabLift env U l Γ Γ₂) (W : Ctx.LiftN 1 k Γ₂ Γ₃)
    (hinh : ∀ Γ₀ A, (∀ t, Ctx.InstN Γ₀ t A k Γ₃ Γ₂) → ∃ t, env.HasType U Γ₀ t A) :
    Ctx.InhabLift env U (Lift.comp l (Lift.consN (.skip .refl) k)) Γ Γ₃ :=
  let ⟨_, _, hI⟩ := W.one_split
  let ⟨_, ht⟩ := hinh _ _ hI
  .step H W ht (hI _)

/-- The `.skip` constructor of `Ctx.Lift'`, refined. -/
theorem Ctx.InhabLift.skip {env : VEnv} {U : Nat} {l : Lift} {Γ Γ' : List VExpr} {A t : VExpr}
    (H : Ctx.InhabLift env U l Γ Γ') (ht : env.HasType U Γ' t A) :
    Ctx.InhabLift env U (.skip l) Γ (A :: Γ') := by
  have h := Ctx.InhabLift.step (k := 0) H .one ht .zero
  rwa [show Lift.comp l (Lift.consN (.skip .refl) 0) = .skip l from
    (Lift.consN_skip_eq (l := l) (k := 0)).symm] at h

/-- **The residual holds at every inhabited lift**, with `us` untouched and `as'` the explicit
substitution instance of `as`. -/
theorem hasType_const_mkApp_of_inhabLift {env : VEnv} {U : Nat} (henv : env.Ordered)
    {c : Lean.Name} {us : List VLevel} :
    ∀ {l : Lift} {Γ Γ' : List VExpr}, Ctx.InhabLift env U l Γ Γ' →
      ∀ {e : VExpr} {as : List VExpr},
      env.HasType U Γ' (e.lift' l) ((VExpr.const c us).mkApp as) →
      ∃ as', as'.length = as.length ∧ env.HasType U Γ e ((VExpr.const c us).mkApp as') := by
  intro l Γ Γ' W
  induction W with
  | refl => intro e as H; exact ⟨as, rfl, by simpa using H⟩
  | step W1 WL ht WI ih =>
    intro e as H
    rw [VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at H
    have H2 := H.instN henv WI ht
    rw [VExpr.inst_liftN, VExpr.inst_mkApp,
      show (VExpr.const c us).inst _ _ = VExpr.const c us from rfl] at H2
    obtain ⟨as', hlen, H3⟩ := ih H2
    exact ⟨as', by simpa using hlen, H3⟩

/-- The same, packaged in `VEnv.ConstAppTypeStrengthen`'s exact conclusion shape. -/
theorem constAppTypeStrengthen_inhab {env : VEnv} {U : Nat} (henv : env.Ordered) {l : Lift}
    {Γ Γ' : List VExpr} {e : VExpr} {c : Lean.Name} {us : List VLevel} {as : List VExpr}
    (W : Ctx.InhabLift env U l Γ Γ') (hlv : ∀ u ∈ us, u.WF U)
    (H : env.HasType U Γ' (e.lift' l) ((VExpr.const c us).mkApp as)) :
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.HasType U Γ e ((VExpr.const c us').mkApp as') :=
  let ⟨as', h1, h2⟩ := hasType_const_mkApp_of_inhabLift henv W H
  ⟨us, as', hlv, .rfl fun _ _ => rfl, h1, h2⟩

/-- **Inhabited lifts exist at every depth**, in *every* environment: a binder of type
`Sort 1` is inhabited by `Sort 0`, with no environment hypothesis at all.  So the bound above
is strictly stronger than `constAppTypeStrengthen_depth_zero`, which covers depth 0 only. -/
theorem Ctx.InhabLift.sorts {env : VEnv} {U : Nat} :
    ∀ (n : Nat) {Γ : List VExpr},
      Ctx.InhabLift env U (.skipN .refl n) Γ
        (List.replicate n (VExpr.sort (.succ .zero)) ++ Γ)
  | 0, _ => .refl
  | n+1, Γ => by
    have h := (Ctx.InhabLift.sorts (env := env) (U := U) n (Γ := Γ)).skip
      (A := VExpr.sort (.succ .zero)) (t := .sort .zero) (VEnv.HasType.sort trivial)
    simpa [List.replicate_succ] using h

/-- **The inhabited-lift bound is not vacuous**: at a lift of depth one whose skipped binder is
inhabited, the residual's hypotheses hold *and* `constAppTypeStrengthen_inhab` discharges its
conclusion — sorry-free, in every environment declaring a `Sort 0`-valued constant.  Compare
`constAppTypeStrengthen_fires`, whose skipped binder is `const c []` and therefore carries no
inhabitant. -/
theorem constAppTypeStrengthen_inhab_fires {env : VEnv} {U : Nat} {c : Lean.Name}
    (henv : env.Ordered) (hc : env.constants c = some ⟨0, .sort .zero⟩) :
    OnCtx [VExpr.sort (.succ .zero), VExpr.const c []] (env.IsType U) ∧
      Ctx.InhabLift env U (.skip .refl) [VExpr.const c []]
        [VExpr.sort (.succ .zero), VExpr.const c []] ∧
      env.HasType U [VExpr.sort (.succ .zero), VExpr.const c []]
        ((VExpr.bvar 0).lift' (.skip .refl)) ((VExpr.const c []).mkApp []) ∧
      ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' ([] : List VLevel) ∧
        as'.length = ([] : List VExpr).length ∧
        env.HasType U [VExpr.const c []] (.bvar 0) ((VExpr.const c us').mkApp as') := by
  have hW : Ctx.InhabLift env U (.skip .refl) [VExpr.const c []]
      [VExpr.sort (.succ .zero), VExpr.const c []] :=
    Ctx.InhabLift.refl.skip (t := .sort .zero) (VEnv.HasType.sort trivial)
  have hty : env.HasType U [VExpr.sort (.succ .zero), VExpr.const c []]
      ((VExpr.bvar 0).lift' (.skip .refl)) ((VExpr.const c []).mkApp []) := by
    have := VEnv.HasType.bvar (env := env) (U := U)
      (Γ := [VExpr.sort (.succ .zero), VExpr.const c []]) (i := 1) (A := _) (.succ .zero)
    simpa [VExpr.lift, VExpr.liftN] using this
  exact ⟨⟨⟨trivial, _, hasType_const_sortZero hc⟩, _, VEnv.HasType.sort trivial⟩,
    hW, hty, constAppTypeStrengthen_inhab henv hW (by simp) hty⟩

/-! ## The residual reduced to **one uninhabited binder**

The bound above is one half of a case split, and the other half is a genuine reduction of the
residual rather than a bound on it.  `Theory/Typing/Strengthen.lean` §12 ran exactly this move
for `IsDefEqU.weakN_iff` (`Strengthening1Uninhab.strengthening1`): a lift over an *inhabited*
entry is undone by instantiation, so the open statement may be restricted to entries with no
inhabitant.  The same move applies here, and it strips two things at once — the arbitrary
`Ctx.Lift'` becomes a **single** binder `Ctx.LiftN 1 k`, and that binder may be assumed
**uninhabited in its own prefix**.

`constAppTypeStrengthen_of_skipUninhab` is that reduction, and it is hole-free: it needs only
`env.Ordered`, `HasType.instN` and `Lift.depth_succ`/`Ctx.Lift'.of_cons_skip`.  In particular it
does **not** use `OnCtx.weak'_inv`, `IsDefEqU.weakN_iff`, Church--Rosser, `NormalEq.descend` or
`ParRed.weakN_inv`, and it does not consume the `OnCtx Γ'` premise of the residual at all. -/

/-- **The residual, reduced: one binder, and it may be assumed uninhabited.**  Compare
`VEnv.Strengthening1Uninhab` (`Theory/Typing/Strengthen.lean` §12), which is the same
restriction of the `weakN_iff` hole. -/
def VEnv.ConstAppSkipUninhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {e : VExpr} {c : Lean.Name} {us : List VLevel}
    {as : List VExpr},
    Ctx.LiftN 1 k Γ Γ' → (∀ u ∈ us, u.WF U) →
    (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ → ¬ env.HasType U Γ₀ e₀ A₀) →
    env.HasType U Γ' (e.liftN 1 k) ((VExpr.const c us).mkApp as) →
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.HasType U Γ e ((VExpr.const c us').mkApp as')

theorem constAppTypeStrengthen_of_skipUninhab_aux {env : VEnv} {U : Nat} (henv : env.Ordered)
    (H : env.ConstAppSkipUninhab U) {c : Lean.Name} :
    ∀ (n : Nat) {l : Lift} {Γ Γ' : List VExpr} {e : VExpr} {us : List VLevel} {as : List VExpr},
      l.depth = n → Ctx.Lift' l Γ Γ' → (∀ u ∈ us, u.WF U) →
      env.HasType U Γ' (e.lift' l) ((VExpr.const c us).mkApp as) →
      ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
        as'.length = as.length ∧ env.HasType U Γ e ((VExpr.const c us').mkApp as') := by
  intro n
  induction n with
  | zero =>
    intro l Γ Γ' e us as hd W hlv hty
    cases W.depth_zero hd
    rw [VExpr.lift'_depth_zero hd] at hty
    exact ⟨us, as, hlv, .rfl fun _ _ => rfl, rfl, hty⟩
  | succ n ih =>
    intro l Γ Γ' e us as hd W hlv hty
    obtain ⟨l, k, hdl, rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at hty
    have step : ∃ us₂ as₂, (∀ u ∈ us₂, u.WF U) ∧ List.Forall₂ (· ≈ ·) us₂ us ∧
        as₂.length = as.length ∧
        env.HasType U Γ₂ (e.lift' (Lift.consN l k)) ((VExpr.const c us₂).mkApp as₂) := by
      by_cases hin : ∃ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ₂ ∧ env.HasType U Γ₀ e₀ A₀
      · obtain ⟨Γ₀, A₀, e₀, hI, h₀⟩ := hin
        have h2 := hty.instN henv hI h₀
        rw [VExpr.inst_liftN, VExpr.inst_mkApp,
          show (VExpr.const c us).inst _ _ = VExpr.const c us from rfl] at h2
        exact ⟨us, _, hlv, .rfl fun _ _ => rfl, by simp, h2⟩
      · exact H W2 hlv (fun Γ₀ A₀ e₀ hI h₀ => hin ⟨Γ₀, A₀, e₀, hI, h₀⟩) hty
    obtain ⟨us₂, as₂, hlv₂, heq₂, hlen₂, hty₂⟩ := step
    obtain ⟨us', as', hlv', heq', hlen', hty'⟩ :=
      ih (by simpa using hdl) W1 hlv₂ hty₂
    exact ⟨us', as', hlv', List.Forall₂.trans (fun _ _ _ ha hb => ha.trans hb) heq' heq₂,
      hlen'.trans hlen₂, hty'⟩

/-- **The reduction.**  `ConstAppSkipUninhab` — one binder, uninhabited — implies the whole
residual `VEnv.ConstAppTypeStrengthen`, hole-free. -/
theorem constAppTypeStrengthen_of_skipUninhab {env : VEnv} {U : Nat} (henv : env.Ordered)
    (H : env.ConstAppSkipUninhab U) : env.ConstAppTypeStrengthen U := fun _ W hlv hty =>
  constAppTypeStrengthen_of_skipUninhab_aux henv H _ rfl W hlv hty

/-- The other direction, stated pointwise so that no hypothesis has to be invented: the
one-binder form **is** an instance of the residual, modulo the `OnCtx Γ'` premise the residual
carries.  So `ConstAppSkipUninhab` gives away nothing beyond that premise. -/
theorem VEnv.ConstAppTypeStrengthen.skip_step {env : VEnv} {U : Nat}
    (H : env.ConstAppTypeStrengthen U) {k : Nat} {Γ Γ' : List VExpr} {e : VExpr}
    {c : Lean.Name} {us : List VLevel} {as : List VExpr}
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN 1 k Γ Γ') (hlv : ∀ u ∈ us, u.WF U)
    (hty : env.HasType U Γ' (e.liftN 1 k) ((VExpr.const c us).mkApp as)) :
    ∃ us' as', (∀ u ∈ us', u.WF U) ∧ List.Forall₂ (· ≈ ·) us' us ∧
      as'.length = as.length ∧ env.HasType U Γ e ((VExpr.const c us').mkApp as') := by
  refine H hΓ' (Ctx.liftN_iff_lift'.1 W) hlv ?_
  rwa [← VExpr.lift'_consN_skipN, Lift.skipN_one] at hty
