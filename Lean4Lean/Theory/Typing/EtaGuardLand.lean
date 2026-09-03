import Lean4Lean.Theory.Inductive.IotaGen
import Lean4Lean.Theory.Typing.StructureRuleFree
import Lean4Lean.Theory.Typing.NoConfRepair
import Lean4Lean.Verify.Typing.NoConfGuard

/-!
# Discharging `hrf`: `RuleFreeHead` at *any* member of a structure block

`Theory/Typing/NoConfRepair.lean` §6 records three named gaps in the structure-eta repair.  Gap
(i) is the one every other lemma in that file pays for: four of its five declarations mentioning
`VEnv.IsStructureG` carry

    hrf : ∀ S D j T C, env.IsStructureG S D j T C → env.RuleFreeHead S

as a *hypothesis*, because `VEnv.IsStructure.ruleFreeHead`
(`Theory/Typing/StructureRuleFree.lean`) proves `RuleFreeHead S` only for the **narrow**
predicate — singleton block, index `0`, no recursive fields.  §1 below supplies the wide version
and §2 discharges `hrf` at every one of those four sites.

**The absence was re-verified, and the scan figure it was recorded with was wrong.**
`scripts/exists.lean`: `Lean4Lean.VEnv.IsStructureG.ruleFreeHead` — `NOT FOUND` (population 433).
`scripts/shape.lean` on `HEADS="Lean4Lean.VEnv.IsStructureG Lean4Lean.VEnv.RuleFreeHead"`:
**5 hits, not the 0 that `NoConfRepair.lean` §6 and `docs/vacuity-ledger.md` row 245f report** —
`ConstAppInvSI.constNoConf`, `notStructInhab_of_isType`, `notStructInhab_of_forallE`,
`ConstAppInvSI.of_isType`, `IsStructure.spine_inv_of_si`.  All five are in `NoConfRepair.lean`
and all five mention both heads because they *assume* `hrf`; none concludes it.  So the lemma is
genuinely absent, but "0 hits" was not the evidence for it — "5 hits, all of them the hypothesis"
is.  Recorded here because a scan summary that reads as stronger than the scan is exactly the
failure mode `shape.lean` exists to prevent.

## Why the wide version is not harder than the narrow one

`VEnv.WF.iotaTypeNotKey` (`Theory/Typing/DeltaUnique.lean` Part III) is *already* stated at an
arbitrary block index: `∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), env.defeqs
(D.iotaRule j q C) → ∀ df, env.defeqs df → (D.types.getD j default).name ∉ df.key`.  The narrow
proof instantiates it at `j = 0, q = 0` and reads `(D.types.getD 0 default).name = S` off
`IsStructure.types`.  Two substitutions carry it to index `j`:

* the type name — `VInductDecl'.getD_types` turns `IsStructureG.types : D.types[j]? = some T`
  into `D.types.getD j default = T`, and `IsStructureG.name` finishes;
* the ι-rule — the narrow `IsStructure.iotaDefeq` hands over rule `(0, 0)`; the wide
  `VEnv.IsStructureG.iotaDefeq` (`Verify/Typing/ProjGenTerm.lean`) hands over rule `(j, q)` for
  any `q` with `D.ctorsAll[q]? = some (j, C)`, and `VInductDecl'.mem_ctorsAll_gen` produces one
  from exactly the two fields `IsStructureG` carries.

`C.recFields = []` is never touched, which is what makes this work at a *recursive* member too —
the widening `IsStructureG` was introduced for.  Nothing is added to either predicate, so
`IsStructureG.mono` is untouched; the anti-monotonicity note at
`VEnv.IsStructure.ruleFreeHead` applies here verbatim and for the same reason (`VEnv.WF env` is
what carries the anti-monotone conclusion, not a field of the monotone hypothesis).
-/

namespace Lean4Lean

open VExpr

namespace VEnv

/-! ## 1. `RuleFreeHead` at any member of a declared block

### Two inputs, re-derived here so that §1 stays inside `Theory/`

The wide `iotaDefeq` and the `ctorsAll` membership both exist already, but in
`Verify/Typing/ProjGenTerm.lean` (`VEnv.IsStructureG.iotaDefeq`,
`VInductDecl'.mem_ctorsAll_gen`).  Using them would make §1 depend on a `Verify/` module, and
that would forbid the placement §1 actually wants: **inside
`Theory/Typing/StructureRuleFree.lean`**, next to the narrow lemma — which is imported *by*
`Verify/Typing/ProjSpineInv.lean` and hence by `NoConfRepair.lean`, so a `Verify/` import there
would be a cycle.  Both are two lines from `Theory/`-resident facts
(`VInductDecl'.iotaRule_mem` in `Theory/Inductive/IotaGen.lean`, `VEnv.addInduct'_defeqs` in
`Theory/Inductive/Lemmas.lean`), so they are re-derived rather than imported.  They are
deliberately `private`: the public names stay the `Verify/` ones. -/

/-- `VInductDecl'.mem_ctorsAll_gen`, re-derived (see the note above).  Same proof. -/
private theorem ctorsAll_mem_of_types {D : VInductDecl'} {j : Nat} {T : VIndType}
    {C : VIndCtor} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors) : (j, C) ∈ D.ctorsAll :=
  List.mem_flatMap.2 ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hTj,
    List.mem_map.2 ⟨C, hC, rfl⟩⟩

/-- `VEnv.IsStructureG.iotaDefeq`, re-derived (see the note above).  Same proof. -/
private theorem isStructureG_iotaDefeq {env : VEnv} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
    {T : VIndType} {C : VIndCtor} (H : env.IsStructureG S D j T C) {q : Nat} {C' : VIndCtor}
    (hqC : D.ctorsAll[q]? = some (j, C')) : env.defeqs (D.iotaRule j q C') := by
  obtain ⟨env₀, envF, hWF, hadd, hle⟩ := H.decl
  exact hle.defeqs (VEnv.addInduct'_defeqs hadd _ (D.iotaRule_mem hqC))

/-- **`RuleFreeHead` at the name of any member of a structure-like block.**  The wide analogue of
`VEnv.IsStructure.ruleFreeHead`: `IsStructureG` in place of `IsStructure`, so the block may have
any number of members, `S` may be any of them, and `C.recFields` is unconstrained.

Hypotheses are `VEnv.WF env` and `env.IsStructureG S D j T C` *as they stand* — no field is added
to `IsStructureG` and `IsStructureG.mono` is untouched.  See this file's header for why the
narrow proof transports without new work, and `VEnv.IsStructure.ruleFreeHead`'s docstring for why
the `WF` hypothesis cannot be traded for a field of the shape predicate (`RuleFreeHead` is
anti-monotone in `env`, `IsStructureG` is monotone). -/
theorem IsStructureG.ruleFreeHead {env : VEnv} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
    {T : VIndType} {C : VIndCtor} (henv : env.WF) (H : env.IsStructureG S D j T C) :
    env.RuleFreeHead S := by
  intro df hdf hhead
  have hname : (D.types.getD j default).name = S := by
    rw [VInductDecl'.getD_types H.types]; exact H.name
  have hC : C ∈ T.ctors := by rw [H.ctors]; exact List.mem_singleton_self _
  obtain ⟨q, hqC⟩ := List.mem_iff_getElem?.1 (ctorsAll_mem_of_types H.types hC)
  exact hname ▸ henv.iotaTypeNotKey D j q C (isStructureG_iotaDefeq H hqC) df hdf <|
    (henv.defeq_isDeclRule hdf).headConst?_mem_key hhead

/-- **`hrf` itself**, in the exact shape `NoConfRepair.lean`'s four lemmas take it: a single
`VEnv.WF` hypothesis now supplies the guard at *every* structure member of the environment at
once.  This is the declaration that closes gap (i). -/
theorem WF.isStructureG_ruleFreeHead {env : VEnv} (henv : env.WF) :
    ∀ (S : Lean.Name) (D : VInductDecl') (j : Nat) (T : VIndType) (C : VIndCtor),
      env.IsStructureG S D j T C → env.RuleFreeHead S :=
  fun _ _ _ _ _ H => IsStructureG.ruleFreeHead henv H

/-- Collapse test: the narrow lemma is the wide one at index `0`, so §1 subsumes
`VEnv.IsStructure.ruleFreeHead` rather than sitting beside it.  (`IsStructure.toG` drops
`noRec`, which §1 never reads.) -/
theorem IsStructure.ruleFreeHead_of_g {env : VEnv} {S : Lean.Name} {D : VInductDecl'}
    {T : VIndType} {C : VIndCtor} (henv : env.WF) (H : env.IsStructure S D T C) :
    env.RuleFreeHead S := IsStructureG.ruleFreeHead henv H.toG

end VEnv


/-! ## 2. The four `hrf`-carrying lemmas of `NoConfRepair.lean`, with `hrf` discharged

Each is the corresponding lemma of `Theory/Typing/NoConfRepair.lean` with the `hrf` hypothesis
removed and `VEnv.WF.isStructureG_ruleFreeHead` supplied in its place.  Nothing else changes, so
each inherits its original's cone and hole set exactly (the four census holes
`IsDefEqU.weakN_iff`, `IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`,
`NormalEq.descend`) — §1 adds no taint, it only removes a hypothesis.  **These are re-derivations
of already-tainted lemmas at the same taint, not new hole-free results.**

The names are suffixed rather than shadowing: `NoConfRepair.lean` is not mine to edit, so the
`hrf`-taking originals stay, and §5 records the exact edit that would retire them. -/

namespace VEnv

/-- `VEnv.notStructInhab_of_isType` with `hrf` discharged by §1. -/
theorem notStructInhab_of_isType_of_wf {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    {e : VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hty : env.IsType U Γ e) :
    ¬ env.StructInhab U Γ e :=
  notStructInhab_of_isType henv hΓ henv.isStructureG_ruleFreeHead hty

/-- `VEnv.notStructInhab_of_forallE` with `hrf` discharged by §1.  This is the sub-spine half:
with `hrf` gone the statement says outright that no Π-typed term of a well-formed environment
inhabits a structure, which is what makes the guard *free* at every proper sub-spine rather than
inherited. -/
theorem notStructInhab_of_forallE_of_wf {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    {f A B : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ f (.forallE A B)) : ¬ env.StructInhab U Γ f :=
  notStructInhab_of_forallE henv hΓ henv.isStructureG_ruleFreeHead hf

/-- `VEnv.ConstAppInvSI.of_isType` with `hrf` discharged.  Now **hypothesis-for-hypothesis
identical to `VEnv.constApp_inv_of_wf`** (`Verify/Typing/ConstSpineWF.lean`) apart from the single
extra `H : env.ConstAppInvSI U` — which is the whole point: the repair's remaining debt is one
premise, not two. -/
theorem ConstAppInvSI.of_isType_of_wf {env : VEnv} {U : Nat} (H : env.ConstAppInvSI U)
    (henv : env.WF) {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {c c' : Lean.Name}
    {ls ls' : List VLevel} {as as' : List VExpr}
    (hc : env.RuleFreeHead c) (hc' : env.RuleFreeHead c')
    (hty : env.IsType U Γ ((VExpr.const c ls).mkApp as))
    (h : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as')) :
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as' :=
  H.of_isType henv henv.isStructureG_ruleFreeHead hΓ hc hc' hty h

/-- `VEnv.ConstAppInvSI.constNoConf` with `hrf` discharged: the repaired premise implies
`VEnv.ConstNoConf` from `VEnv.WF` alone. -/
theorem ConstAppInvSI.constNoConf_of_wf {env : VEnv} {U : Nat} (H : env.ConstAppInvSI U)
    (henv : env.WF) : env.ConstNoConf U := H.constNoConf henv henv.isStructureG_ruleFreeHead

end VEnv

/-- `VEnv.IsStructure.spine_inv_of_si` with `hrf` discharged.  Binder order is
`VEnv.IsStructure.spine_inv`'s **exactly**, with `HSI` prepended — see §3 for why that matters and
for the machine-checked statement of the drop-in claim. -/
theorem VEnv.IsStructure.spine_inv_of_si_wf {env : VEnv} {U : Nat} {Γ : List VExpr}
    {S₁ S₂ : Lean.Name} {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    {us₁ us₂ : List VLevel} {as₁ as₂ : List VExpr} {e₁ e₂ : VExpr}
    (HSI : env.ConstAppInvSI U) (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsStructure S₁ D₁ T₁ C₁) (h₂ : env.IsStructure S₂ D₂ T₂ C₂)
    (ht₁ : env.HasType U Γ e₁ ((VExpr.const S₁ us₁).mkApp as₁))
    (ht₂ : env.HasType U Γ e₂ ((VExpr.const S₂ us₂).mkApp as₂))
    (H : env.IsDefEqU U Γ e₁ e₂) :
    S₁ = S₂ ∧ List.Forall₂ (· ≈ ·) us₁ us₂ ∧ List.Forall₂ (env.IsDefEqU U Γ) as₁ as₂ :=
  spine_inv_of_si henv henv.isStructureG_ruleFreeHead HSI hΓ h₁ h₂ ht₁ ht₂ H

/-! ## 3. What `spine_inv_of_si` still needs to be a drop-in, stated so it can be checked

`VEnv.IsStructure.spine_inv` is used at exactly two places, both in the module that declares it:
`Verify/Typing/ProjSpineInv.lean:86` (`h₁.spine_inv henv hΓ h₂ ht₁ ht₂ H`) and
`:150` (`(hS1.spine_inv henv hΓ₁ hS2 hty1 hty2 H).1`).  Both use **dot notation on the first
`IsStructure`**, so a replacement has to keep the explicit-argument order `henv, hΓ, h₂, ht₁,
ht₂, H` after the receiver.  §2's `spine_inv_of_si_wf` does.

After §1 there is **exactly one** thing left: `env.ConstAppInvSI U` has to follow from
`env.WF`.  That is the repair itself (`NoConfRepair.lean` §6, steps 1–2: the eta case of
`ParRed.constApp_inv` and of `NormalEq.constApp_inv`), and it is named here so the drop-in claim
is a theorem rather than a plan. -/

/-- **The one remaining premise.**  `VEnv.constApp_inv_of_wf` has this shape for the *unguarded*
statement; the repair has to reproduce it for the `¬ StructInhab`-guarded one. -/
def ConstAppInvSIFromWF : Prop := ∀ (env : VEnv) (U : Nat), env.WF → env.ConstAppInvSI U

/-- `VEnv.IsStructure.spine_inv`'s statement, named so the drop-in claim is machine-checked
rather than eyeballed: `spineInvStmt_today` inhabits it from the lemma in the tree, and
`spineInvStmt_of_repair` inhabits it from `ConstAppInvSIFromWF`.  Two inhabitants of one `Prop`
is the strongest sense in which "drop-in" is checkable without editing the call sites. -/
def SpineInvStmt : Prop :=
  ∀ {env : VEnv} {U : Nat} {Γ : List VExpr} {S₁ S₂ : Lean.Name} {D₁ D₂ : VInductDecl'}
    {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor} {us₁ us₂ : List VLevel} {as₁ as₂ : List VExpr}
    {e₁ e₂ : VExpr}, env.WF → OnCtx Γ (env.IsType U) → env.IsStructure S₁ D₁ T₁ C₁ →
    env.IsStructure S₂ D₂ T₂ C₂ → env.HasType U Γ e₁ ((VExpr.const S₁ us₁).mkApp as₁) →
    env.HasType U Γ e₂ ((VExpr.const S₂ us₂).mkApp as₂) → env.IsDefEqU U Γ e₁ e₂ →
    S₁ = S₂ ∧ List.Forall₂ (· ≈ ·) us₁ us₂ ∧ List.Forall₂ (env.IsDefEqU U Γ) as₁ as₂

/-- `SpineInvStmt` is not stronger than what the tree has today: the existing lemma inhabits it.
This is the half that certifies `SpineInvStmt` is a faithful transcription. -/
theorem spineInvStmt_today : SpineInvStmt :=
  fun henv hΓ h₁ h₂ ht₁ ht₂ H => VEnv.IsStructure.spine_inv henv hΓ h₁ h₂ ht₁ ht₂ H

/-- The other direction of the transcription check: `SpineInvStmt` **delivers**
`VEnv.IsStructure.spine_inv`'s conclusion at its hypotheses, so "the same `Prop`" is not doing
hidden work in one direction only.  Together with `spineInvStmt_today` this pins `SpineInvStmt` to
`spine_inv`'s statement from both sides. -/
theorem spine_inv_of_spineInvStmt (Hs : SpineInvStmt) {env : VEnv} {U : Nat} {Γ : List VExpr}
    {S₁ S₂ : Lean.Name} {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    {us₁ us₂ : List VLevel} {as₁ as₂ : List VExpr} {e₁ e₂ : VExpr}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsStructure S₁ D₁ T₁ C₁) (h₂ : env.IsStructure S₂ D₂ T₂ C₂)
    (ht₁ : env.HasType U Γ e₁ ((VExpr.const S₁ us₁).mkApp as₁))
    (ht₂ : env.HasType U Γ e₂ ((VExpr.const S₂ us₂).mkApp as₂))
    (H : env.IsDefEqU U Γ e₁ e₂) :
    S₁ = S₂ ∧ List.Forall₂ (· ≈ ·) us₁ us₂ ∧ List.Forall₂ (env.IsDefEqU U Γ) as₁ as₂ :=
  Hs henv hΓ h₁ h₂ ht₁ ht₂ H

/-- **The drop-in, complete modulo the one named premise.**  With gap (i) closed, the whole
re-basing cost of the 156 transitive users of `VEnv.IsDefEq.constApp_inv` that reach it only
through `spine_inv` is `ConstAppInvSIFromWF` — and nothing else. -/
theorem spineInvStmt_of_repair (Hsi : ConstAppInvSIFromWF) : SpineInvStmt :=
  fun henv hΓ h₁ h₂ ht₁ ht₂ H =>
    VEnv.IsStructure.spine_inv_of_si_wf (Hsi _ _ henv) henv hΓ h₁ h₂ ht₁ ht₂ H

/-! ## 4. The two smaller gaps of `NoConfRepair.lean` §6

### (ii) `StructInhab` transport along `IsDefEqU`

Three lines, as advertised — with one correction to the advertisement: the lemma it needs is
`VEnv.HasType.defeqU_l` (`Theory/Typing/UniqueTyping.lean`).  **`HasType.defeqU_l'` — the primed
name `NoConfRepair.lean` §6 (ii) and `docs/vacuity-ledger.md` row 245f both cite — does not
exist** (`scripts/exists.lean`: `NOT FOUND`).

### (iii) `¬ IsProof` does not go away, and here it is as a theorem

`NoConfRepair.lean` §6 (iii) argues this in prose from `not_constConfUG_ncPropEnv`, which deletes
*both* guards.  §4.2 below makes it the exact statement: **`¬ StructInhab` alone**, with
`¬ IsProof` deleted and `RuleFreeHead` kept, is false at a `VEnv.WF` environment.  The witness is
sharper than the both-guards-deleted one, because `¬ StructInhab` genuinely *holds* at it rather
than being absent: `ncPropEnv` has no `defeqs` at all, so it holds no inductive block, so
`StructInhab` is refutable there for **every** term (§4.2's `not_structInhab_ncPropEnv`) — while
the violating pair still exists, by `proofIrrel`.  So the two guards are independent and
`ConstAppInvSI`'s carrying both is forced, not cautious. -/

namespace VEnv

/-- **(ii) `StructInhab` transports along a conversion.**  The exact analogue of
`VEnv.IsProof.defeqU` (`Theory/Typing/Injectivity.lean`), and the step
`IsDefEq.constApp_inv`'s proof needs to move the new guard across a reduction, where the existing
proof's `hnp'` moves `¬ IsProof`.

Tainted, and unavoidably: the only route is `VEnv.HasType.defeqU_l`, whose cone reaches
`IsDefEqU.forallE_inv_stratified`.  Stated at the weakest hypotheses that admit it. -/
theorem StructInhab.defeqU {env : VEnv} {U : Nat} {Γ : List VExpr} {e₁ e₂ : VExpr}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (h : env.IsDefEqU U Γ e₁ e₂)
    (hs : env.StructInhab U Γ e₁) : env.StructInhab U Γ e₂ := by
  obtain ⟨S, D, j, T, C, us, ps, hS, hidx, hrec, he⟩ := hs
  exact ⟨S, D, j, T, C, us, ps, hS, hidx, hrec, he.defeqU_l henv hΓ h⟩

/-- …and the contrapositive, which is the direction the guard is threaded in. -/
theorem notStructInhab_defeqU {env : VEnv} {U : Nat} {Γ : List VExpr} {e₁ e₂ : VExpr}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (h : env.IsDefEqU U Γ e₁ e₂)
    (hs : ¬ env.StructInhab U Γ e₂) : ¬ env.StructInhab U Γ e₁ :=
  fun hs₁ => hs (hs₁.defeqU henv hΓ h)

/-! ### §4.1 An environment with no rules holds no structure

Used twice below: it is what makes the `¬ StructInhab` guard *true* at §4.2's witness, and it is
also the sharpest non-vacuity check on `StructInhabAt` in the other direction — the predicate is
refutable, not just satisfiable. -/

/-- **No `defeqs`, no structure.**  `IsStructureG.decl` places the block's ι-rules in the
environment, so an environment whose `defeqs` is empty satisfies `IsStructureG` for nothing.
(Hole-free: the route is `addInduct'_defeqs`, not typing.) -/
theorem IsStructureG.not_of_no_defeqs {env : VEnv} (hd : ∀ df, ¬ env.defeqs df)
    {S : Lean.Name} {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor} :
    ¬ env.IsStructureG S D j T C := by
  intro H
  have hC : C ∈ T.ctors := by rw [H.ctors]; exact List.mem_singleton_self _
  obtain ⟨q, hqC⟩ := List.mem_iff_getElem?.1 (ctorsAll_mem_of_types H.types hC)
  exact hd _ (isStructureG_iotaDefeq H hqC)

/-- …hence the guard holds everywhere at such an environment. -/
theorem not_structInhabAt_of_no_defeqs {env : VEnv} (hd : ∀ df, ¬ env.defeqs df)
    {Ty : VExpr → VExpr → Prop} {e : VExpr} : ¬ env.StructInhabAt Ty e := by
  rintro ⟨S, D, j, T, C, us, ps, hS, -, -, -⟩
  exact IsStructureG.not_of_no_defeqs hd hS

end VEnv

/-! ### §4.2 `¬ StructInhab` alone is not enough -/

/-- Every term of `ncPropEnv` (`Verify/Typing/NoConfGuard.lean`: three axioms, `defeqs = False`,
`VEnv.WF`) satisfies the new guard. -/
theorem VEnv.not_structInhab_ncPropEnv {U : Nat} {Γ : List VExpr} {e : VExpr} :
    ¬ VEnv.ncPropEnv.StructInhab U Γ e :=
  VEnv.not_structInhabAt_of_no_defeqs (fun _ h => h)

/-- **(iii) as a theorem: dropping `¬ IsProof` and keeping `¬ StructInhab` is false.**

The guards `RuleFreeHead` and `¬ StructInhab` are both *satisfied* at the witness
(`VEnv.ruleFreeHead_ncPropEnv`, `VEnv.not_structInhab_ncPropEnv`) and no-confusion still fails,
by `proofIrrel` (`VEnv.ncPropEnv_link`: `mkP Prop ≡ mkQ (Prop → Prop)` at a `VEnv.WF`
environment).  So `VEnv.ConstAppInvSI` must keep `¬ IsProof`; the repair adds a guard, it does not
trade one for another.

Hole-free — `ncPropEnv_link` is `proofIrrel` applied to two `constDF`s, and §4.1 is
`addInduct'_defeqs`.  Contrast `VEnv.not_isType_ncPropEnv_lhs`, which is tainted because
`IsType.not_isProof` is. -/
theorem VEnv.structInhabOnlyNoConf_false :
    ¬ ∀ {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
      VEnv.ncPropEnv.RuleFreeHead c → VEnv.ncPropEnv.RuleFreeHead c' →
      ¬ VEnv.ncPropEnv.StructInhab 0 [] ((VExpr.const c ls).mkApp as) →
      VEnv.ncPropEnv.IsDefEqU 0 [] ((VExpr.const c ls).mkApp as)
        ((VExpr.const c' ls').mkApp as') → c = c' := fun H =>
  absurd (H (c := `mkP) (c' := `mkQ) (ls := []) (ls' := []) (as := [vprop])
    (as' := [vpropArrow]) (VEnv.ruleFreeHead_ncPropEnv _) (VEnv.ruleFreeHead_ncPropEnv _)
    VEnv.not_structInhab_ncPropEnv VEnv.ncPropEnv_link) (by decide)

/-! ## 5. Vacuity, both ways

The discipline of `docs/vacuity-ledger.md` §0, applied to everything §1–§4 exhibits.  Two
distinct failure modes, and both are checked:

* a **relation** that relates nothing satisfies every no-confusion statement;
* a **guard** that no real environment satisfies is not a repair, and a guard that *every* term
  satisfies is not a guard.

The brief's specific requirement is checked in §5.2: `¬ StructInhab` is restrictive at a
**positive-field** structure, not only at a zero-field one, because the failure was shown not to
be zero-field-only (`zeroFieldOnlyNoConf_false_for_IsDefEqSE`). -/

/-! ### §5.1 §1's hypothesis is satisfiable and its conclusion is refutable -/

namespace MutField

/-- **§1 at the zero-field member of `bigEnv`**, block index `0`. -/
theorem bigEnv_ruleFreeHead_A_general : bigEnv.RuleFreeHead `MutField.A :=
  VEnv.IsStructureG.ruleFreeHead bigEnv_wf bigEnv_IsStructureG_A

/-- **§1 at the ONE-FIELD member of `bigEnv`**, block index `1` — the case the narrow
`VEnv.IsStructure.ruleFreeHead` cannot reach at all, since `MutField.decl` has two types.
`MutField.bCtor_has_a_field` is the field count, so "positive field" is not a paraphrase.

Note what this replaces: `MutField.bigEnv_ruleFreeHead` gets the same conclusion by `decide` on
`bigEnv.defeqs`, i.e. by computation at one environment.  This gets it from `VEnv.WF` and the
shape predicate, at any environment — which is the point of gap (i). -/
theorem bigEnv_ruleFreeHead_B_general : bigEnv.RuleFreeHead `MutField.B :=
  VEnv.IsStructureG.ruleFreeHead bigEnv_wf bigEnv_IsStructureG_B

/-- Cross-check: the general route and the `decide` route agree at `B`.  (Both are `Prop`s about
the same environment, so this is `rfl`-level; it is here because a mismatch would mean one of the
two is about a different environment than advertised.) -/
example : bigEnv.RuleFreeHead `MutField.B ∧ bigEnv.RuleFreeHead `MutField.B :=
  ⟨bigEnv_ruleFreeHead_B_general, bigEnv_ruleFreeHead (by decide) (by decide)⟩

end MutField

/-- **§1's conclusion is refutable**, so §1 is not proving a tautology: a δ-rule for `v` is headed
by `v.name`.  (`StructureRuleFree.lean` §3 has this for the narrow lemma; repeated here because
§1 is a different statement and its non-vacuity should not be by reference.) -/
example (v : VDefVal) : ¬ (VEnv.empty.addDefEq v.toDefEq).RuleFreeHead v.name :=
  fun h => h v.toDefEq (.inl rfl) rfl

/-- **§1's hypothesis is refutable too** — `IsStructureG` is not satisfied by everything, so the
lemma is not "`RuleFreeHead` always".  §4.1 at `ncPropEnv`. -/
example {S : Lean.Name} {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor} :
    ¬ VEnv.ncPropEnv.IsStructureG S D j T C :=
  VEnv.IsStructureG.not_of_no_defeqs (fun _ h => h)

/-! ### §5.2 The guard is non-trivial at a positive-field structure, both directions -/

namespace MutField

/-- **The guard is FALSE at the eta rule's left endpoint at the one-field member.**  `bar` is an
axiom inhabitant of `MutField.B`, whose constructor has one field; `MutField.bigEnv_structEtaSE_bar`
is the fourteenth constructor firing at it, with a genuine `projTermG` argument on the right.  So
`¬ StructInhab` excludes that eta instance, and it does so at a positive-field structure — which
is what `zeroFieldOnlyNoConf_false_for_IsDefEqSE` says a repair must do.

Hole-free: `structEta_lhs_structInhabAt` (cone 84) plus `bigEnv_bar_hasType`. -/
theorem bigEnv_structInhab_bar :
    bigEnv.StructInhab 0 [] ((VExpr.const `MutField.bar []).mkApp []) :=
  VEnv.structEta_lhs_structInhabAt bigEnv_IsStructureG_B rfl rfl bigEnv_bar_hasType

/-- …and at the *right* endpoint's head as well is not claimed — `B.mk`'s spine there carries a
projection argument, so the pair is excluded from the left only, exactly as `ConstNoConf` guards
only its left spine.  What *is* checked is the second axiom at the zero-field member, so both
members of the block are covered. -/
theorem bigEnv_structInhab_foo2 :
    bigEnv.StructInhab 0 [] ((VExpr.const `MutField.foo2 []).mkApp []) :=
  VEnv.structEta_lhs_structInhabAt bigEnv_IsStructureG_A rfl rfl bigEnv_foo2_hasType

/-- **The guard is TRUE at the one-field structure's own type**, via §2 — so it is available where
consumers need it, and available *generally*: `hrf` is discharged by §1 rather than computed.
This is the end-to-end check that §1 + §2 do what gap (i) was blocking.

Tainted at the four census holes, inherited from `notStructInhab_of_isType` (universe uniqueness);
`MutField.unitEnv_not_isType_foo` is tainted for the same reason. -/
theorem bigEnv_not_structInhab_B :
    ¬ bigEnv.StructInhab 0 [] (VExpr.const `MutField.B []) :=
  VEnv.notStructInhab_of_isType_of_wf bigEnv_wf trivial ⟨_, bigEnv_B_hasType⟩

/-- The same at the zero-field member, for contrast with §5.2's first result: at `A` the guard
holds of the *type* and fails of its *inhabitants*. -/
theorem bigEnv_not_structInhab_A :
    ¬ bigEnv.StructInhab 0 [] (VExpr.const `MutField.A []) :=
  VEnv.notStructInhab_of_isType_of_wf bigEnv_wf trivial ⟨_, bigEnv_A_hasType⟩

/-- **The guard separates**, at a positive-field structure, in one statement: `B` satisfies it and
`bar` does not, at the same well-formed environment.  A guard that failed to separate would be
either vacuous or trivial. -/
theorem bigEnv_guard_separates_at_B :
    ¬ bigEnv.StructInhab 0 [] (VExpr.const `MutField.B []) ∧
      bigEnv.StructInhab 0 [] ((VExpr.const `MutField.bar []).mkApp []) :=
  ⟨bigEnv_not_structInhab_B, bigEnv_structInhab_bar⟩

end MutField

/-! ### §5.3 `SpineInvStmt`'s hypotheses are satisfiable

The drop-in target quantifies over the **narrow** `VEnv.IsStructure`, which no `MutField`
environment satisfies (`MutField.decl` has two types).  So the check has to be run elsewhere, and
`Lean4Lean.barEnv` (`Verify/Typing/ProjLevelWitness.lean`) is the witness: a *singleton* block
whose constructor has **two** fields (`barCtor.fields = [barField0, barField1]`).

Its `VEnv.WF` was not in the tree — `Lean4Lean.EtaUnit.barEnv_wf` is a different `barEnv` — so it
is proved here, by the one-step chain `addInduct'` from `VEnv.empty` that `barEnv_eq` already
supplies. -/

/-- `Lean4Lean.barEnv` is well formed: one `.induct` step from `VEnv.empty`. -/
theorem barEnv_wf' : VEnv.WF barEnv :=
  ⟨[.induct barDecl], .decl (.induct barDecl_WF barEnv_eq.choose_spec) .empty⟩

/-- **`SpineInvStmt` is not vacuous**: a well-formed environment with a narrow structure whose
constructor has two fields exists, so the statement §3 certifies as the drop-in target has
satisfiable hypotheses.  (The full instantiation also needs two `HasType`s at `Bar`'s spine; those
are `barEnv_Bar_hasType`-shaped and not reproduced — what is checked here is the pair the
*environment-side* hypotheses ask for.) -/
theorem spineInvStmt_premises_satisfiable :
    VEnv.WF barEnv ∧ barEnv.IsStructure `Bar barDecl barType barCtor ∧
      barCtor.fields.length = 2 :=
  ⟨barEnv_wf', barEnv_IsStructure, rfl⟩

/-- …and §1 applies there too, through `IsStructure.toG`: the wide lemma subsumes the narrow one
at a real narrow structure, not only in the abstract. -/
theorem barEnv_ruleFreeHead_general : barEnv.RuleFreeHead `Bar :=
  VEnv.IsStructureG.ruleFreeHead barEnv_wf' barEnv_IsStructure.toG

/-! ## 6. The exact edits this licenses elsewhere, none of them made here

Nothing outside this file and `docs/handoff-etaguardland.md` is touched.  The three edits below
are stated for the orchestrator; each is mechanical once §1 exists.

### 6.1 `Theory/Typing/StructureRuleFree.lean` — move §1 in, delete §2's narrow special case

§1 compiles with **only** `Theory.Inductive.IotaGen` and `Theory.Typing.StructureRuleFree` as
imports (verified: standalone elaboration, `sorryAx`-free, no `Verify/` module in the import
closure — which is why the two inputs are re-derived privately above rather than taken from
`Verify/Typing/ProjGenTerm.lean`).  `IotaGen`'s import closure is 15 modules, contains no
`Verify/` module and does not contain `StructureRuleFree`, so adding

    import Lean4Lean.Theory.Inductive.IotaGen

to `StructureRuleFree.lean` is cycle-free.  Then §1's three declarations plus the two private
helpers move there verbatim, and `VEnv.IsStructure.ruleFreeHead` becomes
`IsStructureG.ruleFreeHead henv H.toG` — i.e. §1's `IsStructure.ruleFreeHead_of_g`.  Doing this
makes §1 visible to `Verify/Typing/ProjSpineInv.lean` and hence to `NoConfRepair.lean`, which is
what the next two edits need.

### 6.2 `Theory/Typing/NoConfRepair.lean` — drop `hrf` from four signatures

With 6.1 in place, delete the hypothesis

    (hrf : ∀ S D j T C, env.IsStructureG S D j T C → env.RuleFreeHead S)

from `VEnv.notStructInhab_of_isType`, `VEnv.notStructInhab_of_forallE`,
`VEnv.ConstAppInvSI.of_isType` and `VEnv.IsStructure.spine_inv_of_si`, replacing each use of
`hrf _ _ _ _ _ hS` by `IsStructureG.ruleFreeHead henv hS` and each pass-through by
`henv.isStructureG_ruleFreeHead`.  `ConstAppInvSI.constNoConf` loses it by propagation.  §2 above
is exactly those five statements, proved through the unedited originals, so the edit is
type-checked before it is made.  Gap (i) of that file's §6 then reads *closed*, and its
sentence "for `IsStructureG` at a block index `j` nothing in the tree does" is retired.

Two further corrections to that file's §6 that are **not** about `hrf`:

* (ii) cites `HasType.defeqU_l'`.  That name does not exist; the lemma is
  `VEnv.HasType.defeqU_l`, and §4 uses it.
* §6 (i) and `docs/vacuity-ledger.md` row 245f both record the `shape.lean` evidence as
  "0 hits, heads resolved".  Re-run on 434 modules it is **5 hits** — the four `hrf`-carrying
  lemmas plus `ConstAppInvSI.constNoConf`.  The conclusion is unchanged (none of the five
  *concludes* `RuleFreeHead`), but the recorded evidence was for a stronger claim than the scan
  supports.

### 6.3 `Verify/Typing/ProjSpineInv.lean` — one line, and only when the repair lands

`VEnv.IsStructure.spine_inv`'s **statement** does not change; only its body does, and only once
`ConstAppInvSIFromWF` is a theorem.  Today:

    VEnv.constApp_inv_of_wf henv U hΓ (h₁.ruleFreeHead henv) (h₂.ruleFreeHead henv)
      (ht₁.isType henv hΓ) ((H.of_l henv hΓ ht₁).uniqU henv hΓ ht₂)

after (writing `Hsi : ConstAppInvSIFromWF`):

    (Hsi env U henv).of_isType_of_wf henv hΓ (h₁.ruleFreeHead henv) (h₂.ruleFreeHead henv)
      (ht₁.isType henv hΓ) ((H.of_l henv hΓ ht₁).uniqU henv hΓ ht₂)

`spineInvStmt_of_repair` above is that substitution, elaborated.  Both call sites
(`ProjSpineInv.lean:86` and `:150`) are dot-notation applications with explicit arguments
`henv, hΓ, h₂, ht₁, ht₂, H`, and neither changes.

### 6.4 What is still open, precisely

`ConstAppInvSIFromWF` — and, after §1 and §2, **nothing else** on this route.  Its two new
sub-steps are the ones `NoConfRepair.lean` §6 names: the eta case of `ParRed.constApp_inv`
(`Verify/Typing/ConstSpine.lean:115`) and of `NormalEq.constApp_inv` (`:186`).  §4's
`StructInhab.defeqU` is the transport those need, and §2's `notStructInhab_of_forallE_of_wf` is
the sub-spine discharge, now hypothesis-free.

**Cone arithmetic, for the record.**  `VEnv.IsStructure.spine_inv_of_si_wf` measures **7538**,
which is `VEnv.IsStructure.spine_inv`'s own figure exactly (7538) — so on this route the repair
is cone-neutral, not merely bounded.  `IsStructureG.ruleFreeHead` is 4093 against the narrow
lemma's 4091: two constants, both of them §1's private helpers. -/

end Lean4Lean
