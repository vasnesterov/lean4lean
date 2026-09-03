import Lean4Lean.Verify.Inductive.ValAtPrice

/-!
# The restriction step at `SpineHargsK`: the hypothesis is still the consequence

`docs/handoff-restrict.md` §3 measured the restriction route's hypothesis (`σ.WF`, whose `val`
field is `VIndRestore.ValAt`) against the datum and reported a **sandwich, not a circle**: the
datum implies `ValAt`, and the converse "would need `of_mkApp`", so no equivalence was claimed.
`docs/handoff-valat.md` §3 then weakened the input to `VInductDecl'.SpineHargsK` — one `HasArgs`
per companion member, the datum's `ty` half — and proved `valAt_of_spineHargsK`.

This file answers: **with `SpineHargsK` as the input, does the restriction step close?**

**No — and the sandwich is now a closed cycle.**  §1 composes three already-proved arrows

    ArgsTypedK K e₁ occ  --of_argsTypedK-->  SpineHargsK K e₁ occ
                         --valAt_of_spineHargsK-->  ValAt D K e₂ e₁
                         --restrict_of_val (+ datum at e₂)-->  ArgsTypedK K e₁ occ

so that, modulo the datum at `e₂` (which `D.WF` supplies) and side conditions that are jointly
inhabited (§3), all three are **equivalent**.  Two consequences:

* the restriction step does **not** close at `SpineHargsK`: its hypothesis is the `ty` projection
  of its own conclusion, so the reduction is a genuine *shrink of the discharge site* and no
  progress at all towards a *derivation*;
* the equivalence is obtained by going **forwards** through the restriction, not by inverting an
  application, so `ValAt → SpineHargsK` holds here **without `of_mkApp`**.  That corrects
  `docs/handoff-valat.md` §2(a) ("`ValAt → SpineHargsK` is `of_mkApp`"), which is true
  unconditionally and false in this configuration.

§2 answers the question a closed cycle raises: **can it be entered?**  It can, in exactly one way.
Two more nodes are added, and neither is a judgement — both are *transports* from `e₂` to `e₁`
(`VInductDecl'.SpineStrengthen`, `VIndRestore.ValStrengthen`), and both have a **free** antecedent,
so both are equivalent to the nodes they transport into.  `restrictStep_entry` is the punchline:

    D.ArgsTypedK K e₁ occ  ↔  R.ValStrengthen D K e₂ e₁

*the whole residual is one constant-strengthening step — one closed `HasType`, per companion member,
across one `addConstList`* — and `valStrengthen_endpoints_clean` shows both endpoints of that
judgement are already `e₁`-clean, so it is a **plain** instance of `VEnv.AxiomConservativityWF`
(`RestrictCompanion.lean` §4), which is provably equivalent to `StrengtheningTarget`, one of
`UniqueTyping.lean`'s thirteen holes.  Since `restrictStep_entry` is an `↔`, **no node of the cycle
is a cheaper door.**

§3 exhibits the side conditions jointly inhabited, with nothing hypothesised, at the *parameterised*
nested block (`ntreeAux`, `np = 1`, `uvars = 1`) that `docs/handoff-valat.md` §4 flagged as not yet
instantiated — together with the datum at `e₂` and, at that witness, a discharged instance of node 5.
§4 audits the side conditions and corrects one over-claim of my own §0 (the config's `wf` field is
*not* residual-blind: `D.WF` + `stage₂` is where the datum at `e₂` comes from).

Nothing here makes the flip, closes `tryEtaStructCore.WF` / `isDefEqUnitLike.WF`, or uses
`VEnv.HasArgs.of_mkApp`.  Nothing here proves the strengthening instance either: §2 *locates* the
residual on the recorded hole, it does not discharge it.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkLams mkApp mkPi splitPis bvars)

/-! ## §0 The side conditions, bundled

Every hypothesis the arrows share, in one place, so that "jointly inhabited" is a single
existential (§3) rather than a list of promises.

**NINE fields, not eleven.**  The first version of this structure carried `occurs` and `argsNoK` as
fields; both are consequences of `built` (`RestrictStepCfg.occurs`, `RestrictStepCfg.argsFree`), and
§4 is the audit.  The nine that remain are facts about the staging and the block — with the caveat
§4 also records: `wf` is *not* residual-blind in the sense the first version's docstring suggested,
because `D.WF` + `stage₂` is where the datum at `e₂` comes from. -/

/-- The configuration of the nested restriction step: the pre-block environment `env`, the
`addIndTypes` staging `e₂` where `D.WF.ctors` types the spine, the `addIndTypesC` staging `e₁`
where §8.7 consumes, and the presentation `R` / occurrence data `occ`. -/
structure RestrictStepCfg (D : VInductDecl') (R : VIndRestore) (K : List Name)
    (env e₂ e₁ : VEnv) (occ : Nat → VNestedOcc) : Prop where
  ordered : env.Ordered
  ordered₁ : e₁.Ordered
  wf : D.WF env
  built : D.Built R K env occ
  fresh : (R.csubstTy D K).FreshIn env
  closed : (R.csubstTy D K).Closed
  stage₂ : env.addIndTypes D = some e₂
  stage₁ : env.addIndTypesC D K = some e₁
  lvls : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ l ∈ R.tyLvls j, l.WF D.uvars

/-- Every type in an `IsType`-context of an ordered environment is constant-closed. -/
theorem ctxConstsIn_of_onCtx {env : VEnv} (henv : env.Ordered) {U : Nat} :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → CtxConstsIn env.contains Γ
  | [], _ => trivial
  | _ :: Γ, h => by
    obtain ⟨h1, u, h2⟩ := h
    have ih := ctxConstsIn_of_onCtx henv (Γ := Γ) h1
    exact ⟨ih, (h2.constsIn henv.constsIn ih).1⟩

namespace RestrictStepCfg

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
  {occ : Nat → VNestedOcc}

/-- `e₁` is an extension of the pre-block environment: it is an `addConstList`. -/
theorem le₁ (H : RestrictStepCfg D R K env e₂ e₁ occ) : env ≤ e₁ := by
  have := H.stage₁; rw [VEnv.addIndTypesC] at this; exact VEnv.addConstList_le this

/-- The block's parameters mention only pre-block constants. -/
theorem paramsIn (H : RestrictStepCfg D R K env e₂ e₁ occ) :
    ∀ B ∈ D.params.reverse, B.ConstsIn env.contains :=
  ctxConstsIn_mem (ctxConstsIn_of_onCtx H.ordered H.wf.params)

/-- …hence they are types at `e₁` too. -/
theorem params₁ (H : RestrictStepCfg D R K env e₂ e₁ occ) :
    OnCtx D.params.reverse (e₁.IsType D.uvars) :=
  OnCtx.mono (fun h => h.mono H.le₁) H.wf.params

/-- **`occurs` IS NOT A FIELD** — it is `Built.occurs`, forgetting `OccursN`'s extra clauses.
See §4: two of what looked like eleven side conditions are consequences of `built`. -/
theorem occurs (H : RestrictStepCfg D R K env e₂ e₁ occ) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → (occ j).Occurs env :=
  fun j T hT hK => (H.built.occurs j T hT hK).toOccurs

/-- **…AND NEITHER IS THE SPINE'S CLEANLINESS.**  The spine avoids `csubstTy`'s domain, which is
inside `K`, and `Built.kfresh.argsNoK` is exactly that — *guarded* by `T.name ∈ K`, which is the
only form the cycle needs (§4). -/
theorem argsFree (H : RestrictStepCfg D R K env e₂ e₁ occ) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ a ∈ (occ j).args, a.NoCSubst (R.csubstTy D K) := fun j T hT hK a ha =>
  VExpr.NoConsts.noCSubst
    (fun _ hn => by
      by_contra hK'
      exact hn (VIndRestore.csubstTy_eq_none hK'))
    (H.built.kfresh.argsNoK j T hT hK a ha)

end RestrictStepCfg

/-! ## §1 The cycle over the three known nodes -/

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
  {occ : Nat → VNestedOcc}

/-- Arrow 1 → 2, restated at the configuration: free. -/
theorem cyc_datum_to_spine (H : D.ArgsTypedK K e₁ occ) : D.SpineHargsK K e₁ occ :=
  VInductDecl'.SpineHargsK.of_argsTypedK H

/-- Arrow 2 → 3: `ValAtPrice.lean` §3. -/
theorem cyc_spine_to_val (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (hS : D.SpineHargsK K e₁ occ) : R.ValAt D K e₂ e₁ :=
  valAt_of_spineHargsK C.built hS C.le₁ C.params₁ C.stage₂ C.lvls

/-- Arrow 3 → 1: `RestrictCompanion.lean` §11a, with the datum at `e₂` as the extra input. -/
theorem cyc_val_to_datum (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (H₂ : D.ArgsTypedK K e₂ occ) (hval : R.ValAt D K e₂ e₁) : D.ArgsTypedK K e₁ occ :=
  fun j T hT hK => (H₂ j T hT hK).restrictC'
    (R.csubstTy_WF_of_val C.ordered C.ordered₁ C.wf C.fresh C.closed C.stage₂ C.stage₁ hval)
    C.ordered C.fresh (C.occurs j T hT hK) C.paramsIn (C.argsFree j T hT hK)

/-- **THE CYCLE.**  Given the datum at `e₂` — which is what `D.WF.ctors` supplies — the three
candidate residuals are the same statement.  Read this as the answer to "does the restriction step
close at `SpineHargsK`?": it does not, because its hypothesis is the `ty` projection of its own
conclusion, and the loop is closed. -/
theorem restrictStep_cycle (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (H₂ : D.ArgsTypedK K e₂ occ) :
    (D.ArgsTypedK K e₁ occ ↔ D.SpineHargsK K e₁ occ) ∧
    (D.SpineHargsK K e₁ occ ↔ R.ValAt D K e₂ e₁) ∧
    (R.ValAt D K e₂ e₁ ↔ D.ArgsTypedK K e₁ occ) :=
  ⟨⟨cyc_datum_to_spine, fun hS => cyc_val_to_datum C H₂ (cyc_spine_to_val C hS)⟩,
   ⟨cyc_spine_to_val C, fun hv => cyc_datum_to_spine (cyc_val_to_datum C H₂ hv)⟩,
   ⟨cyc_val_to_datum C H₂, fun hA => cyc_spine_to_val C (cyc_datum_to_spine hA)⟩⟩

/-- **THE CORRECTION TO `docs/handoff-valat.md` §2(a).**  `ValAt → SpineHargsK` is stated there as
needing `VEnv.HasArgs.of_mkApp`.  Unconditionally it does; *in this configuration* it does not —
the route is forwards through the restriction and back down the `ty` projection.  No `of_mkApp`. -/
theorem spineHargsK_of_valAt (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (H₂ : D.ArgsTypedK K e₂ occ) (hval : R.ValAt D K e₂ e₁) : D.SpineHargsK K e₁ occ :=
  cyc_datum_to_spine (cyc_val_to_datum C H₂ hval)

end VIndRestore

/-! ## §2 The entry point, named: one constant-strengthening step

§1 says the three nodes are the same statement.  A closed cycle is only useful if it can be
*entered*, and this section answers that question: **it can, and in exactly one way — the
strengthening hole.**

Two further nodes are added, and neither is a judgement: both are *transports*.

* `VInductDecl'.SpineStrengthen` — "the spine's `HasArgs` replays from `e₂` at `e₁`", per companion
  member.  Its antecedent is free (`SpineHargsK.of_argsTypedK` on the datum at `e₂`), so it is
  equivalent to node 2.
* `VIndRestore.ValStrengthen` — "the one closed typing replays from `e₂` at `e₁`", per replaced
  constant.  Its antecedent is free too — `valAt_e₂` is `valAt_of_spineHargsK` run at `e₂` in place
  of `e₁` — so it is equivalent to node 3.

`ValStrengthen` is the smallest of the five nodes: **one `HasType` in the empty context, per
companion member, moved down one `addConstList`.**  And `valStrengthen_endpoints_clean` proves both
of its endpoints — subject *and* type — mention only constants `e₁` declares.  So the instance the
cycle needs is a **plain** instance of `VEnv.AxiomConservativityWF` (`RestrictCompanion.lean` §4):
its "the endpoints do not mention the dropped constants" side condition is discharged here, not
assumed.  And `AxiomConservativityWF` is proved equivalent to `StrengtheningTarget`, which
`Theory/Typing/UniqueTyping.lean` (the comment above `IsDefEqU.weakN_iff`) records as **exactly**
one of the thirteen open holes.

**So: a circle, whose only entry is a plain instance of the strengthening hole.**
`restrictStep_entry` is an `↔`, so every other node hands the entry point straight back; nothing on
the cycle is weaker than node 5.

**What this does NOT say, and the distinction matters.**  Node 5 is an *instance* of
`AxiomConservativityWF`, not that statement itself: its context is empty, its gap is a single
`addConstList`, and its subject is `R.tyVal D j`.  A proof of the instance family need therefore not
be a proof of the hole — and §3a exhibits an instance discharged with no hole at all, by `type_tac`
on the concrete spine at the `NTree`/`List` witness.  What is measured here is (i) that the residual
is *equivalent* to that instance, so no node of the cycle is a cheaper target, and (ii) that the
instance's own side condition — clean endpoints — is discharged, so it is a plain instance rather
than a harder one.  Whether the instance family is strictly weaker than the hole is **not** measured,
and would be the next question worth asking. -/

namespace RestrictStepCfg

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
  {occ : Nat → VNestedOcc}

/-- `e₂` is an extension of the pre-block environment too — `addIndTypes` is an `addConstList`. -/
theorem le₂ (H : RestrictStepCfg D R K env e₂ e₁ occ) : env ≤ e₂ := by
  have := H.stage₂; rw [VEnv.addIndTypes] at this; exact VEnv.addConstList_le this

/-- The staging environment where `D.WF.ctors` lives is ordered. -/
theorem ordered₂ (H : RestrictStepCfg D R K env e₂ e₁ occ) : e₂.Ordered :=
  VInductDecl'.addIndTypes_ordered H.ordered H.wf H.stage₂

/-- The parameters are types at `e₂` as well. -/
theorem params₂ (H : RestrictStepCfg D R K env e₂ e₁ occ) :
    OnCtx D.params.reverse (e₂.IsType D.uvars) :=
  OnCtx.mono (fun h => h.mono H.le₂) H.wf.params

/-- …and constant-closed there. -/
theorem ctxIn₂ (H : RestrictStepCfg D R K env e₂ e₁ occ) :
    CtxConstsIn e₂.contains D.params.reverse :=
  ctxConstsIn_of_onCtx H.ordered₂ H.params₂

/-- …and at `e₁`, in the un-reversed form `tyVal_constsIn` consumes. -/
theorem paramsIn₁ (H : RestrictStepCfg D R K env e₂ e₁ occ) :
    ∀ B ∈ D.params, B.ConstsIn e₁.contains := fun B hB =>
  ctxConstsIn_mem (ctxConstsIn_of_onCtx H.ordered₁ H.params₁) B (List.mem_reverse.2 hB)

end RestrictStepCfg

/-- **NODE 4: the spine strengthening.**  Not a judgement but a transport: whatever the datum at
`e₂` gives about the spine replays one environment down.  Compare `SpineHargsK`, which *asserts*
the `e₁` half outright. -/
def VInductDecl'.SpineStrengthen (D : VInductDecl') (K : List Name) (e₂ e₁ : VEnv)
    (occ : Nat → VNestedOcc) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    e₂.HasArgs D.uvars D.params.reverse
      (splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1 (occ j).args →
    e₁.HasArgs D.uvars D.params.reverse
      (splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1 (occ j).args

/-- **NODE 5: the value strengthening.**  The smallest node: one closed `HasType`, per replaced
constant, moved from `e₂` to `e₁`. -/
def VIndRestore.ValStrengthen (R : VIndRestore) (D : VInductDecl') (K : List Name)
    (e₂ e₁ : VEnv) : Prop :=
  ∀ {c : Name} {t : VExpr} {ci : VConstant}, R.csubstTy D K c = some t →
    e₂.constants c = some ci → e₂.HasType ci.uvars [] t ci.type →
    e₁.HasType ci.uvars [] t ci.type

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
  {occ : Nat → VNestedOcc}

/-- Node 2 ⟹ node 4: drop the antecedent.  (The `e₁` half is asserted, so the transport is free.) -/
theorem cyc_spine_to_strengthen (hS : D.SpineHargsK K e₁ occ) : D.SpineStrengthen K e₂ e₁ occ :=
  fun j T hT hK _ => hS j T hT hK

/-- Node 4 ⟹ node 2, using **only** the datum at `e₂`: the transport's antecedent is free. -/
theorem cyc_strengthen_to_spine (H₂ : D.ArgsTypedK K e₂ occ)
    (hs : D.SpineStrengthen K e₂ e₁ occ) : D.SpineHargsK K e₁ occ :=
  fun j T hT hK => hs j T hT hK (VInductDecl'.SpineHargsK.of_argsTypedK H₂ j T hT hK)

/-- **THE `val` CLAUSE AT `e₂` IS FREE.**  `valAt_of_spineHargsK` with `e := e₂`: at the larger
environment the residual costs nothing but the datum `D.WF.ctors` already supplies there.  This is
`RestrictCompanion.lean` §11a's `valAt_of_argsTypedK`, restated at the configuration and through
the weaker `SpineHargsK` input (so the *guarded* level condition suffices). -/
theorem valAt_e₂ (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ) :
    R.ValAt D K e₂ e₂ :=
  valAt_of_spineHargsK C.built (VInductDecl'.SpineHargsK.of_argsTypedK H₂) C.le₂ C.params₂
    C.stage₂ C.lvls

/-- Node 3 ⟹ node 5: drop the antecedent. -/
theorem cyc_val_to_strengthen (hv : R.ValAt D K e₂ e₁) : R.ValStrengthen D K e₂ e₁ :=
  fun hd hc _ => hv hd hc

/-- Node 5 ⟹ node 3, using only the datum at `e₂` (via `valAt_e₂`). -/
theorem cyc_strengthen_to_val (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (H₂ : D.ArgsTypedK K e₂ occ) (hs : R.ValStrengthen D K e₂ e₁) : R.ValAt D K e₂ e₁ :=
  fun hd hc => hs hd hc (valAt_e₂ C H₂ hd hc)

/-- **THE FIVE-NODE CYCLE.**  Given the datum at `e₂`, the datum at `e₁`, the spine typing at `e₁`,
the `val` clause at `e₁`, and the two *transports* from `e₂` to `e₁` are all the same statement. -/
theorem restrictStep_cycle₅ (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (H₂ : D.ArgsTypedK K e₂ occ) :
    (D.ArgsTypedK K e₁ occ ↔ D.SpineHargsK K e₁ occ) ∧
    (D.SpineHargsK K e₁ occ ↔ D.SpineStrengthen K e₂ e₁ occ) ∧
    (D.SpineStrengthen K e₂ e₁ occ ↔ R.ValAt D K e₂ e₁) ∧
    (R.ValAt D K e₂ e₁ ↔ R.ValStrengthen D K e₂ e₁) ∧
    (R.ValStrengthen D K e₂ e₁ ↔ D.ArgsTypedK K e₁ occ) :=
  ⟨(restrictStep_cycle C H₂).1,
   ⟨cyc_spine_to_strengthen, cyc_strengthen_to_spine H₂⟩,
   ⟨fun hs => cyc_spine_to_val C (cyc_strengthen_to_spine H₂ hs),
    fun hv => cyc_spine_to_strengthen (spineHargsK_of_valAt C H₂ hv)⟩,
   ⟨cyc_val_to_strengthen, cyc_strengthen_to_val C H₂⟩,
   ⟨fun hs => cyc_val_to_datum C H₂ (cyc_strengthen_to_val C H₂ hs),
    fun hA => cyc_val_to_strengthen (cyc_spine_to_val C (cyc_datum_to_spine hA))⟩⟩

/-- **THE ENTRY POINT, ISOLATED.**  The whole residual of the nested restriction step *is* one
constant-strengthening step per companion member: a single closed `HasType` that holds at `e₂` and
is wanted at `e₁`.  Read right-to-left it is a route; read left-to-right it says no cheaper door
exists on the cycle. -/
theorem restrictStep_entry (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (H₂ : D.ArgsTypedK K e₂ occ) :
    D.ArgsTypedK K e₁ occ ↔ R.ValStrengthen D K e₂ e₁ :=
  ((restrictStep_cycle₅ C H₂).2.2.2.2).symm

/-- **…AND IT IS A *PLAIN* INSTANCE OF AXIOM CONSERVATIVITY.**  Both endpoints of the judgement
node 5 has to move are already `e₁`-clean: the subject by `ValAtPrice.lean` §5's `tyVal_constsIn`,
the type because `D.WF` types every member type at the pre-block environment.  So node 5 asks for
no more than `VEnv.AxiomConservativityWF` gives — the side condition that makes that statement
non-trivial is discharged, not assumed. -/
theorem valStrengthen_endpoints_clean (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (H₂ : D.ArgsTypedK K e₂ occ) {c : Name} {t : VExpr} {ci : VConstant}
    (hd : R.csubstTy D K c = some t) (hc : e₂.constants c = some ci) :
    t.ConstsIn e₁.contains ∧ ci.type.ConstsIn e₁.contains := by
  obtain ⟨j, T, hT, rfl, hK, rfl⟩ := VIndRestore.csubstTy_dom hd
  have hmem : (T.name, (⟨D.uvars, T.type⟩ : VConstant)) ∈ D.typeConsts :=
    List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩
  have h₂ := C.stage₂
  rw [VEnv.addIndTypes] at h₂
  rw [VEnv.addConstList_constants h₂ _ hmem] at hc
  cases hc
  refine ⟨tyVal_constsIn C.built C.ordered₂ C.ctxIn₂ C.stage₂ C.stage₁ H₂ C.paramsIn₁ hT hK,
    ?_⟩
  exact (C.wf.types_constsIn C.ordered T (List.mem_of_getElem? hT)).mono
    fun _ h => C.le₁.contains h

end VIndRestore

/-! ## §3 The nine side conditions, jointly inhabited at a real block

Working rule: **a reduction is not a discharge, and hole-freeness is not inhabitation.**  §1 and §2
are implications; this section exhibits a single block at which every one of the nine fields holds
*at the same time*, together with the datum at `e₂` that the cycle takes as its extra input.

The block is `ntreeAux` — `NTree α` with a `List (NTree α)` field, `np = 1`, `uvars = 1`, the block
Lean's own kernel runs the nested elimination on.  This is deliberately **not** `nfnAux`:
`docs/handoff-valat.md` §4 reports `nfnAux` as degenerate (`uvars = 0`, `params = []`, so the
parameter-context conditions are `trivial` there) and records that the parameterised witness was
*not* instantiated.  It is now.

Nothing is hypothesised: `ntreeAux_restrictStepCfg_exists` closes the staging existentially. -/

namespace InductiveDeclExamples

/-- **THE CONFIG AT THE PARAMETERISED NESTED BLOCK.**  Every field from an existing lemma; the two
that used to be fields come from `ntreeAux_built`. -/
theorem ntreeAux_restrictStepCfg {env₁ env₂ env₃ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (h₂ : env₁.addIndTypes ntreeAux = some env₂)
    (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃) :
    RestrictStepCfg ntreeAux ntreeRestore ntreeK env₁ env₂ env₃ (fun _ => listOcc) where
  ordered := listEnv_ordered h
  ordered₁ := VEnv.addConstList_ordered (listEnv_ordered h)
    (VEnv.addInductR_typeConstsC_wf ntreeAux_WF') h₃
  wf := ntreeAux_WF'
  built := ntreeAux_built h
  fresh := by rw [ntree_csubstTy]; exact ntreeSubst_fresh h
  closed := ntree_csubstTy_closed
  stage₂ := h₂
  stage₁ := h₃
  lvls := fun j _ _ _ => by
    rw [show ntreeRestore.tyLvls j = [VLevel.param 0] from rfl]; decide

/-- **JOINTLY INHABITED, NOTHING HYPOTHESISED.**  The nine side conditions and the datum at `e₂`,
at one block, one restoration, one occurrence family and one staging.  The datum at `e₂` is not an
extra assumption at this witness either: `ntreeAux_argsTypedK_of_wf` derives it from `D.WF` and the
staging alone (§4). -/
theorem ntreeAux_restrictStepCfg_exists :
    ∃ env₁ env₂ env₃ : VEnv,
      RestrictStepCfg ntreeAux ntreeRestore ntreeK env₁ env₂ env₃ (fun _ => listOcc) ∧
      ntreeAux.ArgsTypedK ntreeK env₂ (fun _ => listOcc) := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  exact ⟨env₁, env₂, env₃, ntreeAux_restrictStepCfg h h₂ h₃, ntreeAux_argsTypedK_of_wf h₂⟩

/-- **AND THE CYCLE IS ENTERED THERE — so node 5 is not vacuous either.**  All five nodes hold at
this witness; the one exhibited is `ValStrengthen`, the strengthening instance §2 isolates.  Read
this together with §2's caveat: the entry is a plain *instance* of the hole, and here is one such
instance discharged with **no** hole, by `ntreeSubst_WF`'s `val` clause — `type_tac` on the concrete
spine `List.{u} (NTree.{u} #0)`.  So the instance family is certainly not *equivalent* to the hole
pointwise; **two witnesses with a hand discharge are still two witnesses**, and what §2 measures is
that no node of the cycle is a weaker target than this instance. -/
theorem ntreeAux_valStrengthen :
    ∃ env₁ env₂ env₃ : VEnv,
      RestrictStepCfg ntreeAux ntreeRestore ntreeK env₁ env₂ env₃ (fun _ => listOcc) ∧
      ntreeAux.ArgsTypedK ntreeK env₂ (fun _ => listOcc) ∧
      ntreeRestore.ValStrengthen ntreeAux ntreeK env₂ env₃ ∧
      ntreeAux.SpineStrengthen ntreeK env₂ env₃ (fun _ => listOcc) := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  have C := ntreeAux_restrictStepCfg h h₂ h₃
  have H₂ := ntreeAux_argsTypedK_of_wf (env₁ := env₁) h₂
  have H₁ : ntreeAux.ArgsTypedK ntreeK env₃ (fun _ => listOcc) :=
    ntreeAux_argsTypedK_restrict h h₂ h₃
  exact ⟨env₁, env₂, env₃, C, H₂, (VIndRestore.restrictStep_entry C H₂).1 H₁,
    VIndRestore.cyc_spine_to_strengthen (VIndRestore.cyc_datum_to_spine H₁)⟩

end InductiveDeclExamples

/-! ### §3a Node 5 is not vacuous at the witness

`ValStrengthen` is a `∀` over `csubstTy`'s domain; if that domain missed `e₂`'s constants the
statement would hold for nothing.  It does not: the companion name `_nested.List_1` is in the
domain, `e₂` declares it, and the judgement being moved is the concrete typing
`ntreeVal : Type u → Type u`.  So §3's `ntreeAux_valStrengthen` moves a real judgement. -/

namespace InductiveDeclExamples

/-- **THE JUDGEMENT NODE 5 MOVES, AT THE WITNESS, AT BOTH ENDS.** -/
theorem ntreeAux_valStrengthen_nonvacuous :
    ∃ env₂ env₃ : VEnv,
      ntreeRestore.csubstTy ntreeAux ntreeK `_nested.List_1 = some ntreeVal ∧
      env₂.constants `_nested.List_1
        = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ ∧
      env₂.HasType 1 [] ntreeVal
        (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) ∧
      env₃.HasType 1 [] ntreeVal
        (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  have C := ntreeAux_restrictStepCfg h h₂ h₃
  have H₂ := ntreeAux_argsTypedK_of_wf (env₁ := env₁) h₂
  have hd := ntree_csubst_ty_val
  have hc := nlist_const_staged h₂
  exact ⟨env₂, env₃, hd, hc, VIndRestore.valAt_e₂ C H₂ hd hc,
    VIndRestore.cyc_spine_to_val C
      (VIndRestore.cyc_datum_to_spine (ntreeAux_argsTypedK_restrict h h₂ h₃)) hd hc⟩

end InductiveDeclExamples

/-! ## §4 The audit: are the side conditions "about the staging and the block, not the residual"?

Three parts, and the third is a correction to §0 as it was first written.

**(a) Two of the eleven were not side conditions at all.**  `occurs` is `Built.occurs` with
`OccursN`'s extra clauses forgotten, and `argsNoK` is `Built.kfresh.argsNoK` — except that `Built`'s
form is *guarded* by `T.name ∈ K` and the field was not.  The unguarded quantifier was an artefact
of `VInductDecl'.ArgsTypedK.restrict_of_val`'s signature, whose `hargs` is unguarded although its
body only ever applies it at a guarded `j`; `cyc_val_to_datum` now inlines
`VNestedOcc.ArgsTypedH.restrictC'` with the guarded form and the two fields are gone.  **Nine
fields, and this is machine-checked**: the whole of §1 and §2 elaborates over the nine-field
structure.  *A note for whoever owns `RestrictCompanion.lean`*: `restrict_of_val` can take the
guarded `hargs` with its body unchanged, and would then be applicable from `Built` alone.

**(b) None of the nine is a typing at `e₁`.**  Field by field: `ordered`, `ordered₁` are `VEnv`
well-formedness; `stage₂`, `stage₁` are the two `addConstList` equations; `fresh`, `closed` are
syntactic facts about `csubstTy`; `lvls` is a level-well-formedness condition on `R.tyLvls`; `built`
is `VInductDecl'.Built`, all ten of whose clauses are equations between names/members, an `OccursN`,
an `OwnId`, a `Nodup` and a `KFresh` — no judgement anywhere; `wf` is `D.WF env`.  So no field is
`ValAt`, `SpineHargsK` or `SpineStrengthen` in disguise.

**(c) But `wf` is NOT residual-blind, and §0's first wording over-claimed.**  `D.WF`'s `ctors`
clause is staged at `e₂`, and `VInductDecl'.WF.recField_canonResult` turns it into the spine typing
*there*.  At the parameterised witness this is not hypothetical:
`InductiveDeclExamples.ntreeAux_argsTypedK_of_wf` takes **only** the staging equation and produces
the datum at `e₂` out of `ntreeAux_WF'`.  So `wf` + `stage₂` already contains the residual's `e₂`
shadow, and `H₂` is barely an extra hypothesis at all — which is precisely why the remaining gap is
a *strengthening* step and nothing else: the configuration hands you the residual **one environment
too high**, and §2 measures the price of the last step down.

**What is NOT shown here, and is not claimed.**  That the nine conditions plus `H₂` do *not* imply
the residual.  A proof of that would be a separating witness — a configuration where every field
holds and node 1 fails — and none is exhibited; `ValAtPrice.lean` §5 is evidence that none exists
(the constant-level obstruction to node 3 is provably absent at `e₁`), which is why the standing
reading is that the residual is **true with only its proof missing**.  "None of them is about the
residual" is therefore a statement about the *shape* of the nine conditions, verified as (b), not a
non-implication. -/

end Lean4Lean

/-! ## §5 Grading: hole-freeness, per declaration -/

#print axioms Lean4Lean.ctxConstsIn_of_onCtx
#print axioms Lean4Lean.RestrictStepCfg.le₁
#print axioms Lean4Lean.RestrictStepCfg.paramsIn
#print axioms Lean4Lean.RestrictStepCfg.params₁
#print axioms Lean4Lean.RestrictStepCfg.occurs
#print axioms Lean4Lean.RestrictStepCfg.argsFree
#print axioms Lean4Lean.VIndRestore.cyc_datum_to_spine
#print axioms Lean4Lean.VIndRestore.cyc_spine_to_val
#print axioms Lean4Lean.VIndRestore.cyc_val_to_datum
#print axioms Lean4Lean.VIndRestore.restrictStep_cycle
#print axioms Lean4Lean.VIndRestore.spineHargsK_of_valAt
#print axioms Lean4Lean.RestrictStepCfg.le₂
#print axioms Lean4Lean.RestrictStepCfg.ordered₂
#print axioms Lean4Lean.RestrictStepCfg.params₂
#print axioms Lean4Lean.RestrictStepCfg.ctxIn₂
#print axioms Lean4Lean.RestrictStepCfg.paramsIn₁
#print axioms Lean4Lean.VIndRestore.cyc_spine_to_strengthen
#print axioms Lean4Lean.VIndRestore.cyc_strengthen_to_spine
#print axioms Lean4Lean.VIndRestore.valAt_e₂
#print axioms Lean4Lean.VIndRestore.cyc_val_to_strengthen
#print axioms Lean4Lean.VIndRestore.cyc_strengthen_to_val
#print axioms Lean4Lean.VIndRestore.restrictStep_cycle₅
#print axioms Lean4Lean.VIndRestore.restrictStep_entry
#print axioms Lean4Lean.VIndRestore.valStrengthen_endpoints_clean
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_restrictStepCfg
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_restrictStepCfg_exists
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_valStrengthen
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_valStrengthen_nonvacuous
