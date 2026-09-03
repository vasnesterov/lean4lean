import Lean4Lean.Verify.Inductive.RestrictCompanion
import Lean4Lean.Verify.Inductive.ProjNoNested
import Lean4Lean.Theory.Inductive.CompanionResolve

/-!
# `VIndRestore.ValAt`: what it costs, what it does not need, and which routes are closed

`Verify/Inductive/RestrictCompanion.lean` §11 reduced the whole nested `AddInduct` transport to

> `VIndRestore.ValAt D K e₂ e₁` — for each companion member `j`, **one closed typing**
> `e₁.HasType D.uvars [] (R.tyVal D j) T.type`, where `e₁ = env.addIndTypesC D K`,

and `docs/handoff-restrict.md` §5 named two ways at it, recommending: *"Look for it in
`Built.member`, which pins the spine syntactically against the companion member."*

This file measures that recommendation.  Four results, in descending order of value:

1. **§3 The residual's only known general producer needs less than the datum.**
   `RestrictCompanion.lean` §11a reaches `ValAt` from the whole datum `D.ArgsTypedK K e₁ occ`
   (three things per companion member).  `valAt_of_spineHargsK` reaches it from the **`ty` half
   alone** — one `HasArgs` per companion member, `ArgsTypedH`'s `ctor` family and `lvls` condition
   never mentioned.  **Read this correctly**: `SpineHargsK` is *not* weaker than `ValAt` (the
   converse direction is `of_mkApp`, which this corner refuses), so the residual `ValAt` has not
   shrunk.  What shrinks is what a **checker-side clause** must carry in order to discharge it:
   one spine typing at `addIndTypesC`-env, not a datum family.
2. **§4 `Built.member` cannot produce it, and here is the precise reason.**  `D.WF env`'s only
   clause that can type the spine at all is `ctors`, staged at `env.addIndTypes D = e₂` — one
   environment too high (that is `VInductDecl'.WF.recField_canonResult`,
   `Verify/Inductive/ArgsTypedSupply.lean` §5.1, the general lemma behind both witnesses).  The
   clauses staged at `env` are **provably spine-blind**: `builtMember_codomain_constsIn` shows
   `D.WF env` forces the built companion member's stored type — and hence whatever of the spine
   occurs in it — to mention only constants `env` already declares, while a nesting spine mentions
   the block's *own* members, which `env` does not declare.  So the `env`-staged half of `D.WF`
   cannot see the spine, and the `e₂`-staged half sees it one environment too high.
3. **§5 …but the constant-level obstruction to `ValAt` at `e₁` is provably ABSENT**, and this is
   the finding I did not expect.  `VNestedOcc.not_argsTypedH_of_not_constsIn`
   (`ArgsTypedSupply.lean` §6) refutes the spine typing at every environment that does not declare
   what the spine mentions — that is how `pfnOcc_not_argsTypedH_pre` kills the pre-block
   environment.  At `e₁` that obstruction **cannot fire**: `args_constsIn_of_argsTypedK` proves
   that the datum at `e₂` plus `KFresh.argsNoK` puts every spine argument's constants in `e₁`,
   because `e₂ \ e₁` is exactly `K` and `argsNoK` says the spine avoids `K`.  Hence
   `tyVal_constsIn_e₁`: `ValAt`'s cheap necessary condition **holds**.  `e₁` is therefore the
   *exact* boundary at which the pre-block refutation stops working, and any refutation of the
   residual would have to be proof-theoretic — i.e. it would have to go through the same
   strengthening hole §4 of `RestrictCompanion.lean` prices.  **This is evidence the residual is
   true and only its proof is missing**, not evidence it is false.
4. **§6 The `WFC` route is closed, in general.**  `docs/handoff-restrict.md` §6a flagged, as read
   off a note and *not checked*, that `VInductDecl'.WFC` (`Theory/Inductive/CompanionResolve.lean`
   — `WF` with `ctors` re-staged onto exactly `addIndTypesC`-env, i.e. onto `e₁`) is unavailable on
   the nested path, and added: *"if it is wrong then `WFC` is a third route and a much shorter
   one"*.  It is right, and generally so: `WFC.companion_ctors_nil` proves that `D.WFC env K`
   forces **every companion member to have an empty constructor list**, because a constructor's
   `result` clause types the member-headed application, and a companion's head is by construction
   not declared at `e₁`.  A companion's constructor list is the foreign block's, so the route is
   available only at blocks that nest through a constructor-free inductive.  That closes the
   flagged unknown: there is no third route.

**Nothing here makes the flip**, and `ValAt` is **not** constructed in general: §3 shrinks the
residual, §4 measures why the brief's lead does not close it, §5 shows the cheap refutation is
unavailable, §6 closes the one remaining short route.  `tryEtaStructCore.WF` /
`isDefEqUnitLike.WF` (`docs/vacuity-ledger.md` row 197) are untouched, and no `HasArgs.of_mkApp`
appears in any proof below.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkLams mkApp mkPi splitPis instTele bvars)

/-! ## §1 Two library gaps

`Verify/Inductive/ProjNoNested.lean` §1.1 has the inverse `ConstsIn` lemmas for `mkPi` and
`mkApp` but not for `mkLams`, which is the shape `R.tyVal` is in; and nothing yet intersects a
`ConstsIn` with a `NoConsts`, which is what §5 needs to cross from `e₂` down to `e₁`. -/

namespace VExpr

variable {P : Name → Prop} {K : List Name}

/-- `mkLams`, backwards — the twin of `constsIn_mkPi_binders` for the body. -/
theorem constsIn_mkLams_body : ∀ {as : List VExpr} {b : VExpr}, (mkLams as b).ConstsIn P →
    b.ConstsIn P
  | [], _, h => h
  | _ :: as, b, h => constsIn_mkLams_body (as := as) (b := b) h.2

/-- `mkPi`, backwards, at the body. -/
theorem constsIn_mkPi_body : ∀ {as : List VExpr} {b : VExpr}, (mkPi as b).ConstsIn P →
    b.ConstsIn P
  | [], _, h => h
  | _ :: as, b, h => constsIn_mkPi_body (as := as) (b := b) h.2

/-- **Refining a `ConstsIn` by a `NoConsts`.**  The two freshness vocabularies intersect: a term
whose constants satisfy `P` and which mentions nothing in `K` has its constants in `P ∧ ∉ K`. -/
theorem ConstsIn.and_noConsts : ∀ {e : VExpr}, e.ConstsIn P → e.NoConsts K →
    e.ConstsIn (fun n => P n ∧ n ∉ K)
  | .bvar _, _, _ | .sort _, _, _ => trivial
  | .const .., h1, h2 => ⟨h1, h2⟩
  | .app .., h1, h2 | .lam .., h1, h2 | .forallE .., h1, h2 =>
    ⟨h1.1.and_noConsts h2.1, h1.2.and_noConsts h2.2⟩

end VExpr

/-- Every type in a constant-closed context is constant-closed.  (`CtxConstsIn` is an `OnCtx`
whose predicate ignores the prefix, so this is an induction and nothing more.) -/
theorem ctxConstsIn_mem {P : Name → Prop} : ∀ {Γ : List VExpr}, CtxConstsIn P Γ →
    ∀ A ∈ Γ, A.ConstsIn P
  | [], _, _, hA => nomatch hA
  | _ :: Γ, h, A, hA => by
    rcases List.mem_cons.1 hA with rfl | hA
    · exact h.2
    · exact ctxConstsIn_mem (Γ := Γ) h.1 A hA

/-! ## §2 The two stagings, at the level of names

§2 of `RestrictCompanion.lean` proved `e₁ ≤ e₂`.  What §5 needs is the *converse* at the level of
names: a name `e₂` declares and `K` does not name is declared by `e₁` as well.  That is exact —
`e₂ \ e₁` is `K` — and it is what makes the constant-level obstruction vanish at `e₁`. -/

/-- Every entry of the companion-aware type-constant list is named outside `K`. -/
theorem VInductDecl'.not_mem_K_of_mem_typeConstsC {D : VInductDecl'} {K : List Name}
    {c : Name × VConstant} (h : c ∈ D.typeConstsC K) : c.1 ∉ K := by
  rw [VInductDecl'.typeConstsC, List.mem_filterMap] at h
  obtain ⟨a, -, he⟩ := h
  split at he
  · exact absurd he nofun
  · cases he; assumption

/-- **A companion name is absent from `e₁`.**  `KFresh.notContains` says it is absent from `env`,
and `addIndTypesC` declares only the members *not* named in `K`. -/
theorem VEnv.not_contains_addIndTypesC {env e₁ : VEnv} {D : VInductDecl'} {K : List Name}
    (h₁ : env.addIndTypesC D K = some e₁) (hfresh : ∀ n ∈ K, ¬ env.contains n)
    {n : Name} (hn : n ∈ K) : ¬ e₁.contains n := by
  rw [VEnv.addIndTypesC] at h₁
  have hm : n ∉ (D.typeConstsC K).map (·.1) := by
    intro h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact VInductDecl'.not_mem_K_of_mem_typeConstsC hp hn
  rintro ⟨ci, hc⟩
  rw [VEnv.addConstList_constants_of_not_mem h₁ hm] at hc
  exact hfresh n hn ⟨ci, hc⟩

/-- **The name-level inclusion in the direction §5 needs.**  `e₂` declares `env`'s constants and
all of `D`'s members; `e₁` declares `env`'s constants and the members not named in `K`.  So off
`K` the two agree on what they declare. -/
theorem VEnv.contains_addIndTypesC_of_addIndTypes {env e₂ e₁ : VEnv} {D : VInductDecl'}
    {K : List Name} (h₂ : env.addIndTypes D = some e₂) (h₁ : env.addIndTypesC D K = some e₁)
    {n : Name} (hn : e₂.contains n) (hK : n ∉ K) : e₁.contains n := by
  rw [VEnv.addIndTypes] at h₂; rw [VEnv.addIndTypesC] at h₁
  by_cases hm : n ∈ (D.typeConsts.map (·.1))
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 (by simpa [VInductDecl'.typeConsts] using hp)
    have hmem : (T.name, (⟨D.uvars, T.type⟩ : VConstant)) ∈ D.typeConstsC K := by
      rw [VInductDecl'.typeConstsC, List.mem_filterMap]
      exact ⟨(T.name, ⟨D.uvars, T.type⟩), List.mem_map.2 ⟨T, hT, rfl⟩, by simp [hK]⟩
    exact ⟨_, VEnv.addConstList_constants h₁ _ hmem⟩
  · obtain ⟨ci, hc⟩ := hn
    rw [VEnv.addConstList_constants_of_not_mem h₂ hm] at hc
    have hm' : n ∉ ((D.typeConstsC K).map (·.1)) := fun h => hm (by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact List.mem_map.2 ⟨p, VInductDecl'.mem_typeConsts_of_mem_typeConstsC hp, rfl⟩)
    exact ⟨_, by rw [VEnv.addConstList_constants_of_not_mem h₁ hm']; exact hc⟩

/-! ## §3 The `ty` half of the datum, at `e₁`, is enough for `ValAt`

`RestrictCompanion.lean` §11a's `valAt_of_argsTypedK` produces `ValAt` from the **whole** datum
`D.ArgsTypedK K e occ`, which is three things per companion member: a level condition, a `HasArgs`
against the foreign member's parameter telescope (`ty`), and a `HasArgs` against **each foreign
constructor's** parameter telescope (`ctor`).  Only the middle one is used.

`SpineHargsK` below is that middle one alone.  `valAt_of_spineHargsK` is `ValAt` from it, and
`SpineHargsK.of_argsTypedK` is the projection showing it is weaker **than the datum**.  It is *not*
weaker than `ValAt`: `tyVal_hasType_of_spineTyped`'s route back from an applied typing to a
`HasArgs` is `VEnv.HasArgs.of_mkApp` (`HargsShared.lean` §6), which is `sorryAx`-tainted and which
this corner refuses, so no comparison in that direction is claimed here.

The consequence is for the **discharge site**, not for the residual: a clause on the checker side
(`docs/handoff-restrict.md` §5's `TrIndDeclN` option) has to carry only one `HasArgs` per companion
member at `addIndTypesC`-env — neither the constructor family nor the level condition has to be
re-established there, since those are consumed only at `e₂`, where the datum is available. -/

/-- **THE RESIDUAL, in its smallest known form**: for each companion member, the presented spine
instantiates the foreign member's parameter telescope.  This is `VNestedOcc.ArgsTypedH.ty` alone,
quantified over the companion members. -/
def VInductDecl'.SpineHargsK (D : VInductDecl') (K : List Name) (e : VEnv)
    (occ : Nat → VNestedOcc) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    e.HasArgs D.uvars D.params.reverse
      (splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1 (occ j).args

/-- The datum's `ty` half, projected: `SpineHargsK` is weaker than `ArgsTypedK`. -/
theorem VInductDecl'.SpineHargsK.of_argsTypedK {D : VInductDecl'} {K : List Name} {e : VEnv}
    {occ : Nat → VNestedOcc} (hS : D.ArgsTypedK K e occ) : D.SpineHargsK K e occ :=
  fun j T hT hK => (hS j T hT hK).ty

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e : VEnv}
  {occ : Nat → VNestedOcc} {j : Nat} {T : VIndType}

/-- `hargs` in the shape `tyVal_hasType_of_hargs` consumes it, from `SpineHargsK` rather than from
the whole datum.  `hargs_of_argsTypedK`'s proof (`ArgsTypedSupply.lean` §2.1) with `(hS …).ty`
replaced by the hypothesis. -/
theorem hargs_of_spineHargsK (hB : D.Built R K env occ) (hS : D.SpineHargsK K e occ)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
      e.HasArgs D.uvars D.params.reverse
        (R.declTele ci ((occ j).decl.np) j) (R.tyArgs j) := by
  intro ci hci
  have ho := (hB.occurs j T hT hK).toOccurs
  rw [hB.tyName j T hT hK] at hci
  cases Option.some.inj (ho.ty_const.symm.trans hci)
  show e.HasArgs D.uvars D.params.reverse
    (splitPis ((occ j).decl.np) ((occ j).src.type.instL (R.tyLvls j))).1 (R.tyArgs j)
  rw [hB.tyLvls j T hT hK, hB.tyArgs j T hT hK]
  exact hS j T hT hK

/-- **THE RESIDUAL SUFFICES.**  `RestrictCompanion.lean` §11's `ValAt` — hence, with
`csubstTy_WF_of_val`, the whole nested transport — from one `HasArgs` per companion member at the
target environment.  No `of_mkApp`; the telescope is carried. -/
theorem valAt_of_spineHargsK (hB : D.Built R K env occ) (hS : D.SpineHargsK K e occ)
    (hle : env ≤ e) (hparams : OnCtx D.params.reverse (e.IsType D.uvars))
    (h₂ : env.addIndTypes D = some e₂)
    (hlvl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ l ∈ R.tyLvls j, l.WF D.uvars) : R.ValAt D K e₂ e := by
  intro c t ci hd hc
  obtain ⟨j, T, hT, rfl, hK, rfl⟩ := VIndRestore.csubstTy_dom hd
  have hmem : (T.name, (⟨D.uvars, T.type⟩ : VConstant)) ∈ D.typeConsts :=
    List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩
  rw [VEnv.addIndTypes] at h₂
  rw [VEnv.addConstList_constants h₂ _ hmem] at hc
  cases hc
  exact tyVal_hasType_of_hargs hB.toFaithful hle hparams hT hK (hlvl j T hT hK)
    (hargs_of_spineHargsK hB hS hT hK)

end VIndRestore

/-! ### §3a Collapse test

At `K = []` both `SpineHargsK` and `ValAt` are vacuous (`RestrictCompanion.lean` §11b makes the
same point about the datum), so §3's content lives entirely at `K ≠ []`; reported because a
reduction that also holds at `K = []` for the trivial reason grades itself against a criterion
that cannot fail. -/

theorem VInductDecl'.spineHargsK_nil {D : VInductDecl'} {e : VEnv} {occ : Nat → VNestedOcc} :
    D.SpineHargsK [] e occ := fun _ _ _ hK => nomatch hK

/-! ## §4 Why `Built.member` cannot produce it

`docs/handoff-restrict.md` §5 recommended looking in `Built.member`, "which pins the spine
syntactically against the companion member".  It does pin it — and that is exactly the problem.

`Built.member` says `T = (occ j).member D.header R`, whose stored type is
`(occ j).instAt D.header (occ j).src.type = mkPi D.params (instAll (splitPis np …).2 (occ j).args)`.
So the spine enters the built member's **stored type** only through the substituted codomain.  And
`D.WF env`'s clause about that type — `VIndType.WF.isType` — is staged at `env`, which by
`VEnv.Ordered.constsIn` forces it to mention only constants `env` declares
(`VInductDecl'.WF.types_constsIn`, `RestrictCompanion.lean` §11).  A **nesting** spine mentions the
block's *own* members, which `env` does not declare (that is exactly
`NestedWit.pfnOcc_not_argsTypedH_pre`'s content).  So either the spine does not occur in the
codomain at all — in which case `D.WF env`'s `env`-staged clauses say nothing about it — or
`D.WF env` is false.  Either way the `env`-staged half of `D.WF` cannot supply the spine typing.

The same argument applies to the built member's **index telescope**
(`VIndType.WF.indices`, also staged at `env`): `indices_constsIn` below.

What is left is `VInductDecl'.WF.ctors`, staged at `env.addIndTypes D = e₂` — and that *does*
supply the spine typing, in general, through `VInductDecl'.WF.recField_canonResult`
(`ArgsTypedSupply.lean` §5.1).  One environment too high, which is the whole residual. -/

namespace VInductDecl'

variable {D : VInductDecl'} {env : VEnv}

/-- **The built member's stored type is `env`-clean**, hence so is whatever of the spine occurs in
its codomain.  `WF.types_constsIn` (`RestrictCompanion.lean` §11) plus `Built.member`. -/
theorem builtMember_codomain_constsIn {R : VIndRestore} {K : List Name} {occ : Nat → VNestedOcc}
    {j : Nat} {T : VIndType} (henv : env.Ordered) (hD : D.WF env) (hB : D.Built R K env occ)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    (VExpr.instAll (splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).2
      (occ j).args).ConstsIn env.contains := by
  have h := hD.types_constsIn henv T (List.mem_of_getElem? hT)
  rw [hB.member j T hT hK] at h
  exact VExpr.constsIn_mkPi_body h

/-- **…and so is its index telescope.**  The `indices` twin of `WF.types_constsIn`: every entry of
every member's index telescope mentions only constants the *pre-block* environment declares. -/
theorem WF.indices_constsIn (henv : env.Ordered) (hD : D.WF env) :
    ∀ T ∈ D.types, ∀ A ∈ T.indices, A.ConstsIn env.contains := by
  intro T hT
  have h := (hD.types T hT).indices
  intro A hA
  exact ctxConstsIn_mem (VEnv.ctxConstsIn_of_onCtx henv h) A
    (List.mem_append_left _ (List.mem_reverse.2 hA))

end VInductDecl'

/-! ## §5 The constant-level obstruction is ABSENT at `e₁` — so no cheap refutation exists

`VNestedOcc.not_argsTypedH_of_not_constsIn` (`ArgsTypedSupply.lean` §6) is the tree's cheap
refutation of a spine typing: it fires at **any** environment that fails to declare what the spine
mentions, and `NestedWit.pfnOcc_not_argsTypedH_pre` uses it to kill the pre-block environment
outright.  The natural attempt at outcome 3 is to run it at `e₁`.

**It provably cannot fire there**, and that is this section.  `not_valAt_of_not_constsIn` is the
obstruction in `ValAt`'s own vocabulary; `args_constsIn_of_argsTypedK` and `tyVal_constsIn` prove
its premise **false** whenever the datum holds at `e₂` and the spine avoids `K` — which is
`VInductDecl'.KFresh.argsNoK`, a field of `Built`.  The reason is exact: `e₂ \ e₁` is precisely
`K` (§2), and `argsNoK` says the spine mentions no name in `K`.

Two consequences.  (i) `e₁` is the *first* environment at which the pre-block refutation stops
working, so `addIndTypesC`-env is not merely convenient but the exact boundary.  (ii) Any
refutation of the residual must be **proof-theoretic** rather than constant-level — it would have
to exhibit a companion-free judgement derivable at `e₂` and not at `e₁`, which is
`VEnv.AxiomConservativityWF`'s failure, i.e. the strengthening hole
(`RestrictCompanion.lean` §4).  So the residual is *not* refutable by the means available in this
corner, and the evidence points to its being true with only its proof missing. -/

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
  {occ : Nat → VNestedOcc} {j : Nat} {T : VIndType}

/-- **THE OBSTRUCTION, in `ValAt`'s vocabulary.**  General: no block, no `Built`, no restoration.
The context is empty, so `IsDefEq.constsIn`'s context side condition is `trivial`. -/
theorem not_valAt_of_not_constsIn {c : Name} {t : VExpr} {ci : VConstant} (he : e₁.Ordered)
    (hd : R.csubstTy D K c = some t) (hc : e₂.constants c = some ci)
    (hbad : ¬ t.ConstsIn e₁.contains) : ¬ R.ValAt D K e₂ e₁ :=
  fun h => hbad ((h hd hc).constsIn he.constsIn trivial).1

end VIndRestore

/-- **THE SPINE'S CONSTANTS ARE DECLARED AT `e₁`.**  From the datum at `e₂` — where it is
available (`ArgsTypedSupply.lean` §5.2, §10) — plus `KFresh.argsNoK`.  `HasArgs.mem_wf` forgets
the telescope, `IsDefEq.constsIn` reads the constants off, and §2 crosses from `e₂` to `e₁`. -/
theorem VInductDecl'.ArgsTypedK.args_constsIn {D : VInductDecl'} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {j : Nat} {T : VIndType}
    (henv₂ : e₂.Ordered) (hΓ : CtxConstsIn e₂.contains D.params.reverse)
    (h₂ : env.addIndTypes D = some e₂) (h₁ : env.addIndTypesC D K = some e₁)
    (hS : D.ArgsTypedK K e₂ occ)
    (hnoK : ∀ a ∈ (occ j).args, VExpr.NoConsts K a)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    ∀ a ∈ (occ j).args, a.ConstsIn e₁.contains := by
  intro a ha
  obtain ⟨A, hA⟩ := (hS j T hT hK).ty.mem_wf a ha
  have h2 : a.ConstsIn e₂.contains := (hA.constsIn henv₂.constsIn hΓ).1
  refine (h2.and_noConsts (hnoK a ha)).mono fun n hn => ?_
  exact VEnv.contains_addIndTypesC_of_addIndTypes h₂ h₁ hn.1 hn.2

/-- **…HENCE THE OBSTRUCTION'S PREMISE IS FALSE.**  `ValAt`'s cheap necessary condition — that the
substituted value mentions only constants `e₁` declares — **holds**, at every companion member, in
general.  So `not_valAt_of_not_constsIn` cannot be used to refute the residual. -/
theorem VIndRestore.tyVal_constsIn {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc} {j : Nat} {T : VIndType}
    (hB : D.Built R K env occ) (henv₂ : e₂.Ordered)
    (hΓ : CtxConstsIn e₂.contains D.params.reverse)
    (h₂ : env.addIndTypes D = some e₂) (h₁ : env.addIndTypesC D K = some e₁)
    (hS : D.ArgsTypedK K e₂ occ)
    (hp : ∀ B ∈ D.params, B.ConstsIn e₁.contains)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    (R.tyVal D j).ConstsIn e₁.contains := by
  have hle : env ≤ e₁ := by rw [VEnv.addIndTypesC] at h₁; exact VEnv.addConstList_le h₁
  have ho := (hB.occurs j T hT hK).toOccurs
  refine VExpr.constsIn_mkLams hp (VExpr.constsIn_mkApp ?_ ?_)
  · show e₁.contains (R.tyName j)
    rw [hB.tyName j T hT hK]
    exact ⟨_, hle.constants ho.ty_const⟩
  · rw [hB.tyArgs j T hT hK]
    exact VInductDecl'.ArgsTypedK.args_constsIn henv₂ hΓ h₂ h₁ hS
      (hB.kfresh.argsNoK j T hT hK) hT hK

/-! ## §6 The `WFC` route is closed — generally, and with no extra hypothesis

`docs/handoff-restrict.md` §6a listed, under "read off source, not independently proved":

> that `VInductDecl'.WFC` is unavailable on the nested path because a companion's constructor type
> is not well formed at `addIndTypesC`-env (read from `InductR.lean` §4's own note — I did **not**
> check it, and if it is wrong then `WFC` is a third route and a much shorter one).

It would indeed be a much shorter route: `VInductDecl'.WFC` (`Theory/Inductive/CompanionResolve.lean`)
is `VInductDecl'.WF` with the `ctors` clause re-staged from `addIndTypes`-env onto
**`addIndTypesC`-env — that is, onto `e₁`**, exactly where §3's residual lives.  Its `ctors` clause
would then give the companion's substituted field types at `e₁`, and
`VInductDecl'.WF.recField_canonResult`'s argument would produce the spine typing there, i.e. `ValAt`
in general.

The note is **right**, and the general reason is one line of `IsDefEq.constsIn`: a constructor's
`result` clause types the *member-headed* application `C.canonResult D j`, whose head constant is
the member's own name; at a companion member that name is by construction not declared at `e₁`.  So
`D.WFC env K` forces every companion member's constructor list to be **empty**
(`WFC.companion_ctors_nil`), and since a built companion's constructor list is the foreign block's
(`Built.member`), the route is available only when nesting through a **constructor-free** inductive
(`WFC.nested_src_ctors_nil`).

Note what this does *not* say: `WFC` is not thereby useless.  It was introduced for the
`fooComp` unsoundness witness, whose companion has `ctors = []`, and `CompanionResolve.lean`'s own
docstring says re-staging "restores the clause's *domain*; it does not give it any *content* at
`ctors = []`".  The theorem below is the exact scope of that domain: `ctors = []` is not one case
among many, it is the **only** case. -/

namespace VInductDecl'

/-- **THE `WFC` ROUTE IS CLOSED.**  `D.WFC env K` forces every companion member to have no
constructors.  The field context comes free from `VIndCtor.WF.onCtxAllFields`
(`Theory/Inductive/Lemmas.lean`), so this has no side condition beyond the three the re-staged
predicate is used with. -/
theorem WFC.companion_ctors_nil {env e₁ : VEnv} {D : VInductDecl'} {K : List Name}
    (he₁ : e₁.Ordered) (h₁ : env.addIndTypesC D K = some e₁)
    (hfresh : ∀ n ∈ K, ¬ env.contains n) (hwfc : D.WFC env K)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    T.ctors = [] := by
  cases hc : T.ctors with
  | nil => rfl
  | cons C Cs =>
    have hC : C ∈ T.ctors := by rw [hc]; exact List.mem_cons_self
    have hwf := hwfc.ctors e₁ h₁ j T hT C hC
    have hΓ := VEnv.ctxConstsIn_of_onCtx he₁ (hwf.onCtxAllFields he₁)
    have hcs := (hwf.result.constsIn he₁.constsIn hΓ).1
    rw [VIndCtor.canonResult, VInductDecl'.tyApp] at hcs
    have hhead := (VExpr.constsIn_mkApp_inv hcs).1
    rw [show (D.types.getD j default).name = T.name from by
      rw [List.getD_eq_getElem?_getD, hT]; rfl] at hhead
    exact absurd hhead (VEnv.not_contains_addIndTypesC h₁ hfresh hK)

/-- **…so the route exists only for nesting through a constructor-free inductive.**  A built
companion's constructor list is the foreign block's, mapped, so `WFC` forces the *foreign* member to
have no constructors either. -/
theorem WFC.nested_src_ctors_nil {env e₁ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {occ : Nat → VNestedOcc} (he₁ : e₁.Ordered)
    (h₁ : env.addIndTypesC D K = some e₁) (hfresh : ∀ n ∈ K, ¬ env.contains n)
    (hwfc : D.WFC env K) (hB : D.Built R K env occ)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    (occ j).src.ctors = [] := by
  have h := WFC.companion_ctors_nil he₁ h₁ hfresh hwfc hT hK
  rw [hB.member j T hT hK, VNestedOcc.member] at h
  exact List.map_eq_nil_iff.1 h

end VInductDecl'

/-! ### §6a …and it bites at the tree's own nested witness

Instantiation, not admiration: `nfnAux`'s companion member `_nested.PFn_1` has the constructor
`pfnAuxMk`, so §6's theorem refutes `WFC` there outright.  The staging is the one
`NestedWit.nfnAux_stage₁_exists` supplies, and `addIndTypesC` is `addConstList (typeConstsC …)` by
definition, so nothing new is assumed. -/

namespace NestedWit
open InductiveDeclExamples

/-- **`WFC` FAILS AT THE NESTED WITNESS.**  Existentially closed: no free variables, nothing
hypothesised.  So the third route is not merely unproved, it is refuted at the block the
development actually carries. -/
theorem nfnAux_not_WFC :
    ∃ env₂ F₁ : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.addIndTypesC nfnAux nfnK = some F₁ ∧ ¬ nfnAux.WFC env₂ nfnK := by
  obtain ⟨env₂, F₁, h, hF₁⟩ := nfnAux_stage₁_exists
  have h₁ : env₂.addIndTypesC nfnAux nfnK = some F₁ := by rw [VEnv.addIndTypesC]; exact hF₁
  have hF₁o : F₁.Ordered :=
    VEnv.addConstList_ordered (pfnEnv_ordered h) (VEnv.addInductR_typeConstsC_wf nfnAux_WF) hF₁
  refine ⟨env₂, F₁, h, h₁, fun hwfc => ?_⟩
  have := VInductDecl'.WFC.companion_ctors_nil hF₁o h₁ (nfnK_not_contains h) hwfc
    (show nfnAux.types[1]? = some _ from rfl) (by decide)
  exact absurd this (by simp)

end NestedWit

/-! ## §7 Inhabitation, stated separately from hole-freeness

`docs/vacuity-ledger.md` §0: the `#print axioms` lines below are hole-freeness and nothing else.
This section is the other question, and it is answered by instantiation rather than by argument.

* **§3's reduction fires**: `nfnAux_valAt_of_spineHargsK` closes `ValAt` at the `NFn`/`PFn` block
  through `valAt_of_spineHargsK` — i.e. through the `ty` half of the datum alone, with the
  constructor family never mentioned.  (`ArgsTypedSupply.lean` §10's `nfnAux_tyVal_hasType` closes
  the same clause through the whole datum; the point here is that the smaller input suffices at a
  real witness, not that the conclusion is new.)
* **§5's theorem fires**: `nfnAux_tyVal_constsIn` produces `ValAt`'s necessary condition at `e₁`
  from the datum at `e₂` alone.  At this witness the conclusion is also checkable directly (the
  value is `PFn NFn`, and `F₁` declares both), which is what makes it a *test* of the general
  theorem rather than a use of it.
* **§6's theorem fires**: `nfnAux_not_WFC` above.
* **Degeneracy, reported**: `nfnAux` has `uvars = 0` and `params = []`, so §5's `hΓ`/`hp` are
  `trivial` there.  The parameterised witness (`ntreeAux`, `np = 1`, `uvars = 1`) is where those
  two hypotheses have content, and I did **not** instantiate §5 or §3 at it.  `K ≠ []` at both. -/

namespace NestedWit
open InductiveDeclExamples

/-- The level side condition at this block, in the guarded form §3 takes it. -/
theorem nfnAux_tyLvls_wf : ∀ (j : Nat) (T : VIndType), nfnAux.types[j]? = some T →
    T.name ∈ nfnK → ∀ l ∈ nfnRestore'.tyLvls j, l.WF nfnAux.uvars := by
  rintro (_ | _ | j) T hT hK
  · cases hT; exact absurd hK (by decide)
  · exact (by decide)
  · simp [nfnAux] at hT

/-- **§3's REDUCTION, FIRING AT THE WITNESS.**  `ValAt` at `addIndTypesC`-env from the datum's
`ty` half alone. -/
theorem nfnAux_valAt_of_spineHargsK :
    ∃ env₂ E₁ F₁ : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.addIndTypes nfnAux = some E₁ ∧ env₂.addIndTypesC nfnAux nfnK = some F₁ ∧
      nfnAux.SpineHargsK nfnK F₁ (fun _ => pfnOcc) ∧
      nfnRestore'.ValAt nfnAux nfnK E₁ F₁ := by
  obtain ⟨env₂, F₁, h, hF₁⟩ := nfnAux_stage₁_exists
  obtain ⟨E₁, h₃⟩ := nfnAux_staged_exists h
  have hS : nfnAux.SpineHargsK nfnK F₁ (fun _ => pfnOcc) :=
    VInductDecl'.SpineHargsK.of_argsTypedK (nfnAux_argsTypedK hF₁)
  refine ⟨env₂, E₁, F₁, h, h₃, by rw [VEnv.addIndTypesC]; exact hF₁, hS, ?_⟩
  exact VIndRestore.valAt_of_spineHargsK (nfnAux_built'_of_blockK h) hS
    (VEnv.addConstList_le hF₁) (by exact trivial) h₃ nfnAux_tyLvls_wf

/-- **§5's THEOREM, FIRING AT THE WITNESS.**  The residual's constant-level necessary condition at
`e₁`, from the datum at `e₂` — so the pre-block refutation
(`NestedWit.pfnOcc_not_argsTypedH_pre`) has no analogue one stage later, at this block. -/
theorem nfnAux_tyVal_constsIn :
    ∃ env₂ E₁ F₁ : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.addIndTypes nfnAux = some E₁ ∧ env₂.addIndTypesC nfnAux nfnK = some F₁ ∧
      (nfnRestore'.tyVal nfnAux 1).ConstsIn F₁.contains := by
  obtain ⟨env₂, F₁, h, hF₁⟩ := nfnAux_stage₁_exists
  obtain ⟨E₁, h₃⟩ := nfnAux_staged_exists h
  have h₁ : env₂.addIndTypesC nfnAux nfnK = some F₁ := by rw [VEnv.addIndTypesC]; exact hF₁
  refine ⟨env₂, E₁, F₁, h, h₃, h₁, ?_⟩
  exact VIndRestore.tyVal_constsIn (nfnAux_built'_of_blockK h)
    (VInductDecl'.addIndTypes_ordered (pfnEnv_ordered h) nfnAux_WF h₃) trivial h₃ h₁
    (nfnAux_argsTypedK_of_wf nfnAux_WF h₃) nofun
    (show nfnAux.types[1]? = some _ from rfl) (by decide)

end NestedWit

end Lean4Lean

/-! ## §8 Grading: hole-freeness, per declaration

Every line is hole-freeness and nothing else (`docs/vacuity-ledger.md` §0); inhabitation is §7.
Names are read off this file's own `namespace` lines. -/

#print axioms Lean4Lean.VExpr.constsIn_mkLams_body
#print axioms Lean4Lean.VExpr.constsIn_mkPi_body
#print axioms Lean4Lean.VExpr.ConstsIn.and_noConsts
#print axioms Lean4Lean.ctxConstsIn_mem
#print axioms Lean4Lean.VInductDecl'.not_mem_K_of_mem_typeConstsC
#print axioms Lean4Lean.VEnv.not_contains_addIndTypesC
#print axioms Lean4Lean.VEnv.contains_addIndTypesC_of_addIndTypes
#print axioms Lean4Lean.VInductDecl'.SpineHargsK.of_argsTypedK
#print axioms Lean4Lean.VIndRestore.hargs_of_spineHargsK
#print axioms Lean4Lean.VIndRestore.valAt_of_spineHargsK
#print axioms Lean4Lean.VInductDecl'.spineHargsK_nil
#print axioms Lean4Lean.VInductDecl'.builtMember_codomain_constsIn
#print axioms Lean4Lean.VInductDecl'.WF.indices_constsIn
#print axioms Lean4Lean.VIndRestore.not_valAt_of_not_constsIn
#print axioms Lean4Lean.VInductDecl'.ArgsTypedK.args_constsIn
#print axioms Lean4Lean.VIndRestore.tyVal_constsIn
#print axioms Lean4Lean.VInductDecl'.WFC.companion_ctors_nil
#print axioms Lean4Lean.VInductDecl'.WFC.nested_src_ctors_nil
#print axioms Lean4Lean.NestedWit.nfnAux_not_WFC
#print axioms Lean4Lean.NestedWit.nfnAux_tyLvls_wf
#print axioms Lean4Lean.NestedWit.nfnAux_valAt_of_spineHargsK
#print axioms Lean4Lean.NestedWit.nfnAux_tyVal_constsIn
