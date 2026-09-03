import Lean4Lean.Theory.Typing.ConstSubstNested
import Lean4Lean.Theory.Typing.ConstVar
import Lean4Lean.Verify.Inductive.ArgsTypedSupply

/-!
# The restriction lemma: what it is, what it costs, and why it is not the producer

`docs/handoff-argstyped.md` §8/§9 named one residual as "the whole distance from two witnesses
to a general route":

> `WF.ctors` is staged at `env.addIndTypes D` (companions **declared**); §8.7 consumes `hargs`
> at `AddInductStagesR`'s second stage (companions **absent**).  Incomparable.  Missing: a
> **restriction lemma** — a derivation whose subject avoids the companion names replays without
> them.  That one `VEnv`-only lemma is the whole distance.

This file measures that sentence.  Three results, in descending order of value:

1. **The restriction lemma is PROVED** (§1), general, hole-free, and with no
   `HasArgs.of_mkApp`: `VEnv.HasArgs.restrictC` and its `HasType`/`IsDefEqU` companions.  The
   engine is `VEnv.IsDefEq.substC` (`Theory/Typing/ConstSubst.lean`) — the one transport in
   `Theory/` that can *remove* a constant — plus `VExpr.NoCSubst.substC_eq`.  It is not new
   mathematics; it is three lines once the right transport is named, and the point of stating
   it is what §3 then measures about its hypothesis.
2. **The environments are NOT incomparable** (§2): `env.addIndTypesC D K = some e₁` and
   `env.addIndTypes D = some e₃` give `e₁ ≤ e₃`, proved.  So the pair (`WF.ctors`' staging,
   §8.7's staging) factors: **restrict** from `e₃` down to `e₁`, then **weaken** up to any
   later stage, `IsDefEq.mono` being free.  Only the first leg is missing, and it drops
   *constants only* — `addIndTypes` registers no defeq.
3. **The restriction lemma is not the producer of the datum** (§3), and this is the finding.
   Its hypothesis is a `CSubst.WF` (or the weaker `CSubst.WFD`), whose `val` field at a
   companion member `j` is, on the nose,
   `e₁.HasType D.uvars [] (R.tyVal D j) (T.type.substC σ)` — **§8.7's own `val` clause at the
   target environment**, which `Verify/Inductive/ArgsTypedSupply.lean`
   (`tyVal_hasType_of_argsTypedK`) derives from the datum *at that environment*.  So the only
   non-open route from `e₃` to `e₁` consumes a consequence of what it is asked to produce.
   Both halves are machine-checked here.
4. **The alternative is an open hole** (§4): dropping a constant with *no* inhabitant is
   `AxiomConservativityWF`, which `Theory/Typing/ConstVar.lean` proves **equivalent** to
   `StrengtheningTarget` — the forward direction of `VEnv.IsDefEqU.weakN_iff`, a `sorry` in
   `Theory/Typing/UniqueTyping.lean`.  So the unconditional restriction is not a small
   `VEnv`-only lemma: it *is* the tree's strengthening hole.

**Nothing here makes the flip**, and the general discharge is not achieved: §5 says what would
achieve it, and it is a producer at `e₁` (§9's `TrIndDeclN` clause), not a restriction.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkLams mkApp instTele)

/-! ## §1 The restriction lemma

Stated for `HasArgs` because that is the shape the datum is in (`VNestedOcc.ArgsTypedH.ty`),
and proved for `IsDefEq` because that is where the work is.  No `PiInv`, no `of_mkApp`: the
telescope is never inverted, it is carried. -/

/-- Every entry of an instantiated telescope is `σ`-free if the telescope and the substituted
term are. -/
theorem VExpr.noCSubst_instTele {σ : CSubst} {a : VExpr} (ha : a.NoCSubst σ) :
    ∀ {As : List VExpr} {k : Nat}, (∀ A ∈ As, A.NoCSubst σ) →
      ∀ A ∈ VExpr.instTele a As k, A.NoCSubst σ
  | [], _, _, _, h => nomatch h
  | A :: As, k, hAs, B, hB => by
    rcases List.mem_cons.1 hB with rfl | hB
    · exact (hAs A List.mem_cons_self).inst ha
    · exact noCSubst_instTele ha (fun C hC => hAs C (List.mem_cons_of_mem _ hC)) _ hB

/-- The same for `ConstsIn`, which is the predicate §4's route carries. -/
theorem VExpr.constsIn_instTele {P : Name → Prop} {a : VExpr} (ha : a.ConstsIn P) :
    ∀ {As : List VExpr} {k : Nat}, (∀ A ∈ As, A.ConstsIn P) →
      ∀ A ∈ VExpr.instTele a As k, A.ConstsIn P
  | [], _, _, _, h => nomatch h
  | A :: As, k, hAs, B, hB => by
    rcases List.mem_cons.1 hB with rfl | hB
    · exact ha.inst (hAs A List.mem_cons_self)
    · exact constsIn_instTele ha (fun C hC => hAs C (List.mem_cons_of_mem _ hC)) _ hB

/-- A `σ`-free context is unchanged by `σ`. -/
theorem CSubst.map_substC_eq {σ : CSubst} : ∀ {Γ : List VExpr}, (∀ B ∈ Γ, B.NoCSubst σ) →
    Γ.map (VExpr.substC · σ) = Γ
  | [], _ => rfl
  | A :: Γ, h => by
    rw [List.map_cons, (h A List.mem_cons_self).substC_eq,
      map_substC_eq fun B hB => h B (List.mem_cons_of_mem _ hB)]

namespace VEnv

variable {env₀ env₁ : VEnv} {σ : CSubst} {U : Nat} {Γ : List VExpr}

/-- **THE RESTRICTION LEMMA, for a conversion.**  A judgement over `env₀` whose context and
endpoints mention no constant `σ` replaces holds over `env₁`, which need declare none of
them. -/
theorem IsDefEqU.restrictC (hσ : σ.WF env₀ env₁ U) (hΓ : ∀ B ∈ Γ, B.NoCSubst σ)
    {e1 e2 : VExpr} (h1 : e1.NoCSubst σ) (h2 : e2.NoCSubst σ)
    (H : env₀.IsDefEqU U Γ e1 e2) : env₁.IsDefEqU U Γ e1 e2 := by
  have := H.substC hσ
  rwa [CSubst.map_substC_eq hΓ, h1.substC_eq, h2.substC_eq] at this

/-- **THE RESTRICTION LEMMA, for a typing.** -/
theorem HasType.restrictC (hσ : σ.WF env₀ env₁ U) (hΓ : ∀ B ∈ Γ, B.NoCSubst σ)
    {e A : VExpr} (he : e.NoCSubst σ) (hA : A.NoCSubst σ)
    (H : env₀.HasType U Γ e A) : env₁.HasType U Γ e A := by
  have := H.substC hσ
  rwa [CSubst.map_substC_eq hΓ, he.substC_eq, hA.substC_eq] at this

/-- **THE RESTRICTION LEMMA, in the shape the nested datum is in.**  `VNestedOcc.ArgsTypedH.ty`
is a `HasArgs`; this replays it in an environment that has dropped the companion constants.
The telescope is *carried*, never inverted, so no `PiInv` and no `HasArgs.of_mkApp`. -/
theorem HasArgs.restrictC (hσ : σ.WF env₀ env₁ U) (hΓ : ∀ B ∈ Γ, B.NoCSubst σ) :
    ∀ {As as : List VExpr}, (∀ A ∈ As, A.NoCSubst σ) → (∀ a ∈ as, a.NoCSubst σ) →
      env₀.HasArgs U Γ As as → env₁.HasArgs U Γ As as
  | _, _, _, _, .nil => .nil
  | A :: As, a :: as, hAs, has, .cons ha h => by
    refine .cons (ha.restrictC hσ hΓ (has a List.mem_cons_self) (hAs A List.mem_cons_self))
      (HasArgs.restrictC hσ hΓ ?_ (fun b hb => has b (List.mem_cons_of_mem _ hb)) h)
    exact VExpr.noCSubst_instTele (has a List.mem_cons_self)
      fun B hB => hAs B (List.mem_cons_of_mem _ hB)

end VEnv

/-! ## §2 The two stagings are NOT incomparable

`docs/handoff-argstyped.md` §8/§9 say of `env.addIndTypes D` (where `WF.ctors` is staged) and
`AddInductStagesR`'s stages (where §8.7 consumes): "**The two are incomparable.**"  Half of that
is right and the load-bearing half is wrong.

* The **second** stage is indeed incomparable with `addIndTypes`: it declares the block's
  constructor constants, which `addIndTypes` does not, and it does *not* declare the companion
  type constants, which `addIndTypes` does.
* But the **first** stage is `env.addIndTypesC D K` (`AddInductStagesR.addIndTypesC`), and
  `addIndTypesC` ≤ `addIndTypes`, proved below.  Since `IsDefEq.mono` weakens for free along
  `AddInductStagesR`'s remaining stages, the transport factors as

      addIndTypes-env  --restrict-->  addIndTypesC-env  --mono-->  stage 2  --mono-->  output

  and only the first leg is missing.  What is more, that leg drops **constants only**:
  `addIndTypes` is an `addConstList`, so it registers no definitional equation
  (`addConstList_defeqs`), and the ι-rules arrive strictly later.

So the residual is not "two incomparable environments" but the one-directional step of a
`≤`-chain, which is what makes §1's `substC` route applicable at all. -/

theorem VInductDecl'.mem_typeConsts_of_mem_typeConstsC {D : VInductDecl'} {K : List Name}
    {c : Name × VConstant} (h : c ∈ D.typeConstsC K) : c ∈ D.typeConsts := by
  rw [VInductDecl'.typeConstsC, List.mem_filterMap] at h
  obtain ⟨a, ha, he⟩ := h
  split at he
  · exact absurd he nofun
  · cases he; exact ha

/-- **The companion-aware staging is BELOW the full one.**  Corrects
`docs/handoff-argstyped.md` §8's "the two are incomparable" for the pair that matters. -/
theorem VEnv.addIndTypesC_le_addIndTypes {env e₁ e₃ : VEnv} {D : VInductDecl'} {K : List Name}
    (h₁ : env.addIndTypesC D K = some e₁) (h₃ : env.addIndTypes D = some e₃) : e₁ ≤ e₃ := by
  rw [VEnv.addIndTypesC] at h₁; rw [VEnv.addIndTypes] at h₃
  refine ⟨fun {n a} hn => ?_, fun {df} hdf => ?_⟩
  · by_cases hm : n ∈ (D.typeConstsC K).map (·.1)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
      rw [VEnv.addConstList_constants h₁ c hc] at hn
      cases hn
      exact VEnv.addConstList_constants h₃ c (VInductDecl'.mem_typeConsts_of_mem_typeConstsC hc)
    · rw [VEnv.addConstList_constants_of_not_mem h₁ hm] at hn
      exact (VEnv.addConstList_le h₃).constants hn
  · rw [VEnv.addConstList_defeqs h₁] at hdf
    rw [VEnv.addConstList_defeqs h₃]; exact hdf

/-! ## §3 The price of §1's hypothesis — and why the restriction is not the producer

§1's hypothesis is `σ.WF env₀ env₁ U`.  Its `val` field is not bookkeeping: it says that the
value replacing each dropped constant **inhabits that constant's declared type in the target
environment**.  At the nested step the substitution is `R.csubstTy D K`
(`Theory/Inductive/Restore.lean`), whose entry at a companion member `j` is `R.tyVal D j`, and
whose declared type is the member's own `T.type`.  So the field reads

    e₁.HasType D.uvars [] (R.tyVal D j) T.type

which is **§8.7's `val` clause at `e₁`** — the very thing
`Verify/Inductive/ArgsTypedSupply.lean` derives *from the datum at `e₁`*
(`VIndRestore.tyVal_hasType_of_argsTypedK`).

Both halves are below.  Together they say: the only non-open transport that can drop a constant
requires, as an input at the **target** environment, a consequence of the datum it would be used
to move there.  A restriction lemma is therefore a *transport* for this datum and not a
*producer* of it — which is what `docs/handoff-argstyped.md` §9 assumed it would be.

**What is not claimed.**  This is not a proof that the two are equivalent.  The gap is exactly
`VEnv.HasArgs.of_mkApp` (Π-inversion): the datum implies the `val` clause outright, while the
`val` clause implies the datum only by inverting the application spine, which the nested corner
keeps out on purpose.  So the honest statement is a **sandwich**, not a circle: the hypothesis
of §1's route and its conclusion both entail the same clause at `e₁`, and no route is known
from that clause back to the hypothesis-free side. -/

namespace CSubst

/-- **The `val` field, projected to a typing.**  This is the substantive content of §1's
hypothesis: an inhabitant, in the target environment, of the type of each dropped constant. -/
theorem WF.val_hasType {env₀ env₁ : VEnv} {σ : CSubst} {U : Nat} {c : Name} {t : VExpr}
    {ci : VConstant} {ls : List VLevel} (hσ : σ.WF env₀ env₁ U) (hdom : σ c = some t)
    (hc : env₀.constants c = some ci) (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = ci.uvars) :
    env₁.HasType U [] (t.instL ls) ((ci.type.substC σ).instL ls) :=
  (hσ.val hdom hc hls hls (LEqv.refl ls) hlen).hasType.1

end CSubst

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env env₃ e₁ : VEnv}
  {occ : Nat → VNestedOcc} {j : Nat} {T : VIndType}

/-- **HALF ONE OF THE SANDWICH.**  §1's hypothesis, at a companion member, *is* §8.7's `val`
clause at the target environment. -/
theorem restrictC_hypothesis_gives_val
    (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars)
    (hc : env₃.constants T.name = some ⟨D.uvars, T.type⟩)
    (hdom : R.csubstTy D K T.name = some (R.tyVal D j))
    (hfree : T.type.NoCSubst (R.csubstTy D K))
    (hlv : (R.tyVal D j).LevelWF D.uvars) (hlt : T.type.LevelWF D.uvars) :
    e₁.HasType D.uvars [] (R.tyVal D j) T.type := by
  have h := hσ.val_hasType (ls := VLevel.params D.uvars) hdom hc VLevel.params_wf
    (by simp [VLevel.params_length])
  rwa [hfree.substC_eq, hlv.instL_id, hlt.instL_id] at h

/-- **HALF TWO OF THE SANDWICH.**  The datum at the target environment produces the same
clause — this is `ArgsTypedSupply.lean` §2.1, unchanged, restated here only so that the two
halves stand side by side. -/
theorem restrictC_conclusion_gives_val (hB : D.Built R K env occ)
    (hS : D.ArgsTypedK K e₁ occ) (hle : env ≤ e₁)
    (hparams : OnCtx D.params.reverse (e₁.IsType D.uvars))
    (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars) :
    e₁.HasType D.uvars [] (R.tyVal D j) T.type :=
  tyVal_hasType_of_argsTypedK' hB hS hle hparams hT hK hlvl

/-- **THE SANDWICH.**  Everything §1 needs to move the datum from `env₃` down to `e₁`, and
everything the datum at `e₁` gives, meet at the same clause.  Read as a measurement: a
restriction lemma cannot be the datum's general producer, because its own hypothesis is
already at the target environment. -/
theorem restrictC_sandwich
    (hc : env₃.constants T.name = some ⟨D.uvars, T.type⟩)
    (hdom : R.csubstTy D K T.name = some (R.tyVal D j))
    (hfree : T.type.NoCSubst (R.csubstTy D K))
    (hlv : (R.tyVal D j).LevelWF D.uvars) (hlt : T.type.LevelWF D.uvars)
    (hB : D.Built R K env occ) (hle : env ≤ e₁)
    (hparams : OnCtx D.params.reverse (e₁.IsType D.uvars))
    (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars) :
    ((R.csubstTy D K).WF env₃ e₁ D.uvars → e₁.HasType D.uvars [] (R.tyVal D j) T.type) ∧
    (D.ArgsTypedK K e₁ occ → e₁.HasType D.uvars [] (R.tyVal D j) T.type) :=
  ⟨fun hσ => restrictC_hypothesis_gives_val hσ hc hdom hfree hlv hlt,
   fun hS => restrictC_conclusion_gives_val hB hS hle hparams hT hK hlvl⟩

end VIndRestore

/-! ## §4 The unconditional restriction is an open hole — and the typed form costs more

§1 needs an inhabitant (§3 measures which one).  The *unconditional* statement — drop a
constant with nothing said about its type — already has a name in this tree:
`VEnv.AxiomConservativityWF` (`Theory/Typing/ConstVar.lean`), and that file proves

    AxiomConservativityWF env U ↔ StrengtheningTarget env U      (`axiomConservativityWF_iff_target`)

with `StrengtheningTarget` the forward direction of `VEnv.IsDefEqU.weakN_iff` — a `sorry` in
`Theory/Typing/UniqueTyping.lean`.  So `docs/handoff-argstyped.md` §9's "that one `VEnv`-only
lemma" is not a small lemma: **unconditionally it *is* the tree's strengthening hole**, and
proving it would close `weakN_iff` as a corollary.

Two further measurements, both consequences of writing the route out:

* the residual delivers the **untyped** restriction directly (`restrict_of_conservativity`), but
  the datum is a `HasArgs`, i.e. a *typed* judgement, and the typed form needs **uniqueness of
  types at the larger environment** on top (`IsDefEq.uniqU`, hence `VEnv.WF env'`).  That is
  recorded as an explicit hypothesis below rather than assumed away.
* nothing in this section is `PiInv`-free by the standard of the nested corner: `uniqU` lives in
  `UniqueTyping.lean`.  §1's route, by contrast, uses only `substC` and stays clean — which is
  the one advantage the inhabited route has, and worth keeping in view. -/

namespace VEnv

variable {env env' : VEnv} {U : Nat} {Γ : List VExpr} {c : Name} {ci : VConstant}

/-- **The untyped restriction, from the residual.**  Wiring, stated so that §4's price is
attached to a statement in this file's vocabulary rather than to a citation. -/
theorem IsDefEqU.restrict_of_conservativity {e1 e2 : VExpr} (H : AxiomConservativityWF env U)
    (hadd : env.addConst c ci = some env') (hci : ci.WF env) (hu : ci.uvars = U)
    (hΓ : OnCtx Γ (env.IsType U)) (hΓc : CtxConstsIn env.contains Γ)
    (h1 : e1.ConstsIn env.contains) (h2 : e2.ConstsIn env.contains)
    (h : env'.IsDefEqU U Γ e1 e2) : env.IsDefEqU U Γ e1 e2 :=
  H hadd hci hu hΓ hΓc h1 h2 h

/-- **The typed restriction**: the untyped one plus uniqueness of types at `env'`.  The type
produced by the untyped statement is not the one asked for, and the two are compared upstairs. -/
theorem IsDefEq.restrict_of_conservativity {e1 e2 A : VExpr} (henv : VEnv.WF env)
    (henv' : VEnv.WF env') (H : AxiomConservativityWF env U)
    (hadd : env.addConst c ci = some env') (hci : ci.WF env) (hu : ci.uvars = U)
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : e1.ConstsIn env.contains) (h2 : e2.ConstsIn env.contains)
    (hA : A.ConstsIn env.contains)
    (h : env'.IsDefEq U Γ e1 e2 A) : env.IsDefEq U Γ e1 e2 A := by
  have hle : env ≤ env' := VEnv.addConst_le hadd
  have hΓc : CtxConstsIn env.contains Γ := ctxConstsIn_of_onCtx henv.ordered hΓ
  have hΓ' : OnCtx Γ (env'.IsType U) := hΓ.mono fun hh => hh.mono hle
  obtain ⟨A', hA'⟩ := H hadd hci hu hΓ hΓc h1 h2 ⟨_, h⟩
  have hA'c : A'.ConstsIn env.contains :=
    (hA'.constsIn henv.ordered.constsIn hΓc).2.2
  have huq : env'.IsDefEqU U Γ A' A := (hA'.mono hle).uniqU henv' hΓ' h.symm
  exact IsDefEqU.defeqDF henv hΓ (H hadd hci hu hΓ hΓc hA'c hA huq) hA'

/-- **The restriction the datum's shape asks for, from the residual.**  `HasArgs` is a list of
typings against a carried telescope, so the typed form transports it entry by entry — again with
no Π-inversion of the telescope. -/
theorem HasArgs.restrict_of_conservativity (henv : VEnv.WF env) (henv' : VEnv.WF env')
    (H : AxiomConservativityWF env U)
    (hadd : env.addConst c ci = some env') (hci : ci.WF env) (hu : ci.uvars = U)
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {As as : List VExpr}, (∀ A ∈ As, A.ConstsIn env.contains) →
      (∀ a ∈ as, a.ConstsIn env.contains) → env'.HasArgs U Γ As as → env.HasArgs U Γ As as
  | _, _, _, _, .nil => .nil
  | A :: As, a :: as, hAs, has, .cons ha h => by
    refine .cons (IsDefEq.restrict_of_conservativity henv henv' H hadd hci hu hΓ
        (has a List.mem_cons_self) (has a List.mem_cons_self) (hAs A List.mem_cons_self) ha)
      (HasArgs.restrict_of_conservativity henv henv' H hadd hci hu hΓ ?_
        (fun b hb => has b (List.mem_cons_of_mem _ hb)) h)
    exact VExpr.constsIn_instTele (has a List.mem_cons_self)
      fun B hB => hAs B (List.mem_cons_of_mem _ hB)

/-- **The unconditional restriction IS the open hole**, re-exported so that the price is stated
here in one line.  `StrengtheningTarget` is `VEnv.IsDefEqU.weakN_iff`'s forward direction, the
`sorry` of `Theory/Typing/UniqueTyping.lean`. -/
theorem restrict_unconditional_iff_target (henv : VEnv.WF env) :
    AxiomConservativityWF env U ↔ StrengtheningTarget env U :=
  axiomConservativityWF_iff_target henv

end VEnv

/-! ## §5 Grading: hole-freeness, per declaration

Every line below is **hole-freeness and nothing else** (`docs/vacuity-ledger.md` §0).
Inhabitation is a separate question and is discussed in §6. -/

#print axioms Lean4Lean.VExpr.noCSubst_instTele
#print axioms Lean4Lean.VExpr.constsIn_instTele
#print axioms Lean4Lean.CSubst.map_substC_eq
#print axioms Lean4Lean.VEnv.IsDefEqU.restrictC
#print axioms Lean4Lean.VEnv.HasType.restrictC
#print axioms Lean4Lean.VEnv.HasArgs.restrictC
#print axioms Lean4Lean.VInductDecl'.mem_typeConsts_of_mem_typeConstsC
#print axioms Lean4Lean.VEnv.addIndTypesC_le_addIndTypes
#print axioms Lean4Lean.CSubst.WF.val_hasType
#print axioms Lean4Lean.VIndRestore.restrictC_hypothesis_gives_val
#print axioms Lean4Lean.VIndRestore.restrictC_conclusion_gives_val
#print axioms Lean4Lean.VIndRestore.restrictC_sandwich
#print axioms Lean4Lean.VEnv.IsDefEqU.restrict_of_conservativity
#print axioms Lean4Lean.VEnv.IsDefEq.restrict_of_conservativity
#print axioms Lean4Lean.VEnv.HasArgs.restrict_of_conservativity
#print axioms Lean4Lean.VEnv.restrict_unconditional_iff_target

/-! ## §6 The datum's own restriction, and it fires at the parameterised witness

§1 applied to the datum itself.  `VNestedOcc.ArgsTypedH` is two `HasArgs` and one level
condition, so its restriction is §1 twice plus a transport of a `VLevel` fact that mentions no
environment at all.

Then the instantiation, which is the point: at the `NTree`/`List` block — the parameterised one,
`np = 1`, the block Lean's own kernel runs the nested elimination on —
`InductiveDeclExamples.ntreeSubst_WF` (`Theory/Typing/ConstSubstNested.lean`) **already supplies
§1's hypothesis at exactly the two environments of the gap**: `env₂ = env₁.addIndTypes ntreeAux`
(companions declared, where `WF.ctors` stages) and `env₃ = env₁.addConstList (typeConstsC …)`
(companions absent, `AddInductStagesR`'s first stage).  So the restriction *fires*, and the
`D.WF`-supplied datum really does descend to the environment §8.7 wants.

What that does **not** do is generalise: `ntreeSubst_WF`'s own `val` clause is discharged at that
witness by `type_tac` on a concrete spine, and §3 is the measurement that in general that clause is
the datum at the target environment.  So this section is inhabitation, not a route. -/

namespace VNestedOcc

variable {N : VNestedOcc} {D : VInductDecl'} {env₀ env₁ : VEnv} {σ : CSubst}

/-- **THE DATUM'S RESTRICTION.**  The four `NoCSubst` side conditions are the honest content:
the block's parameters, the presented spine, and both telescopes must avoid the dropped names.
`RestoreData.args` / `OccursN.args_noNested` are what supply the spine one in the tree. -/
theorem ArgsTypedH.restrictC (hσ : σ.WF env₀ env₁ D.uvars)
    (hΓ : ∀ B ∈ D.params.reverse, B.NoCSubst σ)
    (hargs : ∀ a ∈ N.args, a.NoCSubst σ)
    (hty : ∀ A ∈ (VExpr.splitPis N.decl.np (N.src.type.instL N.lvls)).1, A.NoCSubst σ)
    (hctor : ∀ C ∈ N.src.ctors,
      ∀ A ∈ (VExpr.splitPis N.decl.np ((C.type N.decl N.idx).instL N.lvls)).1, A.NoCSubst σ)
    (H : N.ArgsTypedH D env₀) : N.ArgsTypedH D env₁ where
  lvls := H.lvls
  ty := H.ty.restrictC hσ hΓ hty hargs
  ctor := fun C hC => (H.ctor C hC).restrictC hσ hΓ (hctor C hC) hargs

end VNestedOcc

/-- **…and for the whole `Verify/`-side family.** -/
theorem VInductDecl'.ArgsTypedK.restrictC {D : VInductDecl'} {K : List Name} {env₀ env₁ : VEnv}
    {σ : CSubst} {occ : Nat → VNestedOcc} (hσ : σ.WF env₀ env₁ D.uvars)
    (hΓ : ∀ B ∈ D.params.reverse, B.NoCSubst σ)
    (hargs : ∀ j, ∀ a ∈ (occ j).args, a.NoCSubst σ)
    (hty : ∀ j, ∀ A ∈ (VExpr.splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1,
      A.NoCSubst σ)
    (hctor : ∀ j, ∀ C ∈ (occ j).src.ctors, ∀ A ∈ (VExpr.splitPis (occ j).decl.np
        ((C.type (occ j).decl (occ j).idx).instL (occ j).lvls)).1, A.NoCSubst σ)
    (H : D.ArgsTypedK K env₀ occ) : D.ArgsTypedK K env₁ occ :=
  fun j T hT hK => (H j T hT hK).restrictC hσ hΓ (hargs j) (hty j) (hctor j)

#print axioms Lean4Lean.VNestedOcc.ArgsTypedH.restrictC
#print axioms Lean4Lean.VInductDecl'.ArgsTypedK.restrictC

/-! ## §7 The side conditions are free — everything is concentrated in `σ.WF`

§6's four `NoCSubst` conditions are not the residual, and it matters to say so, because it is
what makes §3 the whole price.  Three of the four come from `Occurs` and `Ordered` alone:

* the two telescopes are `splitPis` of the **foreign** block's member and constructor types, and
  `Occurs.ty_const` / `Occurs.ctor_const` say those types are declared in `env`, so
  `Ordered.noCSubstC` gives them once `σ`'s domain is fresh in `env` — which it is, the companion
  names being `mkUniqueName`'s;
* the parameter context is `env`-constant-closed for the same reason.

Only the **spine** condition is a real hypothesis, and the tree supplies it too:
`RestoreData.args` / `OccursN.args_noNested` say the spine mentions no `_nested` name, which is
exactly `NoCSubst` at a substitution whose domain is those names.

So `ArgsTypedH.restrictC'` below has, as its only environment-sensitive input, `σ.WF env₀ env₁ U`
— and §3 is the measurement of what that costs. -/

/-- **`ConstsIn` implies `NoCSubst` at a fresh substitution.**  The bridge between the two
freshness vocabularies (`Theory/SetModel/Consts.lean`'s and `Theory/Typing/ConstSubst.lean`'s). -/
theorem VExpr.ConstsIn.noCSubst {env : VEnv} {σ : CSubst} (hf : σ.FreshIn env) :
    ∀ {e : VExpr}, e.ConstsIn env.contains → e.NoCSubst σ
  | .bvar _, _ | .sort _, _ => trivial
  | .const .., h => let ⟨_, h⟩ := h; hf _ _ h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.noCSubst hf, h.2.noCSubst hf⟩

/-! `VExpr.NoCSubst.splitPis` — "`NoCSubst` survives `splitPis`" — already exists, in
`Theory/Inductive/NestedTele.lean`; the duplicate this file first declared was caught by Lean at
the point of use, which is the collision class `scripts/dup-names.lean` exists for.  It is used
below through its first component. -/

namespace VNestedOcc

/-- **THE DATUM'S RESTRICTION, with the side conditions discharged from `Occurs`.**  One
environment-sensitive hypothesis remains, and it is the one §3 prices. -/
theorem ArgsTypedH.restrictC' {N : VNestedOcc} {D : VInductDecl'} {env env₀ env₁ : VEnv}
    {σ : CSubst} (hσ : σ.WF env₀ env₁ D.uvars) (henv : env.Ordered) (hf : σ.FreshIn env)
    (ho : N.Occurs env) (hp : ∀ B ∈ D.params.reverse, B.ConstsIn env.contains)
    (hargs : ∀ a ∈ N.args, a.NoCSubst σ) (H : N.ArgsTypedH D env₀) : N.ArgsTypedH D env₁ :=
  H.restrictC hσ
    (fun B hB => (hp B hB).noCSubst hf)
    hargs
    (VExpr.NoCSubst.splitPis ((henv.noCSubstC hf ho.ty_const).instL)).1
    (fun C hC => (VExpr.NoCSubst.splitPis ((henv.noCSubstC hf (ho.ctor_const C hC)).instL)).1)

end VNestedOcc

/-! ## §8 The restriction fires, at the parameterised block — a closed theorem

`InductiveDeclExamples.ntreeSubst_WF` (`Theory/Typing/ConstSubstNested.lean`) supplies §1's
hypothesis at **exactly the two environments of `docs/handoff-argstyped.md` §8's gap**:

* `env₂ = env₁.addIndTypes ntreeAux` — companions declared, where `VInductDecl'.WF.ctors` stages
  and where `ArgsTypedSupply.lean` §10 puts the datum;
* `env₃ = env₁.addConstList (ntreeAux.typeConstsC ntreeK)` — companions absent, i.e.
  `env₁.addIndTypesC ntreeAux ntreeK`, `AddInductStagesR`'s **first stage**, which is `≤` every
  later stage.

So at the `NTree`/`List` block the datum descends from the first to the second, with nothing
hypothesised.  `ArgsTypedSupply.lean` §10's `ntreeAux_datum_of_wf_inhabited` puts the datum only
at `env₂`; this puts it where §8.7 consumes it.

**Not a route.**  `ntreeSubst_WF`'s `val` clause is discharged at this witness by `type_tac` on a
concrete spine (`List.{u} (NTree.{u} #0)` at `Type u → Type u`), and §3 is the measurement that in
general that clause *is* the datum at the target environment.  Two witnesses with the transport are
still two witnesses. -/

namespace InductiveDeclExamples

open VEnv (addIndTypesC)

/-- The spine of the `List` occurrence mentions `NTree`, which the restoration does not replace. -/
theorem listOcc_args_noCSubst : ∀ a ∈ listOcc.args, a.NoCSubst ntreeSubst :=
  fun _ h => by
    simp only [listOcc, List.mem_singleton] at h
    subst h
    exact ⟨rfl, trivial⟩

/-- The block's parameters are a sort, hence mention no constant at all. -/
theorem ntreeAux_params_constsIn {env : VEnv} :
    ∀ B ∈ ntreeAux.params.reverse, B.ConstsIn env.contains := fun _ h => by
  simp only [ntreeAux, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.mem_singleton] at h
  subst h; trivial

/-- **THE RESTRICTION, AT THE PARAMETERISED NESTED BLOCK.**  The datum crosses
`docs/handoff-argstyped.md` §8's environment gap. -/
theorem ntreeAux_argsTypedK_restrict {env₁ env₂ env₃ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (h₂ : env₁.addIndTypes ntreeAux = some env₂)
    (h₃ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃) :
    ntreeAux.ArgsTypedK ntreeK env₃ (fun _ => listOcc) := by
  have henv₁ := listEnv_ordered h
  have hσ := ntreeSubst_WF h henv₁ h₂ h₃
  intro j T hT hK
  exact ((ntreeAux_argsTypedK_of_wf h h₂) j T hT hK).restrictC' hσ henv₁
    (ntreeSubst_fresh h) (listOcc_occurs h).toOccurs ntreeAux_params_constsIn
    listOcc_args_noCSubst

/-- …and with the staging existentially closed: **no free variables, nothing hypothesised**.
The last conjunct is the datum at `addIndTypesC`'s environment — `AddInductStagesR`'s first
stage — for the block Lean's own kernel runs the nested elimination on. -/
theorem ntreeAux_datum_at_stage₁ :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some env₃ ∧
      env₃ ≤ env₂ ∧
      ntreeAux.ArgsTypedK ntreeK env₃ (fun _ => listOcc) := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  exact ⟨env₁, env₂, env₃, h, h₂, h₃,
    VEnv.addIndTypesC_le_addIndTypes h₃ h₂, ntreeAux_argsTypedK_restrict h h₂ h₃⟩

end InductiveDeclExamples

#print axioms Lean4Lean.VExpr.ConstsIn.noCSubst
#print axioms Lean4Lean.VNestedOcc.ArgsTypedH.restrictC'
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_argsTypedK_restrict
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_datum_at_stage₁

/-! ## §9 What this changes, and where the brief was wrong

**(a) "That one `VEnv`-only lemma is the whole distance from two witnesses to a general route."**
Wrong in both halves, and the two errors point in opposite directions.

* The lemma is **not the distance**: it is *proved* here (§1), hole-free, in twenty lines, because
  `Theory/Typing/ConstSubst.lean` already had the only transport that can remove a constant.  What
  was missing was not a proof but the observation that `substC` is that transport.
* But proving it does **not** produce a general route, because its hypothesis `σ.WF env₀ env₁ U`
  carries a `val` field that, at a companion member, *is* §8.7's `val` clause at the target
  environment — the datum's own consequence there (§3).  A restriction lemma transports this datum;
  it cannot produce it.
* And the **`VEnv`-only** version — drop a constant with nothing assumed about its type — is
  `AxiomConservativityWF`, which `Theory/Typing/ConstVar.lean` proves is *equivalent to
  `StrengtheningTarget`*, the `sorry` of `Theory/Typing/UniqueTyping.lean` (§4).  So the `VEnv`-only
  reading of the brief's sentence is not a small lemma; it is the tree's strengthening hole.

**(b) "Incomparable."**  Only for the *second* stage.  `addIndTypesC`'s environment — the **first**
stage, which `AddInductStagesR.addIndTypesC` produces — is `≤` `addIndTypes`' (§2, proved), and
`IsDefEq.mono` covers the rest of the chain.  So the transport is one-directional along a `≤`-chain,
which is why §1 applies at all.

**(c) "check that shape first: a derivation can mention a constant in a *type* without the subject
mentioning it".**  Right, and it is why every `ConstsIn`-style pruning argument fails and `substC`
succeeds — `substC` rewrites the *whole derivation*, types and middle terms included.  The shape is
already machine-checked upstream (`VEnv.axiomConservativity_fires`,
`Theory/Typing/StrengthenAxiom.lean`: two `c`-free endpoints joined by a `trans` whose middle term
is not `c`-free), so it is not a new refutation and the restriction is **not false as stated**.

**(d) The typed/untyped split, which the brief does not mention and which prices route §4 twice
over.**  `AxiomConservativityWF` is a statement about `IsDefEqU` — it loses the type.  The datum is
a `HasArgs`, i.e. *typed*.  Recovering the type costs `IsDefEq.uniqU`, and `uniqU` is `sorryAx`-
tainted (measured: `IsDefEq.uniqU` and `IsDefEqU.defeqDF` both are) *through the very hole*
`AxiomConservativityWF` is equivalent to.  So §4's route is tainted in its plumbing before its
hypothesis is even discharged, while §1's route is hole-free throughout.  A `PiInv`-free corner
cannot use route §4.

## §10 The residual, named (sharpened in §11)

The datum's general producer must live at `addIndTypesC`'s environment, not above it.  Two
candidates, and this file rules out a third:

1. **`docs/handoff-argstyped.md` §9's `TrIndDeclN` clause** — a producer on the checker side,
   staged exactly as `trCtors` is (`Verify/Environment/InductR.lean`).  §3 is the argument that it
   is not derivable from what is there, and §1 is now the transport it would compose with.
2. **A direct construction of `σ.WF`'s `val` clause** for a companion member — i.e. typing
   `R.tyVal D j` at `T.type` in the smaller environment *without* the datum.  At both witnesses
   this is `type_tac` on a concrete spine; in general it is the datum, by
   `tyVal_hasType_of_argsTypedK`, unless a route through `of_mkApp` is admitted — which the nested
   corner refuses.
3. **Ruled out: restriction as a producer** (§3), and **priced: restriction as an unconditional
   lemma** (§4).

§11 then cuts candidate 2 down to its exact size: the *only* thing the general nested transport
lacks is `VIndRestore.ValAt D K e₂ e₁` — one closed typing per companion member, at the smaller
environment — and the same clause at the *larger* environment is free.

Not touched, deliberately: `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (`docs/vacuity-ledger.md`
row 197), and the flip. -/

/-! ## §11 The general route, complete except for one closed typing per companion

§3 shows a restriction lemma cannot *produce* the datum.  What is left to ask is how much of the
general route the restriction lemma **does** buy, and the answer is: everything except one
judgement per companion member.

The substitution's `WF` has four fields.  Three are general facts about the two stagings and are
proved here (`csubstTy_WF_of_val`): closedness is `VIndRestore.csubstTy_closed`; the `const` field
is a case split on `addConstList` at `D.typeConsts` versus `D.typeConstsC K`, using §2's inclusion;
the `defeq` field is `addConstList_defeqs` plus `Ordered.noCSubstD`.  The fourth is the `val`
clause, taken as a hypothesis.

So the residual of the whole nested transport is:

> for each companion member `j`, one **closed** typing
> `e₁.HasType D.uvars [] (R.tyVal D j) T.type`,
> where `e₁ = env.addIndTypesC D K` — the companions absent.

That is sharper than `docs/handoff-argstyped.md` §8's residual in two ways: it is a *single*
judgement per member rather than a family indexed by contexts, and its subject and type are both
**companion-free and closed**, so no context, no spine and no telescope appear in it.  Note also
that the *same* judgement at the *bigger* environment `e₂` is available in general — it is
`tyVal_hasType_of_argsTypedK` applied to the `D.WF`-supplied datum (`ArgsTypedSupply.lean` §5) — so
the general nested route now hangs on **restricting one closed typing**, and on nothing else. -/

/-! `VIndRestore.csubstTy_eq_some` (`Theory/Inductive/RestoreBridge.lean`) already says a
companion member's name is in the substitution's domain, given `D.blockNames.Nodup` — which
`addIndTypes`' own success supplies (`VEnv.addConstList_fresh`).  The first draft of this section
re-derived both and collided with `csubstTy_dom`; the collision is recorded rather than quietly
fixed, since it is the class `scripts/dup-names.lean` exists for. -/

/-- `addIndTypes` succeeding means the member names are distinct. -/
theorem VInductDecl'.blockNames_nodup_of_addIndTypes {D : VInductDecl'} {env e₂ : VEnv}
    (h₂ : env.addIndTypes D = some e₂) : D.blockNames.Nodup := by
  have h := (VEnv.addConstList_fresh (cs := D.typeConsts) h₂).2
  rwa [show D.typeConsts.map (·.1) = D.blockNames from by
    simp [VInductDecl'.typeConsts, VInductDecl'.blockNames]] at h

/-- Every member type of a well-formed block mentions only constants the *pre-block* environment
declares — hence none of the companion names. -/
theorem VInductDecl'.WF.types_constsIn {D : VInductDecl'} {env : VEnv} (henv : env.Ordered)
    (hD : D.WF env) : ∀ T ∈ D.types, T.type.ConstsIn env.contains := by
  intro T hT
  obtain ⟨_, h⟩ := (hD.types T hT).isType
  exact (h.constsIn henv.constsIn trivial).1

/-- **THE GENERAL ROUTE, MODULO THE `val` CLAUSE.**  Everything the restriction needs, at the two
environments of the gap, from the `val` clause and general facts about the two stagings. -/
theorem VIndRestore.csubstTy_WF_of_val {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e₁ : VEnv} (henv : env.Ordered) (he₁ : e₁.Ordered) (hD : D.WF env)
    (hf : (R.csubstTy D K).FreshIn env) (hcl : (R.csubstTy D K).Closed)
    (h₂ : env.addIndTypes D = some e₂) (h₁ : env.addIndTypesC D K = some e₁)
    (hval : ∀ {c : Name} {t : VExpr} {ci : VConstant}, R.csubstTy D K c = some t →
      e₂.constants c = some ci → e₁.HasType ci.uvars [] t ci.type) :
    (R.csubstTy D K).WF e₂ e₁ D.uvars := by
  have htypes := hD.types_constsIn henv
  have hfree : ∀ T ∈ D.types, T.type.NoCSubst (R.csubstTy D K) :=
    fun T hT => (htypes T hT).noCSubst hf
  rw [VEnv.addIndTypes] at h₂; rw [VEnv.addIndTypesC] at h₁
  refine CSubst.WF_of_hasType he₁ hcl (fun {c t ci} hd hc => ?_) (fun {c ci} hd hc => ?_)
    (fun {df} hdf => ?_)
  · -- the `val` clause, with the declared type shown to be σ-free
    have h := hval hd hc
    by_cases hm : c ∈ (D.typeConsts.map (·.1))
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      rw [VEnv.addConstList_constants h₂ p hp] at hc
      cases hc
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 (by simpa [VInductDecl'.typeConsts] using hp)
      rwa [(hfree T hT).substC_eq]
    · rw [VEnv.addConstList_constants_of_not_mem h₂ hm] at hc
      rwa [(henv.noCSubstC hf hc).substC_eq]
  · -- the `const` clause
    by_cases hm : c ∈ (D.typeConsts.map (·.1))
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      rw [VEnv.addConstList_constants h₂ p hp] at hc
      cases hc
      obtain ⟨T, hT, hpe⟩ := List.mem_map.1 (by simpa [VInductDecl'.typeConsts] using hp)
      have hKn : T.name ∉ K := by
        intro hK
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
        rw [← hpe] at hd
        rw [VIndRestore.csubstTy_eq_some (VInductDecl'.blockNames_nodup_of_addIndTypes
          (by rwa [VEnv.addIndTypes])) hj hK] at hd
        exact absurd hd nofun
      have hmem : (T.name, (⟨D.uvars, T.type⟩ : VConstant)) ∈ D.typeConstsC K := by
        rw [VInductDecl'.typeConstsC, List.mem_filterMap]
        exact ⟨(T.name, ⟨D.uvars, T.type⟩), List.mem_map.2 ⟨T, hT, rfl⟩, by simp [hKn]⟩
      rw [← hpe]
      rw [VEnv.addConstList_constants h₁ _ hmem, (hfree T hT).substC_eq]
    · rw [VEnv.addConstList_constants_of_not_mem h₂ hm] at hc
      have hm' : c ∉ ((D.typeConstsC K).map (·.1)) := fun h => hm (by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
        exact List.mem_map.2 ⟨p, VInductDecl'.mem_typeConsts_of_mem_typeConstsC hp, rfl⟩)
      rw [VEnv.addConstList_constants_of_not_mem h₁ hm', hc,
        (henv.noCSubstC hf hc).substC_eq]
  · -- the `defeq` clause
    rw [VEnv.addConstList_defeqs h₂] at hdf
    rw [(henv.noCSubstD hf hdf).substC_eq, VEnv.addConstList_defeqs h₁]
    exact hdf

#print axioms Lean4Lean.VInductDecl'.blockNames_nodup_of_addIndTypes
#print axioms Lean4Lean.VInductDecl'.WF.types_constsIn
#print axioms Lean4Lean.VIndRestore.csubstTy_WF_of_val

/-! ### §11a The residual, named — and the same clause one environment up

`ValAt e` below is the residual of §11, as a `Prop` in its own right: one closed typing per
companion member.  Two theorems about it:

* `ArgsTypedK.restrict_of_val` — **the general route**: `ValAt e₁` transports the datum from
  `env.addIndTypes D` down to `env.addIndTypesC D K`, hence (by `mono`) into every later stage of
  `AddInductStagesR`.  Nothing else is hypothesised that the step does not already carry.
* `valAt_of_argsTypedK` — the **same clause at `e₂`** is free: it is `ArgsTypedSupply.lean` §2.1
  applied to the `D.WF`-supplied datum.  So the entire distance between what `D.WF` gives and what
  §8.7 consumes is: *this one clause, one environment lower*. -/

/-- **THE RESIDUAL.**  For every constant the restoration replaces, its value inhabits its declared
type — in the environment `e`. -/
def VIndRestore.ValAt (R : VIndRestore) (D : VInductDecl') (K : List Name) (e₂ e : VEnv) : Prop :=
  ∀ {c : Name} {t : VExpr} {ci : VConstant}, R.csubstTy D K c = some t →
    e₂.constants c = some ci → e.HasType ci.uvars [] t ci.type

/-- **THE GENERAL ROUTE, under the residual.**  Everything but `ValAt e₁` is either general
(`csubstTy_WF_of_val`, §2) or already carried by the step (`Occurs`, `RestoreData.args`). -/
theorem VInductDecl'.ArgsTypedK.restrict_of_val {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env e₂ e₁ : VEnv} {occ : Nat → VNestedOcc}
    (henv : env.Ordered) (he₁ : e₁.Ordered) (hD : D.WF env)
    (hf : (R.csubstTy D K).FreshIn env) (hcl : (R.csubstTy D K).Closed)
    (h₂ : env.addIndTypes D = some e₂) (h₁ : env.addIndTypesC D K = some e₁)
    (hval : R.ValAt D K e₂ e₁)
    (hocc : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → (occ j).Occurs env)
    (hp : ∀ B ∈ D.params.reverse, B.ConstsIn env.contains)
    (hargs : ∀ j, ∀ a ∈ (occ j).args, a.NoCSubst (R.csubstTy D K))
    (H : D.ArgsTypedK K e₂ occ) : D.ArgsTypedK K e₁ occ :=
  fun j T hT hK => (H j T hT hK).restrictC'
    (R.csubstTy_WF_of_val henv he₁ hD hf hcl h₂ h₁ hval) henv hf (hocc j T hT hK) hp (hargs j)

/-- **…and the residual is free one environment up.**  `ArgsTypedSupply.lean` §2.1 at `e₂`. -/
theorem VIndRestore.valAt_of_argsTypedK {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env e₂ e : VEnv} {occ : Nat → VNestedOcc} (hB : D.Built R K env occ)
    (hS : D.ArgsTypedK K e occ) (hle : env ≤ e)
    (hparams : OnCtx D.params.reverse (e.IsType D.uvars))
    (h₂ : env.addIndTypes D = some e₂)
    (hlvl : ∀ j, ∀ l ∈ R.tyLvls j, l.WF D.uvars) : R.ValAt D K e₂ e := by
  intro c t ci hd hc
  obtain ⟨j, T, hT, rfl, hK, rfl⟩ := VIndRestore.csubstTy_dom hd
  have hmem : (T.name, (⟨D.uvars, T.type⟩ : VConstant)) ∈ D.typeConsts :=
    List.mem_map.2 ⟨T, List.mem_of_getElem? hT, rfl⟩
  rw [VEnv.addIndTypes] at h₂
  rw [VEnv.addConstList_constants h₂ _ hmem] at hc
  cases hc
  exact tyVal_hasType_of_argsTypedK' hB hS hle hparams hT hK (hlvl j)

/-! ### §11b Collapse test: at `K = []` everything here is inert

Working rule 5, and the ledger's "a hypothesis can be inert".  With no companion members the
substitution is the identity (`VIndRestore.csubstTy_nil`), so the residual is vacuous and so is the
datum — **both sides** of the transport.  So §11's content lives entirely at `K ≠ []`, which both of
the tree's nested witnesses satisfy (`nfnK_companion`, `ntree_csubstTy_aux` upstream).  Reported
because a reduction that also holds at `K = []` for the trivial reason would grade itself
against a criterion that cannot fail. -/

theorem VIndRestore.valAt_nil {D : VInductDecl'} {R : VIndRestore} {e₂ e : VEnv} :
    R.ValAt D [] e₂ e := by
  intro c t ci hd _
  rw [VIndRestore.csubstTy_nil] at hd
  exact absurd hd (by simp [CSubst.id])

theorem VInductDecl'.argsTypedK_nil {D : VInductDecl'} {e : VEnv} {occ : Nat → VNestedOcc} :
    D.ArgsTypedK [] e occ := fun _ _ _ hK => nomatch hK

#print axioms Lean4Lean.VInductDecl'.ArgsTypedK.restrict_of_val
#print axioms Lean4Lean.VIndRestore.valAt_of_argsTypedK
#print axioms Lean4Lean.VIndRestore.valAt_nil
#print axioms Lean4Lean.VInductDecl'.argsTypedK_nil
