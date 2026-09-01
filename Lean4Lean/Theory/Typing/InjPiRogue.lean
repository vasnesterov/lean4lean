import Lean4Lean.Theory.Typing.InjPiInhab

/-!
# `ConvPiFromEntry` is not provable over `Ordered env`, and the barrier claimed against the
rogue idiom on the Π side does not exist

`Theory/Typing/InjPiInhab.lean` §7 states the Π half of `ConvStep2` with no typing judgment in
it:

    ConvPiFromEntry :  CtxStrong env U (X::Γ) →
                       ConvC env U (X::Γ) X.lift (.forallE A B) →
                       ConvC env U (X::Γ) X.lift (.forallE A' B') → ConvC env U (A::X::Γ) B B'

and `piChainAt_bvar_iff_convPiFromEntry` makes it equivalent to `PiChainAt env U (.bvar 0)` over
`Ordered env`.  Every reduction in `InjMidLocal.lean`, `InjChainLower.lean` and `InjPiInhab.lean`
carries `Ordered env` and nothing stronger.  **At that strength the statement is false**, and
this file exhibits the environment.

## Two corrections, both machine-checked here

**1. The common source is free.**  `ConvPiInvCod.convPiFromEntry` is three lines and takes *no
hypothesis at all*: `ConvC` is symmetric and transitive unconditionally (`ConvC.symm`,
`ConvC.trans`, `BaseUniqChain.lean`), so two chains out of a common source compose into one
chain between the two Π's.  So `ConvPiFromEntry` is not a weakening of `ConvPiInvCod` in that
direction, and "two chains with a **common source**" is presentation, not strength.  The other
direction is `InjPiInhab.lean`'s own §2/§7 cycle (`Ordered env` plus the `.bvar 0` inhabitant).

**2. `InjChainLower.lean`'s `[analysis]` — "no rogue-environment refutation of `SortChainAt`,
`PiChainAt`, `ConvSortInv` or `ConvPiInvCod` is available by this idiom" — does not hold up on the two
Π-side entries.**  Precisely: the *argument* given there is invalid for them, and the idiom does
reach them.  The argument is a premise count: `IsDefEqStrong.extra`
(`Theory/Typing/Strong.lean:77`) has nine premises, five of them typings, and at `rogueSortEnv`
they demand `[] ⊢ .sort .zero : .sort (.succ (.succ .zero))`, which that environment does not
contain.  That argument is sound **for sort chains only**, where the level bookkeeping
(`.sort l : .sort (.succ l)`) forces the mismatch.  It says nothing about Π chains, and on the
Π side the premises are satisfiable with no anomaly whatever: a δ-shaped rule

    C ≡ ∀ (_ : Prop), Prop        at type   Sort 1

has both sides genuinely typed at `Sort 1` in the empty context, so all nine premises hold and
`IsDefEqStrong.extra` becomes a `ConvC` link.  `rogue_link1`, `rogue_link2` and `rogue_piPi`
below are that link, twice, plus the Π/Π chain they compose to — with **syntactically distinct
codomains** (`rogue_fires`), at an environment proved `Ordered` (`ordered_roguePiEnv`).

## The environment, and what `ConvPiFromEntry` forces at it

`roguePiEnv` declares one constant `C : Sort 1` and **two** definitional equations for it:

    rogueDf1 :  C ≡ ∀ (_ : Prop), Prop                    at  Sort 1
    rogueDf2 :  C ≡ ∀ (_ : Prop), ∀ (_ : Prop), Prop      at  Sort 1

`Ordered.defeq` asks only `df.WF env` — that both sides be typed at `df.type` in the empty
context — and both rules satisfy it, so `Ordered roguePiEnv` holds (`ordered_roguePiEnv`,
`sorryAx`-free).  Instantiating `ConvPiFromEntry` at `Γ = []`, `X = C` (so `X.lift = X`, `C`
being closed) with the two links as the two chains gives, by `convPiFromEntry_forces`:

    ConvC roguePiEnv 0 [Prop, C] Prop (∀ (_ : Prop), Prop)

i.e. `ConvPiFromEntry` at `roguePiEnv` forces a **sort/Π** conversion.  So:

    not_convPiFromEntry_of_convSortPiDisj :
      ConvSortPiDisj roguePiEnv 0 → ¬ ConvPiFromEntry roguePiEnv 0

and the same for `ConvPiInvCod`, `ConvPiInvCodInhab` and `PiChainAt … (.bvar 0)`.
`ConvSortPiDisj` is the `ConvC` form of `RigidSortPiDisj` = `IsDefEqU.sort_forallE_inv`, and
`SortPiDisjRaw.convSortPiDisj` derives it from the reference's typing-free judgment through
`InjMidLocal.ConvC.eq_or_raw` (unconditional).

**Read the bound honestly.**  This is not a completed refutation: `ConvSortPiDisj roguePiEnv 0`
is *not* proved here, and it cannot be, for a reason worth recording — see §"Why no refutation
is constructible" below.  What is proved is that the Π-side residual at `Ordered` strength is at
most **one instance of the other hole's one semantically-live conjunct** away from being false.
`RigidSortPiDisj` is not a part of `ConvPiFromEntry`; it is conjunct 3 of the five that
`RigidNodeCircle.rigidShapeUniqNS_iff_family` decomposes `WF.rigidShapeUniqNS` into, and
`InjSortPiModel.interp_sort_ne_interp_forallE` proves its *semantic* residual outright (the
packaging is what collapses there, not the content).  Nobody in this development doubts sort/Π
disjointness at a two-rule environment with no sort on either side of either rule.  So the
operational conclusion is not conditional:

> **Stop pointing proof attempts at `ConvPiFromEntry` over `Ordered env`.**  Any proof must
> consume `VEnv.WF`, and §7 names exactly which clause of it: `VEnv.RuleShape.delta` pins a
> δ-rule's lhs to `.const ci.name _` and `VEnv.addConst` refuses a duplicate name, so a
> `VEnv.WF` environment cannot carry **two** δ-rules for one constant.  `Ordered` can, and that
> is the only thing `roguePiEnv` needs.

## Why no refutation is constructible in this tree

Refuting `ConvPiFromEntry` at *any* environment requires exhibiting a pair of terms that are
**not** `ConvC`-linked, and this tree proves no such fact without `sorryAx`.  Checked, not
assumed:

* the non-derivability *statements* about unbounded conversion in `Theory/` are the three
  negative conjuncts of `WF.rigidShapeUniqNS` (`RigidSortPiDisj`, `RigidConstPiDisj`,
  `RigidConstSortDisj`) and `DefInvRefute`/`UniqueTypingN`'s `SortForallEDisjN`; **all are
  open**, and `InjSortPiModel.lean` items 2–3 record that the model route to them is circular
  (`RigidSortPiDisj`) or refuted (`RigidConstPiDisj`, `RigidConstSortDisj`).
  `StrengthenAudit.no_neutral_proofIrrel` is the one *inhabited* `¬ IsDefEqU` in the tree and it
  is built from `IsDefEqU.sort_forallE_inv`, i.e. from the hole;
* `Theory/Consistency.lean` states consistency **without proof**, and `Theory/SetModel/` carries
  `sorry` in nine files (`Interp.lean`, `InterpSound.lean`, `SoundInduction.lean`, …), so the
  semantic route cannot supply one either;
* the tree has exactly **two** techniques that do prove a conversion absent, and neither
  applies.  (i) `IsDefEq.closedN`, the scope invariant, used by
  `ConstVar.cvarMain_needs_entries`: useless here, because `B` and `B'` live in contexts of
  **equal length** (`A::X::Γ` and `A'::X::Γ`), so neither is out of scope for the other's
  context.  (ii) inversion at a *bounded* alternation index, used by
  `SubstCRefute.inst_does_not_preserve_index` (`¬ IsDefEqN 1 1 …`, via its `stuck` lemma) and by
  `DefInvRefute.sortForallEDisjN_zero` (index 0, free for every environment): useless here,
  because a `ConvC` chain carries no index bound at all — its links stratify to `IsDefEqN U nᵢ`
  at unrelated `nᵢ`, and covering every `nᵢ` **is** the open `SortForallEDisjN` hypothesis.

Any other separation must survive `IsDefEqStrong.beta`, which can turn an application into a Π
(`.app (.lam _ (.bvar 0)) (∀ (_ : Prop), Prop) ≡ ∀ (_ : Prop), Prop`), so a head- or
occurrence-counting invariant cannot be β-stable: separating two terms here is a normalisation
or model obligation, not a syntactic one.  That is why the residual is left named.

## Axioms and cone

`#print axioms` block at the end: every declaration is `sorryAx`-free; `Classical.choice` appears
nowhere.  The import closure is `InjPiInhab.lean`'s — `UniqueTyping.lean`, `ChurchRosser.lean`
and `Strengthen.lean` absent — so `IsDefEqU.sort_inv`, `WF.sortUniq'`, `IsDefEq.uniq`,
`IsDefEqU.trans` and `NormalEq.descend` are not consumed and not present.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 The common source is free -/

theorem ConvPiInvCod.convPiFromEntry (h : ConvPiInvCod env U) : ConvPiFromEntry env U :=
  fun hΓ h1 h2 => h hΓ (h1.symm.trans h2)

/-! ## §2 The rogue Π environment -/

def rogueC : Lean.Name := `Lean4Lean.roguePiConst

def roguePiCi : VConstant := ⟨0, .sort (.succ .zero)⟩

/-- `∀ (_ : Prop), Prop` -/
def roguePi1 : VExpr := .forallE (.sort .zero) (.sort .zero)
/-- `∀ (_ : Prop), ∀ (_ : Prop), Prop` -/
def roguePi2 : VExpr := .forallE (.sort .zero) roguePi1

def rogueDf1 : VDefEq := ⟨0, .const rogueC [], roguePi1, .sort (.succ .zero)⟩
def rogueDf2 : VDefEq := ⟨0, .const rogueC [], roguePi2, .sort (.succ .zero)⟩

def rogueEnv1 : VEnv where
  constants n := if rogueC = n then some roguePiCi else none
  defeqs _ := False

def roguePiEnv : VEnv := (rogueEnv1.addDefEq rogueDf1).addDefEq rogueDf2

theorem roguePropType {Γ : List VExpr} :
    env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := .sortDF trivial trivial rfl

theorem rogueSort1Type {Γ : List VExpr} :
    env.HasType U Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sortDF (by exact trivial) (by exact trivial) rfl

theorem rogue_imax_one_one : VLevel.imax (.succ .zero) (.succ .zero) ≈ (.succ .zero : VLevel) := by
  simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]

theorem roguePi1_type {Γ : List VExpr} :
    env.HasType U Γ roguePi1 (.sort (.succ .zero)) :=
  .defeqDF (.sortDF (by exact ⟨trivial, trivial⟩) trivial rogue_imax_one_one)
    (.forallEDF roguePropType roguePropType)

theorem roguePi2_type {Γ : List VExpr} :
    env.HasType U Γ roguePi2 (.sort (.succ .zero)) :=
  .defeqDF (.sortDF (by exact ⟨trivial, trivial⟩) trivial rogue_imax_one_one)
    (.forallEDF roguePropType roguePi1_type)

theorem rogueC_type {Γ : List VExpr} (h : env.constants rogueC = some roguePiCi) :
    env.HasType U Γ (.const rogueC []) (.sort (.succ .zero)) := by
  have := IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) (ls := []) (ls' := [])
    h (by simp) (by simp) rfl (by simp)
  exact by simpa [roguePiCi, VExpr.instL, VLevel.inst, VEnv.HasType] using this

/-! ## §3 `roguePiEnv` is `Ordered` -/

theorem rogueEnv1_constants : rogueEnv1.constants rogueC = some roguePiCi := by simp [rogueEnv1]

theorem roguePiEnv_constants : roguePiEnv.constants rogueC = some roguePiCi := rogueEnv1_constants

theorem roguePiEnv_defeqs1 : roguePiEnv.defeqs rogueDf1 := by
  simp [roguePiEnv, VEnv.addDefEq, rogueEnv1]

theorem roguePiEnv_defeqs2 : roguePiEnv.defeqs rogueDf2 := by
  simp [roguePiEnv, VEnv.addDefEq, rogueEnv1]

theorem addConst_rogueEnv1 : VEnv.empty.addConst rogueC roguePiCi = some rogueEnv1 := by
  simp [VEnv.addConst, VEnv.empty, rogueEnv1]

theorem ordered_rogueEnv1 : Ordered rogueEnv1 :=
  .const .empty ⟨_, rogueSort1Type⟩ addConst_rogueEnv1

theorem ordered_roguePiEnv : Ordered roguePiEnv :=
  .defeq (.defeq ordered_rogueEnv1 ⟨rogueC_type rogueEnv1_constants, roguePi1_type⟩)
    ⟨rogueC_type rogueEnv1_constants, roguePi2_type⟩

/-! ## §4 Two `ConvC` links out of one source, at an `Ordered` environment -/

theorem rogue_onCtx : OnCtx [VExpr.const rogueC []] (roguePiEnv.IsType 0) :=
  ⟨trivial, _, rogueC_type roguePiEnv_constants⟩

theorem rogue_ctxStrong : CtxStrong roguePiEnv 0 [VExpr.const rogueC []] :=
  .strong ordered_roguePiEnv rogue_onCtx

theorem rogue_link1 :
    ConvC roguePiEnv 0 [VExpr.const rogueC []] (VExpr.const rogueC []) roguePi1 := by
  have h := IsDefEq.extra (env := roguePiEnv) (uvars := 0) (Γ := [VExpr.const rogueC []])
    (ls := []) (df := rogueDf1) roguePiEnv_defeqs1 (by simp) rfl
  simp [rogueDf1, roguePi1, VExpr.instL, VLevel.inst] at h
  exact .one (h.strong ordered_roguePiEnv rogue_onCtx)

theorem rogue_link2 :
    ConvC roguePiEnv 0 [VExpr.const rogueC []] (VExpr.const rogueC []) roguePi2 := by
  have h := IsDefEq.extra (env := roguePiEnv) (uvars := 0) (Γ := [VExpr.const rogueC []])
    (ls := []) (df := rogueDf2) roguePiEnv_defeqs2 (by simp) rfl
  simp [rogueDf2, roguePi2, roguePi1, VExpr.instL, VLevel.inst] at h
  exact .one (h.strong ordered_roguePiEnv rogue_onCtx)

/-! ## §5 What `ConvPiFromEntry` forces at `roguePiEnv` -/

/-- The two Π-shapes are chain-linked at an `Ordered` environment, with **syntactically
distinct codomains** — `ConvPiInvCod`'s premise, fired by the rogue idiom. -/
theorem rogue_piPi : ConvC roguePiEnv 0 [VExpr.const rogueC []] roguePi1 roguePi2 :=
  rogue_link1.symm.trans rogue_link2

theorem rogue_cod_ne : (VExpr.sort .zero) ≠ roguePi1 := by simp [roguePi1]

theorem rogue_lift : (VExpr.const rogueC []).lift = VExpr.const rogueC [] := rfl

/-- **The forcing theorem.**  `ConvPiFromEntry` at `roguePiEnv` — an `Ordered` environment —
forces the closed conversion `Prop ≡ ∀ (_ : Prop), Prop`. -/
theorem convPiFromEntry_forces (h : ConvPiFromEntry roguePiEnv 0) :
    ConvC roguePiEnv 0 [VExpr.sort .zero, VExpr.const rogueC []] (.sort .zero) roguePi1 :=
  h (Γ := []) (X := .const rogueC []) (A := .sort .zero) (B := .sort .zero)
    (A' := .sort .zero) (B' := roguePi1) rogue_ctxStrong
    (by rw [rogue_lift]; exact rogue_link1) (by rw [rogue_lift]; exact rogue_link2)

/-- The separation fact the refutation needs, named. -/
def RoguePiSep : Prop :=
  ¬ ConvC roguePiEnv 0 [VExpr.sort .zero, VExpr.const rogueC []] (.sort .zero) roguePi1

theorem not_convPiFromEntry_of_sep (h : RoguePiSep) : ¬ ConvPiFromEntry roguePiEnv 0 :=
  fun H => h (convPiFromEntry_forces H)

theorem not_convPiInvCod_of_sep (h : RoguePiSep) : ¬ ConvPiInvCod roguePiEnv 0 :=
  fun H => not_convPiFromEntry_of_sep h H.convPiFromEntry

theorem not_piChainAt_bvar_of_sep (h : RoguePiSep) : ¬ PiChainAt roguePiEnv 0 (.bvar 0) :=
  fun H => not_convPiFromEntry_of_sep h (convPiFromEntry_of_piChainAt_bvar ordered_roguePiEnv H)

theorem not_convPiInvCodInhab_of_sep (h : RoguePiSep) : ¬ ConvPiInvCodInhab roguePiEnv 0 :=
  fun H => not_piChainAt_bvar_of_sep h (piChainAt_of_convPiInvCodInhab H baseUniqCAt_bvar)

/-! ## §6 The residual, named and bounded -/

/-- **Sort/Π disjointness along a chain** — the `ConvC` form of `RigidSortPiDisj`
(`IsDefEqU.sort_forallE_inv`), the one conjunct of `WF.rigidShapeUniqNS` whose *semantic*
residual is a theorem (`InjSortPiModel.interp_sort_ne_interp_forallE`). -/
def ConvSortPiDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u : VLevel} {A B : VExpr}, ¬ ConvC env U Γ (.sort u) (.forallE A B)

/-- The same over the reference's typing-free judgment (`RawDefEq.lean`). -/
def SortPiDisjRaw (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u : VLevel} {A B : VExpr}, ¬ env.IsDefEqRaw U Γ (.sort u) (.forallE A B)

theorem SortPiDisjRaw.convSortPiDisj (h : SortPiDisjRaw env U) : ConvSortPiDisj env U := by
  intro Γ u A B hc
  match hc.eq_or_raw with
  | .inl e => exact absurd e (by simp)
  | .inr r => exact h r

/-- **`ConvPiFromEntry` is FALSE at an `Ordered` environment, modulo sort/Π disjointness at
that environment.**  Nothing here proves `ConvSortPiDisj roguePiEnv 0`; it is the residual, and
it is *not* part of `ConvPiFromEntry` — it is a conjunct of the other hole. -/
theorem not_convPiFromEntry_of_convSortPiDisj (h : ConvSortPiDisj roguePiEnv 0) :
    ¬ ConvPiFromEntry roguePiEnv 0 := fun H => h (convPiFromEntry_forces H)

theorem not_convPiFromEntry_of_sortPiDisjRaw (h : SortPiDisjRaw roguePiEnv 0) :
    ¬ ConvPiFromEntry roguePiEnv 0 := not_convPiFromEntry_of_convSortPiDisj h.convSortPiDisj

theorem not_convPiInvCod_of_convSortPiDisj (h : ConvSortPiDisj roguePiEnv 0) :
    ¬ ConvPiInvCod roguePiEnv 0 :=
  fun H => not_convPiFromEntry_of_convSortPiDisj h H.convPiFromEntry

theorem not_piChainAt_bvar_of_convSortPiDisj (h : ConvSortPiDisj roguePiEnv 0) :
    ¬ PiChainAt roguePiEnv 0 (.bvar 0) :=
  fun H => not_convPiFromEntry_of_convSortPiDisj h
    (convPiFromEntry_of_piChainAt_bvar ordered_roguePiEnv H)

theorem not_convPiInvCodInhab_of_convSortPiDisj (h : ConvSortPiDisj roguePiEnv 0) :
    ¬ ConvPiInvCodInhab roguePiEnv 0 :=
  fun H => not_piChainAt_bvar_of_convSortPiDisj h (piChainAt_of_convPiInvCodInhab H baseUniqCAt_bvar)

/-! ## §7 What separates `Ordered` from `VEnv.WF` here, exactly -/

/-- **The two rogue rules share a left-hand side.**  `VEnv.RuleShape.delta`
(`PatternRules.lean`) pins a δ-rule's lhs to `.const ci.name _`, and `VEnv.addConst` refuses a
name it already holds, so a `VEnv.WF` environment cannot carry two δ-rules for one constant.
`Ordered` has no such clause — `Ordered.defeq` asks only `df.WF env`, which both rules satisfy
(`ordered_roguePiEnv`).  That single missing clause is what makes `roguePiEnv` possible, and it
is therefore the hypothesis a confluence development aimed at `ConvPiFromEntry` has to consume.
(The "at most one δ-rule per constant" half is `[analysis]`: it is a statement about the
declaration history `VEnv.WF'`, not machine-checked here.) -/
theorem rogue_rules_share_lhs : rogueDf1.lhs = rogueDf2.lhs ∧ rogueDf1 ≠ rogueDf2 := by
  refine ⟨rfl, ?_⟩
  intro h; rw [rogueDf1, rogueDf2] at h; injection h with _ _ h; simp [roguePi1, roguePi2] at h

/-- Non-vacuity: `ConvPiInvCod`'s premise fires at `roguePiEnv` with the two codomains
syntactically distinct, so §6 is not about an empty set of instances.  (Firing a premise is not
evidence that the hypothesis is satisfiable.) -/
theorem rogue_fires : ConvC roguePiEnv 0 [VExpr.const rogueC []] roguePi1 roguePi2 ∧
    (VExpr.sort .zero : VExpr) ≠ roguePi1 := ⟨rogue_piPi, rogue_cod_ne⟩

end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.ConvPiInvCod.convPiFromEntry
#print axioms Lean4Lean.VEnv.ordered_roguePiEnv
#print axioms Lean4Lean.VEnv.rogue_link1
#print axioms Lean4Lean.VEnv.rogue_link2
#print axioms Lean4Lean.VEnv.rogue_piPi
#print axioms Lean4Lean.VEnv.convPiFromEntry_forces
#print axioms Lean4Lean.VEnv.not_convPiFromEntry_of_sep
#print axioms Lean4Lean.VEnv.not_convPiInvCod_of_sep
#print axioms Lean4Lean.VEnv.not_piChainAt_bvar_of_sep
#print axioms Lean4Lean.VEnv.not_convPiInvCodInhab_of_sep
#print axioms Lean4Lean.VEnv.SortPiDisjRaw.convSortPiDisj
#print axioms Lean4Lean.VEnv.not_convPiFromEntry_of_convSortPiDisj
#print axioms Lean4Lean.VEnv.not_convPiFromEntry_of_sortPiDisjRaw
#print axioms Lean4Lean.VEnv.not_convPiInvCod_of_convSortPiDisj
#print axioms Lean4Lean.VEnv.not_piChainAt_bvar_of_convSortPiDisj
#print axioms Lean4Lean.VEnv.not_convPiInvCodInhab_of_convSortPiDisj
#print axioms Lean4Lean.VEnv.rogue_rules_share_lhs
#print axioms Lean4Lean.VEnv.rogue_fires
end Audit
