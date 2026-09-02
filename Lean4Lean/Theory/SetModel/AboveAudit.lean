import Lean4Lean.Theory.SetModel.InaccChainOmega
import Lean4Lean.Theory.SetModel.InductOracleWitness
import Lean4Lean.Theory.SetModel.CoherentConstShape
import Lean4Lean.Theory.SetModel.StableAudit

/-!
# `Above` audited: where the wrapper can hide a vacuity, and where it provably cannot

`Above M P := ∃ m, IsInaccessibleChain m M.κ → P` (`InterpSound.lean:696`) is trivially
true at any `M.κ` that is not an inaccessible chain of every finite length, so **every**
`Above M P` — `P := False` included — holds at such a `κ`.  §1 witnesses this
*unconditionally*: `κ := fun _ ↦ ∅` fails already at length **one**, because
`IsInaccessible` demands `ω ∈ κ i`.  (`InaccChainOmega.not_isInaccessibleChain_const` is
the length-two version, but it needs an inaccessible to *exist* in order to exhibit a bad
`κ`; `above_false_zeroChain` needs nothing.)

Every field of `CoherentOn`, `OracleOK`, `QuotOracleOK`, `InductOracleOK` and `DefEqOK` is
an `Above`.  So the question this file answers is: **which positive bounds in
`Theory/SetModel/` are weakened by that?**

## The answer, and the correction it carries

*Being stated at an arbitrary `κ` is not a defect.*  "Arbitrary" means universally
quantified, and §2 shows a universally-quantified-`κ` `Above` claim is **exactly as strong
as the unwrapped claim** at the one `κ` the reduction uses: instantiate at
`InaccChainOmega.omegaChain V` and `CoherentConstShape.above_iff_of_chain` strips the
wrapper (`above_omegaChain_iff`).  The pattern that *would* be worthless is a claim that
**chooses** its own `κ` — `∃ κ, Above ⟨κ, …⟩ P` with no chain condition attached, or a
claim at a fixed `κ` not known to be a chain.  There is no such claim in the directory;
the only two `∃ κ` statements about chains (`Inaccessible.lean:200`,
`InaccChainOmega.lean:212, :270`) carry `IsInaccessibleChain` in the existential body.

Stronger still, and the point for the *single remaining* model-side input: the top-level
input `ModelFitsVacuous.ModelFitsLeanInput` takes `hκ : ∀ m, IsInaccessibleChain m κ` as a
hypothesis.  So §3's `iff`s apply inside it verbatim, and `ModelFitsLeanInput` is
**equivalent** to its wrapper-free form.  The `Above` wrapper therefore weakens nothing at
or below `ModelFits`; it can only weaken intermediate bounds that are stated without `hκ`
in scope — and §4 is the enumeration of those, with each one's route recorded.

## §4: the audit, verbatim

Positive / satisfiability bounds in `Theory/SetModel/` touching an `Above`-wrapped field:

| claim | file:line | route through the wrapper | verdict |
|---|---|---|---|
| `oracleOK_of` | `Cnst.lean:418` | `Above.pure` on both fields | sound — a constructor *from* unwrapped data |
| `oracleOK_prop` | `Cnst.lean:451` | via `oracleOK_of` | sound |
| `oracleOK_above` | `Cnst.lean:438` | identity (`Above` in, `Above` out) | asserts nothing; not a bound |
| `coherentOn_witness` | `CoherentWitness.lean:72` | all four fields `Above.pure` | sound (but at an unvisited env — trap, unrelated) |
| `coherentOn_propAx` | `CoherentConstShape.lean:193` | `Above.pure` | sound |
| `coherentOn_typeAx` | `CoherentConstShape.lean:208` | `const_type` = `⟨1, fun hκ ↦ …⟩` | wrapper **used**, non-vacuously: `typeAx_const_type_unwrapped` (`:220`) is the stripped form given `IsInaccessibleChain 1 κ` |
| `oracleOK_univ` | `CoherentConstShape.lean:312` | `type` = `⟨1, fun hκ ↦ …⟩` | same threshold, same companion |
| `coherent_const_denot_eq_sort` / `_forallE` | `:285` / `:295` | via the two above | sound |
| `coherentOn_axEnv_separates` | `:342` | via the two above | sound |
| `inductOracleOK_empty` | `CnstRecursion.lean:773` | no `Above` reached (both lists empty) | sound; vacuous for a *disclosed* different reason |
| `quotDefEq_ok` | `QuotInterp.lean:3321` | both `Above.pure` | sound |
| `oracleOK_zero_of_ext`, `oracleOK_zero_extAx`, `inductOracleOK_consts_zero` | `InductOracleWitness.lean:198, :207, :219` | via `oracleOK_of` | sound |
| `inductOracleOK_rules_zero` | `:229` | `Above.pure` ×2 | sound |
| `inductOracleOK_zero`, `oracleFits_zero` | `:259`, `:265` | from the above; stripped companions `mem_interp_consts_zero` (`:350`), `defEq_rules_zero` (`:362`) | sound, and independently restated |
| `coherentOn_zero` | `:295` | conclusion `CoherentOn`, i.e. wrapped; provenance entirely `Above.pure` | the **one** entry with no stripped restatement — supplied here as `coherentOn'_zero` (§3) |
| `axiomsValidated_of_coherentOn` | `AxiomsValidatedAudit.lean:78` | consumes `hκ`, strips | sound |
| `axiomsValidated_of_coherentOn_omega` / `_chain` | `InaccChainOmega.lean:265` / `:278` | strips at `omegaChain` | sound |
| `falseProp_above_false` | `FalseProp.lean:157` | conclusion `Above M False` | honest: the consumer (`consistent_of`) supplies `hκ` |
| `soundAbove` / `sound_nil` | `SoundInduction.lean:199`, `:394` | *produces* an `Above` with a threshold read off the derivation — the wrapper's intended use | sound at arbitrary `κ`; collapsible at `omegaChain` by §2 |
| `coherentOn_defConst`, `coherentOn_defEq` | `Cnst.lean:74`, `:99` | `Above.imp (sound_nil …)` for the sort-side fields, `Above.pure` for the equation | sound — inherits `soundAbove`'s threshold |
| `coherentOn_addConst`/`addDefEq`/`addConstList`/`addConstList'`/`addDefEqFold`/`addInduct`/`cnstOf`, `axiomsValidatedAbove_of_coherentOn`, `coherentOn_boxDecl_history_of`, `oracleFits_boxDecl_iff` | `InterpSound.lean:911, :960`; `Cnst.lean:189, :264`; `CnstRecursion.lean:205, :552`; `IndInterp.lean:1803`; `AxiomsValidatedAudit.lean:69`; `InductOracleAudit.lean:280, :291` | `Above` in, `Above` out | step lemmas; assert no satisfiability |

**No worthless entry.**  Every positive bound either goes through `Above.pure` or names its
threshold and uses it, and the one whose conclusion had no stripped restatement gets one
below.  `QuotOracleOK` is never inhabited anywhere (only `quotDefEq_ok` covers its `rule`
field), so it contributes no row.

Negative results are *not* at risk and are not listed: refuting `Above M P` requires
`∀ m, IsInaccessibleChain m M.κ ∧ ¬P`, which is strictly harder than refuting `P`.  That
asymmetry is why `not_oracleOK_falseProp` and `not_coherentOn_falseProp` take `hκ` and
`not_axiomsValidated_falseProp` does not.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## 1. The vacuity, unconditionally

No large-cardinal hypothesis is needed to exhibit a `κ` at which `Above` collapses: `∅`
is not inaccessible, so the constantly-`∅` chain fails at length one. -/

section Vacuity

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- `∅` is not inaccessible: `IsInaccessible` demands `ω ∈ k`. -/
theorem not_isInaccessible_empty : ¬ IsInaccessible (∅ : V) :=
  fun h ↦ not_mem_empty h.omega_mem

/-- **A bad `κ` with no hypotheses at all**, and bad already at length one — unlike
`InaccChainOmega.not_isInaccessibleChain_const`, which needs an inaccessible to exist in
order to name one. -/
theorem not_isInaccessibleChain_one_zero :
    ¬ IsInaccessibleChain 1 (fun _ ↦ (∅ : V)) :=
  fun h ↦ not_isInaccessible_empty (h.inaccessible 0 Nat.one_pos)

/-- **`Above` is trivially true below a failing threshold**, for every `P`. -/
theorem above_of_not_chain {M : ModelData V} {m : ℕ} (h : ¬ IsInaccessibleChain m M.κ)
    (P : Prop) : Above M P :=
  ⟨m, fun hc ↦ absurd hc h⟩

/-- **The wrapper alone proves `False` at a bad `κ`.**  So no `Above`-wrapped statement is
information about a `κ` that is not constrained to be a chain. -/
theorem above_false_zeroChain (ls : List ℕ) (c : Name → List VLevel → V) :
    Above (V := V) ⟨fun _ ↦ ∅, ls, c⟩ False :=
  above_of_not_chain (m := 1) not_isInaccessibleChain_one_zero _

end Vacuity

/-! ## 2. …and the repair: an arbitrary `κ` is *not* a bad `κ`

A claim quantified over all `κ` may be instantiated at `omegaChain V`, where
`above_iff_of_chain` strips the wrapper.  This is what makes "stated at an arbitrary `κ`
through the wrapper" a sound form rather than a worthless one. -/

section Omega

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]

/-- **At the chain `InaccChainOmega.lean` builds, `Above` is the identity.** -/
theorem above_omegaChain_iff {ls : List ℕ} {c : Name → List VLevel → V} {P : Prop} :
    Above (V := V) ⟨omegaChain V, ls, c⟩ P ↔ P :=
  above_iff_of_chain (M := (⟨omegaChain V, ls, c⟩ : ModelData V))
    omegaChain_isInaccessibleChain

/-- **The transport, in the form the audit uses**: a `κ`-universal `Above` claim yields its
payload outright at `omegaChain V`.  `Q` is allowed to depend on `κ`, which it must — the
assignment the recursion produces is `cnstOf L κ ls o ds`. -/
theorem payload_omegaChain_of_forall {ls : List ℕ} {cf : (ℕ → V) → Name → List VLevel → V}
    {Q : (ℕ → V) → Prop} (h : ∀ κ : ℕ → V, Above (V := V) ⟨κ, ls, cf κ⟩ (Q κ)) :
    Q (omegaChain V) :=
  above_omegaChain_iff.1 (h (omegaChain V))

end Omega

/-! ## 3. The obligations with the wrapper stripped

Under `hκ` — which `ModelFitsLeanInput` supplies as a hypothesis and `omegaChain` supplies
outright — each residual is *equivalent* to its wrapper-free form.  So the wrapper is not
a weakening of the specification anywhere at or below `ModelFits`. -/

section Strip

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {κ : ℕ → V} {ls : List ℕ}

/-- `OracleOK` with both `Above`s removed. -/
def OracleOKRaw (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o c : Name → List VLevel → V) (n : Name) (ci : VConstant) : Prop :=
  (∀ us us' : List VLevel, (∀ l ∈ us, l.WF nv) → (∀ l ∈ us', l.WF nv) →
      List.Forall₂ (· ≈ ·) us us' → o n us = o n us') ∧
    (∀ us : List VLevel, (∀ l ∈ us, l.WF nv) → us.length = ci.uvars →
      o n us ∈ (interp (⟨κ, ls, c⟩ : ModelData V) L [] (ci.type.instL us)).toFun ∅)

/-- `DefEqOK` with both `Above`s removed. -/
def DefEqOKRaw (L : PropSplit envF nv) (M : ModelData V) (df : VDefEq) : Prop :=
  ∀ us : List VLevel, (∀ l ∈ us, l.WF nv) → us.length = df.uvars →
    (interp M L [] (df.lhs.instL us)).toFun ∅ = (interp M L [] (df.rhs.instL us)).toFun ∅ ∧
      (interp M L [] (df.lhs.instL us)).toFun ∅
        ∈ (interp M L [] (df.type.instL us)).toFun ∅

/-- `CoherentOn` with all four `Above`s removed. -/
structure CoherentOn' {envF : VEnv} {nv : ℕ} (M : ModelData V) (L : PropSplit envF nv)
    (env : VEnv) : Prop where
  const_congr : ∀ (c : Name) (ls ls' : List VLevel), (∀ l ∈ ls, l.WF nv) →
    (∀ l ∈ ls', l.WF nv) → List.Forall₂ (· ≈ ·) ls ls' → M.cnst c ls = M.cnst c ls'
  const_type : ∀ (c : Name) (ci : VConstant) (ls : List VLevel),
    env.constants c = some ci → (∀ l ∈ ls, l.WF nv) → ls.length = ci.uvars →
      M.cnst c ls ∈ (interp M L [] (ci.type.instL ls)).toFun ∅
  defeq : ∀ (df : VDefEq) (ls : List VLevel), env.defeqs df → (∀ l ∈ ls, l.WF nv) →
    ls.length = df.uvars →
      (interp M L [] (df.lhs.instL ls)).toFun ∅ = (interp M L [] (df.rhs.instL ls)).toFun ∅
  defeq_type : ∀ (df : VDefEq) (ls : List VLevel), env.defeqs df → (∀ l ∈ ls, l.WF nv) →
    ls.length = df.uvars →
      (interp M L [] (df.lhs.instL ls)).toFun ∅ ∈ (interp M L [] (df.type.instL ls)).toFun ∅

variable (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)

include hκ

/-- **The oracle's obligation is unchanged by the wrapper**, given a chain of every
length. -/
theorem oracleOK_iff_of_chain (L : PropSplit envF nv) (o c : Name → List VLevel → V)
    (n : Name) (ci : VConstant) :
    OracleOK L κ ls o c n ci ↔ OracleOKRaw L κ ls o c n ci := by
  have hA : ∀ P : Prop, Above (V := V) ⟨κ, ls, c⟩ P ↔ P :=
    fun _ ↦ above_iff_of_chain (M := (⟨κ, ls, c⟩ : ModelData V)) hκ
  constructor
  · exact fun h ↦ ⟨fun _ _ hw hw' hd ↦ (hA _).1 (h.congr hw hw' hd),
      fun _ hw hl ↦ (hA _).1 (h.type hw hl)⟩
  · exact fun h ↦ ⟨fun {_ _} hw hw' hd ↦ (hA _).2 (h.1 _ _ hw hw' hd),
      fun {_} hw hl ↦ (hA _).2 (h.2 _ hw hl)⟩

/-- The same for a defining equation. -/
theorem defEqOK_iff_of_chain (L : PropSplit envF nv) (c : Name → List VLevel → V)
    (df : VDefEq) :
    DefEqOK L (⟨κ, ls, c⟩ : ModelData V) df ↔ DefEqOKRaw L (⟨κ, ls, c⟩ : ModelData V) df := by
  have hA : ∀ P : Prop, Above (V := V) ⟨κ, ls, c⟩ P ↔ P :=
    fun _ ↦ above_iff_of_chain (M := (⟨κ, ls, c⟩ : ModelData V)) hκ
  constructor
  · exact fun h _ hw hl ↦ ⟨(hA _).1 (h hw hl).1, (hA _).1 (h hw hl).2⟩
  · exact fun h {_} hw hl ↦ ⟨(hA _).2 (h _ hw hl).1, (hA _).2 (h _ hw hl).2⟩

/-- **The `.induct` residual, wrapper-free.**  This is the honest statement of what is open:
every declared constant of the block is inhabited and every ι-rule holds, with no threshold
anywhere. -/
theorem inductOracleOK_iff_of_chain (L : PropSplit envF nv) (o c : Name → List VLevel → V)
    (D : VInductDecl') :
    InductOracleOK L κ ls o c D ↔
      ((∀ p ∈ D.allConsts, OracleOKRaw L κ ls o c p.1 p.2) ∧
        ∀ df ∈ D.iotaRules, DefEqOKRaw L (⟨κ, ls, c⟩ : ModelData V) df) := by
  constructor
  · exact fun h ↦ ⟨fun p hp ↦ (oracleOK_iff_of_chain hκ L o c p.1 p.2).1 (h.consts p hp),
      fun df hdf ↦ (defEqOK_iff_of_chain hκ L c df).1 (h.rules df hdf)⟩
  · exact fun h ↦ ⟨fun p hp ↦ (oracleOK_iff_of_chain hκ L o c p.1 p.2).2 (h.1 p hp),
      fun df hdf ↦ (defEqOK_iff_of_chain hκ L c df).2 (h.2 df hdf)⟩

/-- **And coherence itself.**  `CoherentOn` and `CoherentOn'` agree at a chain-carrying
`κ`, so no `CoherentOn` in the tree is weaker than it reads. -/
theorem coherentOn_iff_of_chain (L : PropSplit envF nv) (c : Name → List VLevel → V)
    (env : VEnv) :
    CoherentOn (⟨κ, ls, c⟩ : ModelData V) L env ↔
      CoherentOn' (⟨κ, ls, c⟩ : ModelData V) L env := by
  have hA : ∀ P : Prop, Above (V := V) ⟨κ, ls, c⟩ P ↔ P :=
    fun _ ↦ above_iff_of_chain (M := (⟨κ, ls, c⟩ : ModelData V)) hκ
  constructor
  · exact fun h ↦
      ⟨fun _ _ _ hw hw' hd ↦ (hA _).1 (h.const_congr hw hw' hd),
       fun _ _ _ hc hw hl ↦ (hA _).1 (h.const_type hc hw hl),
       fun _ _ hd hw hl ↦ (hA _).1 (h.defeq hd hw hl),
       fun _ _ hd hw hl ↦ (hA _).1 (h.defeq_type hd hw hl)⟩
  · exact fun h ↦
      ⟨fun {_ _ _} hw hw' hd ↦ (hA _).2 (h.const_congr _ _ _ hw hw' hd),
       fun {_ _ _} hc hw hl ↦ (hA _).2 (h.const_type _ _ _ hc hw hl),
       fun {_ _} hd hw hl ↦ (hA _).2 (h.defeq _ _ hd hw hl),
       fun {_ _} hd hw hl ↦ (hA _).2 (h.defeq_type _ _ hd hw hl)⟩

end Strip

/-! ## 4. The one row of the table that lacked a stripped restatement

`InductOracleWitness.coherentOn_zero` concludes `CoherentOn`, i.e. four `Above`s.  Its
provenance is entirely `Above.pure` (`inductOracleOK_zero`, `oracleOK_zero_extAx`), so
nothing was hidden — but the *statement* was not independently checkable in the way
`mem_interp_consts_zero` and `defEq_rules_zero` make the residual's two fields checkable.
This is that check: the same conclusion, wrapper-free, at `omegaChain V`. -/

section ZeroUnwrapped

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]
variable {envF : VEnv} {nv : ℕ} {ls : List ℕ}

open SetModelAudit

/-- **`coherentOn_zero`, with all four `Above`s removed.**  At `boxDecl`'s certified
history and the chain of `exists_inaccessibleChain_omega`, coherence holds outright. -/
theorem coherentOn'_zero (L : PropSplit envF nv)
    {R : List VExpr → List VExpr → Prop} (hS : L.Stable) (hR : CtxInvariant L R)
    (hRdF : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
      envF.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))
    {env : VEnv} (hwf : VEnv.WF' [.induct boxDecl, .axiom extAx] env) (hle : env ≤ envF) :
    CoherentOn' (V := V)
      ⟨omegaChain V, ls,
        cnstOf L (omegaChain V) ls (zeroOracle V) [.induct boxDecl, .axiom extAx]⟩ L env :=
  (coherentOn_iff_of_chain omegaChain_isInaccessibleChain L _ env).1
    (coherentOn_zero (κ := omegaChain V) (ls := ls) L hS hR hRdF hwf hle)

end ZeroUnwrapped

/-! ## 5. `ModelFits`'s relation parameter is not an obligation

`ModelFits` (`CnstRecursion.lean:655`) bundles **four** things: `L.Stable`, a relation `R`
with `CtxInvariant L R`, the pairing hypothesis
`hRd : env.IsDefEq 0 Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ)`, and `OracleFits`.
`CoherentWitness.lean:109` records that `CtxInvariant L R` alone is trivially satisfiable
(`R := Eq`) and that the *pair* is what must be tested.

This section tests the pair, and the answer is sharper than "consistent": the existential
over `R` can be **eliminated**.  `CtxAgree L` is the greatest relation satisfying
`CtxInvariant L`, so `∃ R, CtxInvariant L R ∧ hRd` is *equivalent* to `CtxAgreeRd L` — one
statement, no relation parameter, no `Above` anywhere.  `ModelFits` therefore has three
components rather than four (`modelFits_iff_ctxAgreeRd`), and the whole content of the
`R` slot is the junk-prefix context-conversion statement that `CtxAgreeRd` names.

What that statement needs is exactly what `StableAudit.lean`'s closing note calls the
junk-context gap: `CoherentWitness.ctxInvariant_prop_agrees` proves the `Δ = []` case for
**well-typed** subjects via `IsDefEq.defeqDFC`, and `Theory/Typing/Lemmas.lean:294`'s
`IsDefEqCtx` cannot be extended by an arbitrary common `A` (its `.succ` demands
`A₁ ≡ A₂ : .sort u`), which is why the `Δ ≠ []` case is not a corollary. -/

section CtxAgree

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ}

/-- **The greatest `CtxInvariant` relation**: two contexts agree if they have the same
length and are indistinguishable to `L` under every common prefix.  The prefix quantifier
is what makes it closed under `cons`, which is the only field of `CtxInvariant` that a
"just assert the two `iff`s" relation would fail. -/
def CtxAgree (L : PropSplit envF nv) (Γ₁ Γ₂ : List VExpr) : Prop :=
  Γ₁.length = Γ₂.length ∧
    ∀ (Δ : List VExpr) (ls : List ℕ),
      (∀ A : VExpr, L.IsPropAt ls (Δ ++ Γ₁) A ↔ L.IsPropAt ls (Δ ++ Γ₂) A) ∧
      (∀ e : VExpr, L.IsProofAt ls (Δ ++ Γ₁) e ↔ L.IsProofAt ls (Δ ++ Γ₂) e)

/-- `CtxAgree L` is itself a `CtxInvariant`. -/
theorem ctxInvariant_ctxAgree (L : PropSplit envF nv) : CtxInvariant L (CtxAgree L) where
  len h := h.1
  prop h ls A := (h.2 [] ls).1 A
  proof h ls e := (h.2 [] ls).2 e
  cons {Γ₁ Γ₂} h A := by
    refine ⟨congrArg Nat.succ h.1, fun Δ ls ↦ ?_⟩
    have e₁ : Δ ++ A :: Γ₁ = (Δ ++ [A]) ++ Γ₁ := by simp
    have e₂ : Δ ++ A :: Γ₂ = (Δ ++ [A]) ++ Γ₂ := by simp
    rw [e₁, e₂]
    exact h.2 (Δ ++ [A]) ls

/-- …and it is the **greatest** one: any `CtxInvariant` relation refines it.  This is the
half that eliminates the existential. -/
theorem ctxAgree_of_ctxInvariant {L : PropSplit envF nv}
    {R : List VExpr → List VExpr → Prop} (hR : CtxInvariant L R)
    {Γ₁ Γ₂ : List VExpr} (h : R Γ₁ Γ₂) : CtxAgree L Γ₁ Γ₂ := by
  refine ⟨hR.len h, fun Δ ls ↦ ?_⟩
  have key : ∀ Δ : List VExpr, R (Δ ++ Γ₁) (Δ ++ Γ₂) := by
    intro Δ
    induction Δ with
    | nil => exact h
    | cons A Δ ih => exact hR.cons ih A
  exact ⟨fun A ↦ hR.prop (key Δ) ls A, fun e ↦ hR.proof (key Δ) ls e⟩

/-! #### Bounds on `CtxAgree`

Per the standing check: the relation is neither trivially true nor empty. -/

/-- **Not empty.** -/
theorem ctxAgree_refl (L : PropSplit envF nv) (Γ : List VExpr) : CtxAgree L Γ Γ :=
  ⟨rfl, fun _ _ ↦ ⟨fun _ ↦ Iff.rfl, fun _ ↦ Iff.rfl⟩⟩

/-- A variable of type `Type 0` is **not** a proposition — the `Type`-side companion of
`PropSplitAudit.prop_forces_true`, and a genuine `bvar` instance. -/
theorem prop_forces_false_bvar (L : PropSplit envF nv) (ls : List ℕ) :
    ¬ L.IsPropAt ls [.sort (.succ .zero)] (.bvar 0) := by
  have h : envF.HasType nv [.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.bvar .zero
  have hΓ : OnCtx [(VExpr.sort (.succ .zero))] (envF.IsType nv) :=
    ⟨trivial, .succ (.succ .zero), VEnv.HasType.sort trivial⟩
  rw [L.prop_sound (u := .succ .zero) hΓ (by trivial) h]
  simp [VLevel.eval]

/-- **Not trivially true**, and not merely by a length mismatch: two contexts of the *same*
length that every `PropSplit` distinguishes.  `bvar 0` is a proposition under `Prop` and is
not one under `Type 0`. -/
theorem not_ctxAgree_sortShift (L : PropSplit envF nv) :
    ¬ CtxAgree L [.sort .zero] [.sort (.succ .zero)] := by
  intro h
  exact prop_forces_false_bvar L []
    (((h.2 [] []).1 (.bvar 0)).1 (prop_forces_true L []))

/-- **The pairing hypothesis, with the relation parameter gone.**  This is the whole content
of `ModelFits`' `R` slot. -/
def CtxAgreeRd (L : PropSplit envF nv) : Prop :=
  ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
    envF.IsDefEq nv Γ A A' (.sort u) → CtxAgree L (A' :: Γ) (A :: Γ)

/-- **The existential over `R` is eliminable.** -/
theorem exists_ctxInvariant_rd_iff (L : PropSplit envF nv) :
    (∃ R : List VExpr → List VExpr → Prop, CtxInvariant L R ∧
        ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
          envF.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ)) ↔ CtxAgreeRd L := by
  constructor
  · rintro ⟨R, hR, hRd⟩
    exact fun {_ _ _ _} hd ↦ ctxAgree_of_ctxInvariant hR (hRd hd)
  · exact fun h ↦ ⟨CtxAgree L, ctxInvariant_ctxAgree L, fun hd ↦ h hd⟩

/-- **`ModelFits` has three components, not four.**  `ls`, `L` and `o` remain; the relation
parameter is absorbed into `CtxAgreeRd`. -/
theorem modelFits_iff_ctxAgreeRd (κ : ℕ → V) (env : VEnv) (ds : List VDecl) :
    ModelFits κ env ds ↔
      ∃ (ls : List ℕ) (L : PropSplit env 0) (o : Name → List VLevel → V),
        L.Stable ∧ CtxAgreeRd L ∧ OracleFits L κ ls o ds := by
  constructor
  · rintro ⟨ls, L, o, R, hS, hR, hRd, hfits⟩
    exact ⟨ls, L, o, hS, (exists_ctxInvariant_rd_iff L).1 ⟨R, hR, fun hd ↦ hRd hd⟩, hfits⟩
  · rintro ⟨ls, L, o, hS, hA, hfits⟩
    obtain ⟨R, hR, hRd⟩ := (exists_ctxInvariant_rd_iff L).2 hA
    exact ⟨ls, L, o, R, hS, hR, fun hd ↦ hRd hd, hfits⟩

/-! ### …and for the natural `PropSplit` the slot is **discharged**

`IsDefEq.defeqDFC'` (`Theory/Typing/Lemmas.lean:712`) already carries an arbitrary common
prefix `Δ`: it moves `IsDefEq (Δ ++ Γ₁)` to `IsDefEq (Δ ++ Γ₂)` for `IsDefEqCtx Γ₀ Γ₁ Γ₂`,
by an induction that generalises `Δ`.  So the junk-prefix case is **not** a gap after all,
and for `PropSplitAudit.propSplitOf` — whose `IsPropAt`/`IsProofAt` *contain* their own
typing derivations, so no well-typedness side condition has to be supplied — `CtxAgreeRd`
holds outright.

Note the contrast with `CoherentWitness.ctxInvariant_prop_agrees`, which proves the same
`iff` for an arbitrary `PropSplit` and therefore needs `hB : HasType nv (A :: Γ) B (.sort w)`
as a hypothesis: at the *natural* split the hypothesis is already inside the predicate.

Consequence (`modelFits_of_propSplit_inputs`): `ModelFits`' four components reduce to
**two** — `env.PropDescend 0` (via `L.Stable`) and `OracleFits` — on top of
`env.Ordered`, `env.PropUniq 0`, `env.PropTypeAgree 0`.  At `nv = 0` those last two are the
minimal form: `PropReduce.PropUniq.of_zero`/`PropTypeAgree.of_zero` derive every other `nv`
from them, and `PropUniqFromFalse` derives `PropUniq` from `PropTypeAgree` plus the goal's
own `hfalse`. -/

section Natural

variable {env : VEnv}

/-- **`CtxAgree` at defeq-converted contexts, for the natural split** — including every
common prefix, and with no typing hypothesis on the subject. -/
theorem propSplitOf_ctxAgree (henv : env.Ordered) (hU : env.PropUniq nv)
    (hT : env.PropTypeAgree nv) {Γ : List VExpr} {A A' : VExpr} {u : VLevel}
    (h : env.IsDefEq nv Γ A A' (.sort u)) :
    CtxAgree (propSplitOf env nv hU hT) (A' :: Γ) (A :: Γ) := by
  have hfwd : VEnv.IsDefEqCtx env nv Γ (A' :: Γ) (A :: Γ) := .succ .zero h.symm
  have hbwd : VEnv.IsDefEqCtx env nv Γ (A :: Γ) (A' :: Γ) := .succ .zero h
  refine ⟨rfl, fun Δ ls ↦ ⟨fun B ↦ ⟨?_, ?_⟩, fun e ↦ ⟨?_, ?_⟩⟩⟩
  · exact fun ⟨w, hw, hB, h0⟩ ↦ ⟨w, hw, VEnv.IsDefEq.defeqDFC' henv hfwd hB, h0⟩
  · exact fun ⟨w, hw, hB, h0⟩ ↦ ⟨w, hw, VEnv.IsDefEq.defeqDFC' henv hbwd hB, h0⟩
  · exact fun ⟨C, w, hw, he, hC, h0⟩ ↦ ⟨C, w, hw, VEnv.IsDefEq.defeqDFC' henv hfwd he,
      VEnv.IsDefEq.defeqDFC' henv hfwd hC, h0⟩
  · exact fun ⟨C, w, hw, he, hC, h0⟩ ↦ ⟨C, w, hw, VEnv.IsDefEq.defeqDFC' henv hbwd he,
      VEnv.IsDefEq.defeqDFC' henv hbwd hC, h0⟩

/-- **`ModelFits`' relation slot, discharged.** -/
theorem ctxAgreeRd_propSplitOf (henv : env.Ordered) (hU : env.PropUniq nv)
    (hT : env.PropTypeAgree nv) : CtxAgreeRd (propSplitOf env nv hU hT) :=
  fun hd ↦ propSplitOf_ctxAgree henv hU hT hd

/-- **`ModelFits` from two inputs plus the oracle.**  The relation slot is gone and the
proof-split slot is `PropDescend`; what is left of the model side is `OracleFits`, i.e. the
`.axiom`/`.quot` obligations and the `.induct` residual. -/
theorem modelFits_of_propSplit_inputs {κ : ℕ → V} {ds : List VDecl} (henv : env.Ordered)
    (hU : env.PropUniq 0) (hT : env.PropTypeAgree 0) (hD : env.PropDescend 0)
    (ls : List ℕ) (o : Name → List VLevel → V)
    (hfits : OracleFits (propSplitOf env 0 hU hT) κ ls o ds) : ModelFits κ env ds :=
  (modelFits_iff_ctxAgreeRd κ env ds).2
    ⟨ls, propSplitOf env 0 hU hT, o,
      propSplitOf_stable (hU := hU) (hT := hT) henv hD,
      ctxAgreeRd_propSplitOf henv hU hT, hfits⟩

end Natural

end CtxAgree

end Lean4Lean.SetModel

/-! ## Axiom census -/

#print axioms Lean4Lean.SetModel.not_isInaccessible_empty
#print axioms Lean4Lean.SetModel.not_isInaccessibleChain_one_zero
#print axioms Lean4Lean.SetModel.above_of_not_chain
#print axioms Lean4Lean.SetModel.above_false_zeroChain
#print axioms Lean4Lean.SetModel.above_omegaChain_iff
#print axioms Lean4Lean.SetModel.payload_omegaChain_of_forall
#print axioms Lean4Lean.SetModel.oracleOK_iff_of_chain
#print axioms Lean4Lean.SetModel.defEqOK_iff_of_chain
#print axioms Lean4Lean.SetModel.inductOracleOK_iff_of_chain
#print axioms Lean4Lean.SetModel.coherentOn_iff_of_chain
#print axioms Lean4Lean.SetModel.coherentOn'_zero
#print axioms Lean4Lean.SetModel.ctxInvariant_ctxAgree
#print axioms Lean4Lean.SetModel.ctxAgree_of_ctxInvariant
#print axioms Lean4Lean.SetModel.exists_ctxInvariant_rd_iff
#print axioms Lean4Lean.SetModel.modelFits_iff_ctxAgreeRd
#print axioms Lean4Lean.SetModel.propSplitOf_ctxAgree
#print axioms Lean4Lean.SetModel.ctxAgreeRd_propSplitOf
#print axioms Lean4Lean.SetModel.modelFits_of_propSplit_inputs
#print axioms Lean4Lean.SetModel.ctxAgree_refl
#print axioms Lean4Lean.SetModel.not_ctxAgree_sortShift
