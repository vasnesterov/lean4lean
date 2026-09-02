import Lean4Lean.Theory.SetModel.ModelExists
import Lean4Lean.Theory.SetModel.PropUpFits
import Lean4Lean.Theory.SetModel.UnitOracleWitness

/-!
# The `←` half of the equiconsistency, as one named theorem — and its witness gap

`Theory/Equiconsistency.lean` states the headline biconditional with a single `sorry`.
Only its `←` half — the **upper bound**

    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent

is on the path to `kernel_sound`; the `→` half (building models of `ZFC + n inaccessibles`
inside Lean TT) is what makes the statement an `↔` and nothing consumes it.  This file
gives the `←` half its own name and the tightest hypothesis set the tree supports, and then
measures whether that hypothesis set — and the *conclusion* — is inhabited.

## What is proved

`upper_bound_of_inputs` (§2): the `←` half from **three** separately named inputs, none of
them a bundled existential:

| input | content |
|---|---|
| `PropTypeAgreeInput` | every Lean-reachable environment has `VEnv.PropTypeAgree 0` |
| `InstDescendInput` | …and `VEnv.InstDescendUp 0` |
| `OracleInput` | at every Lean-reachable environment the oracle's `.axiom`/`.quot`/`.induct` obligations are met |

Everything else is discharged: Input A (`ModelExists.inaccModelInput`), the relation slot
(`AboveAudit.ctxAgreeRd_propSplitUp`), `PropSplit.Stable` (`PropSplitUp.propSplitUp_stable`),
`VEnv.PropUniq 0` (`PropUniqFromFalse.PropUniq.of_propTypeAgree`, from the goal's own
inconsistency hypothesis), the whole `VEnv.WF'` recursion (`CnstRecursion.coherentOn_cnstOf`)
and `hκ` (`InaccChainOmega.exists_inaccessibleChain_omega`).

Compared with `ModelExists.upper_bound_of_modelFits`, whose one hypothesis
`ModelFitsLeanInput` bundles all three *plus* an existential over `PropSplit`, `ls`, `o` and
`R`: this packaging cannot be satisfied "by accident" at a junk split, and each input can be
attacked on its own.  Note one thing the unbundling buys concretely — `PropUniq` disappears
entirely, because `leanTTConsistent`'s own goal supplies it, and `ModelFitsLeanInput`'s shape
has nowhere to put that.

## What is **not** proved, and the reason it is the headline

**UPDATE 2026-09-02 — this section is now historical.**  `SetModel/PreludeWitness.lean`
proves `PreludeWF`, hence `∃ env, env.LeanWF` (through `exists_leanWF_iff` below), hence
`not_forall_not_leanWF : ¬ ∀ env, ¬ env.LeanWF`.  So the hypothesis of §3's
`upper_bound_vacuous_of_no_leanWF` is **refuted** and the collapse it records can no longer
be used to discharge anything.  §3 and §4 are kept exactly as they were: they are the
statement of the gap, and the instrument that measures it, and both are still what makes the
witness worth having.  What follows describes the situation *before* that file.

**At the time of writing, nothing in this repository exhibited an environment satisfying
`VEnv.LeanWF`.**  That is the quantifier of `leanTTConsistent` itself, so:

* the *conclusion* of the `←` half is true for free if `LeanWF` is empty
  (`leanTTConsistent_of_no_leanWF`);
* and so is every one of the three inputs (`propTypeAgreeInput_of_no_leanWF`,
  `instDescendInput_of_no_leanWF`, `oracleInput_of_no_leanWF`).

So §3 does not merely note a missing witness: it proves that the *whole* reduction — premises
and conclusion together — collapses to `True` at the same time.  This is the `SetModel`-side
analogue of `docs/vacuity-ledger.md` rows 126 and 104a (`addDecl.WF` is inhabited, and the witness is
the empty environment); here the corresponding witness would have to be a *prelude*
environment, and there is none.

§4 pins the missing object exactly: `∃ env, env.LeanWF` is **equivalent** to
`∃ env, VEnv.WF' leanPrelude.reverse env` (`exists_leanWF_iff`), i.e. to abstract
well-formedness of the seven prelude steps and nothing more.  The `ds` of `LeanWF` cannot
help: a longer history contains a prelude-only prefix.

§6 discharges the **first** of those seven steps, `eqIndDecl`, over an arbitrary environment
(`eqIndDecl_WF`) — so the gap is six steps, not seven, and it is unbuilt rather than blocked.
**The other six are now discharged too** (`SetModel/PreludeWitness.lean`), and its §9.2 of
`docs/handoff-setmodel.md` records that this file's costing of them, in §6 below, was wrong in
three places and wrong in the pessimistic direction each time.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. The three inputs -/

/-- **Input 1.**  Unique typing, in the only form the model consumes: two types of the same
term agree on being propositions.  `NotProofNoModel.nonempty_propSplit_iff_agree` makes this
*equivalent* to `Nonempty (PropSplit env 0)`, so no choice of predicate removes it. -/
def PropTypeAgreeInput : Prop := ∀ env : VEnv, env.LeanWF → env.PropTypeAgree 0

/-- **Input 2.**  The substitution-descent residual of `PropSplit.Stable` for the lift-closed
split (`PropSplitUp.lean` §5).  Two fields, neither of them strengthening-shaped. -/
def InstDescendInput : Prop := ∀ env : VEnv, env.LeanWF → env.InstDescendUp 0

/-- **Input 3.**  The oracle's obligations: `OracleOK` at each `.axiom`, `QuotOracleOK` at
`.quot`, and `InductOracleOK` at each `.induct` — the last being the `.induct` residual that
`InductOracleAudit.lean` §5 bounds field by field.

`henv`, `hU` and `hT` are taken as arguments rather than derived because the split the
obligations are stated against is `propSplitUp env 0 henv hU hT`; the value does not depend
on which proofs are supplied (they are `Prop`s), so this is a single obligation per `ds`, not
a family. -/
def OracleInput : Prop :=
  ∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
    (κ : ℕ → V), (∀ m : ℕ, IsInaccessibleChain m κ) →
    ∀ (env : VEnv) (ds : List VDecl), VEnv.WF' ds env → PureOverPrelude ds →
      ∀ (henv : env.Ordered) (hU : env.PropUniq 0) (hT : env.PropTypeAgree 0),
        ∃ (ls : List ℕ) (o : Name → List VLevel → V),
          OracleFits (propSplitUp env 0 henv hU hT) κ ls o ds

/-! ## 2. The `←` half from the three inputs

The chain, in the order the proof takes it:

`env.LeanWF` → `VEnv.WF' ds env ∧ PureOverPrelude ds` (`leanWF_iff`) → `env.Ordered`
→ `PropUniq 0` (from the goal's own inconsistency witness) → `propSplitUp` with `Stable`
and `CtxAgreeRd` → `ModelFits` (`modelFits_of_propSplitUp_inputs`) → `env.Consistent`
(`consistent_of`, i.e. `coherentOn_cnstOf` composed with `FalseProp.lean`) → `leanTTConsistent`
→ the `←` half (`inaccModelInput`). -/

section Reduction

variable {V : Type} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **One environment.**  Note where `PropUniq` comes from: `env.Consistent` is a negation,
so its own hypothesis `hf` is available to the proof, and `PropUniq.of_propTypeAgree` turns
`PropTypeAgree` into `PropUniq` using it.  That is why `PropUniq` is not an input. -/
theorem consistent_of_inputs {κ : ℕ → V} (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (hTI : PropTypeAgreeInput) (hII : InstDescendInput) (hO : OracleInput)
    {env : VEnv} {ds : List VDecl} (hwf : VEnv.WF' ds env) (hp : PureOverPrelude ds) :
    env.Consistent := by
  intro hf
  have hlw : env.LeanWF := leanWF_iff.2 ⟨ds, hwf, hp⟩
  have henv : env.Ordered := VEnv.WF.ordered ⟨ds, hwf⟩
  have hT : env.PropTypeAgree 0 := hTI env hlw
  have hI : env.InstDescendUp 0 := hII env hlw
  have hU : env.PropUniq 0 := VEnv.PropUniq.of_propTypeAgree henv hf hT
  obtain ⟨ls, o, hfits⟩ := hO V κ hκ env ds hwf hp henv hU hT
  obtain ⟨ls', L, o', R, hS, hR, hRd, hfits'⟩ :=
    modelFits_of_propSplitUp_inputs (κ := κ) henv hU hT hI ls o hfits
  exact consistent_of hκ L o' hS hR hRd hwf (noUnsafe_of_pureOverPrelude hp) hfits' hf

/-- **`leanTTConsistent` in one model.** -/
theorem leanTTConsistent_of_inputs (κ : ℕ → V) (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (hTI : PropTypeAgreeInput) (hII : InstDescendInput) (hO : OracleInput) :
    leanTTConsistent := by
  intro env hlw
  obtain ⟨ds, hwf, hp⟩ := leanWF_iff.1 hlw
  exact consistent_of_inputs hκ hTI hII hO hwf hp

end Reduction

/-- **The `←` half of the equiconsistency, from the three inputs.**  This is the theorem
`Theory/Equiconsistency.lean`'s `inconsistent_of_upper_bound` consumes, and the only half of
the biconditional `kernel_sound` needs. -/
theorem upper_bound_of_inputs (hTI : PropTypeAgreeInput) (hII : InstDescendInput)
    (hO : OracleInput) :
    Entailment.Consistent (𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 : SetTheory) → leanTTConsistent := fun hc ↦
  inaccModelInput leanTTConsistent
    (fun _ _ _ _ _ κ hκ ↦ leanTTConsistent_of_inputs κ hκ hTI hII hO) hc

/-! ## 3. The vacuity instrument: premises and conclusion collapse together

Every instrument in this repository reads *conclusions* — `scripts/sorry-census.lean` looks
for `sorryAx` in a proof term, the cone walker follows dependencies, `#print axioms` reports
what a proof uses.  None asks whether a hypothesis is inhabited
(`docs/vacuity-ledger.md` §0, blindness 8 and row 90a).  So the reduction above is measured
here against the only thing that can make it worthless: emptiness of `VEnv.LeanWF`, which is
simultaneously the quantifier of the conclusion and of all three premises. -/

section Vacuity

/-- **The conclusion is free if `LeanWF` is empty.** -/
theorem leanTTConsistent_of_no_leanWF (h : ∀ env : VEnv, ¬ env.LeanWF) : leanTTConsistent :=
  fun env hlw ↦ absurd hlw (h env)

/-- **…and so is input 1.** -/
theorem propTypeAgreeInput_of_no_leanWF (h : ∀ env : VEnv, ¬ env.LeanWF) :
    PropTypeAgreeInput := fun env hlw ↦ absurd hlw (h env)

/-- **…and input 2.** -/
theorem instDescendInput_of_no_leanWF (h : ∀ env : VEnv, ¬ env.LeanWF) :
    InstDescendInput := fun env hlw ↦ absurd hlw (h env)

/-- **…and input 3**, whose quantifier is the `WF'`/`PureOverPrelude` pair rather than
`LeanWF`; `leanWF_iff` identifies the two, so the same emptiness kills it. -/
theorem oracleInput_of_no_leanWF (h : ∀ env : VEnv, ¬ env.LeanWF) : OracleInput := by
  intro _ _ _ _ _ _ _ env ds hwf hp _ _ _
  exact absurd (leanWF_iff.2 ⟨ds, hwf, hp⟩) (h env)

/-- **The collapse, stated once.**  If `LeanWF` is empty then `upper_bound_of_inputs` proves
a true conclusion from true premises and measures nothing.  Recorded as a theorem rather than
as prose because the taxonomy's kind 4 — a negative asserted rather than proved — is the
expensive mistake in this corner. -/
theorem upper_bound_vacuous_of_no_leanWF (h : ∀ env : VEnv, ¬ env.LeanWF) :
    PropTypeAgreeInput ∧ InstDescendInput ∧ OracleInput ∧ leanTTConsistent :=
  ⟨propTypeAgreeInput_of_no_leanWF h, instDescendInput_of_no_leanWF h,
   oracleInput_of_no_leanWF h, leanTTConsistent_of_no_leanWF h⟩

end Vacuity

/-! ## 4. The missing witness, pinned exactly

`VEnv.LeanWF env` is `∃ ds, VEnv.WF' (ds ++ leanPrelude.reverse) env ∧ ∀ d ∈ ds, d.isPure`.
The `ds` cannot help: a `VEnv.WF'` history of a concatenation contains one of the suffix
alone, at the intermediate environment.  So the whole content of "some environment is a Lean
environment" is **abstract well-formedness of the seven prelude steps**. -/

section Witness

/-- A `VEnv.WF'` history of `ds ++ pre` passes through a history of `pre`. -/
theorem exists_wf'_of_append : ∀ (ds pre : List VDecl) {env : VEnv},
    VEnv.WF' (ds ++ pre) env → ∃ env₀, VEnv.WF' pre env₀
  | [], _, _, h => ⟨_, h⟩
  | _ :: ds, pre, _, h => by
    cases h with | decl _ h2 => exact exists_wf'_of_append ds pre h2

/-- **The prelude is well formed as an abstract declaration list** — the one missing object.
Named so that a future stream can state its target without re-deriving §4. -/
def PreludeWF : Prop := ∃ env : VEnv, VEnv.WF' leanPrelude.reverse env

/-- `PreludeWF` gives a Lean environment: take `ds = []`. -/
theorem leanWF_of_preludeWF : PreludeWF → ∃ env : VEnv, env.LeanWF
  | ⟨env, h⟩ => ⟨env, [], by simpa using h, nofun⟩

/-- **…and it is exactly what is needed.**  Not merely sufficient: any Lean environment's
history contains a prelude-only prefix, so the two statements are equivalent.  This is the
sharp form of §3: the reduction of §2 measures something iff `PreludeWF` holds. -/
theorem exists_leanWF_iff : (∃ env : VEnv, env.LeanWF) ↔ PreludeWF := by
  refine ⟨fun ⟨_, ds, hwf, _⟩ ↦ exists_wf'_of_append ds _ hwf, leanWF_of_preludeWF⟩

/-- The seven steps, listed in the order `VEnv.WF'` consumes them (most recent first), so
that the innermost obligation — the only one over `VEnv.empty` — is visible: it is
`eqIndDecl`. -/
theorem preludeRev_eq :
    leanPrelude.reverse =
      [.axiom quotSoundConst, .quot, .axiom choiceConst, .induct nonemptyIndDecl,
       .axiom propextConst, .induct iffIndDecl, .induct eqIndDecl] := rfl

end Witness

/-! ## 5. Positive control: which of the three inputs is *not* the binding constraint

§3 and §4 say the reduction is unwitnessed.  That is a statement about `PureOverPrelude`
histories, and it would be a mistake to read it as "the oracle obligations are unreachable":
they are not.  At a certified `VEnv.WF'` history that the recursion is entitled to visit —
just not a Lean one — `OracleFits` is **discharged outright, at an arbitrary `PropSplit` and
an arbitrary `κ`** (`UnitOracleWitness.oracleFits_unit_at_consumer`, row 72 of the vacuity
ledger).  So input 3's payload is satisfiable; what is missing at `unitEnv` is only the split.

The measurement to take from this section: at a reachable history, **input 3 is met and
inputs 1–2 are what is open.**  At a *prelude* history that is no longer true — the `.induct`
steps there are `eqIndDecl`, `iffIndDecl` and `nonemptyIndDecl`, all with parameters and (for
`Eq`) an index, which `docs/vacuity-ledger.md` row 83c records as the open frontier of
`InductOracleOK`.  Both statements are needed; neither implies the other. -/

section Control

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ}

/-- **Input 3's payload, satisfied at a certified history.**  `unitEnv` is reached by a
one-declaration `VEnv.WF'` history (`unitDecl_history`) whose only declaration is `noUnsafe`,
and there an oracle exists for *every* split and *every* `κ` — no chain condition, no `Above`
unwrapping.  The `hle` is what `coherentOn_cnstOf` already holds at the step. -/
theorem exists_oracleFits_unit (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (hle : UnitAudit.unitEnv ≤ envF) :
    ∃ o : Name → List VLevel → V, OracleFits L κ ls o [.induct UnitAudit.unitDecl] :=
  ⟨UnitAudit.unitOracle V, UnitAudit.oracleFits_unit L κ ls hle⟩

/-- **…and the history it sits on is real**, so the previous theorem is not about an empty
class of environments.  `unitEnv` is *not* `LeanWF` (its history is one `.induct`, not the
prelude), which is exactly why §3 stands. -/
theorem unitEnv_history_noUnsafe :
    VEnv.WF' [VDecl.induct UnitAudit.unitDecl] UnitAudit.unitEnv ∧
      ∀ d ∈ [VDecl.induct UnitAudit.unitDecl], d.noUnsafe :=
  ⟨UnitAudit.unitDecl_history, UnitAudit.unitDecl_noUnsafe⟩

end Control

/-! ## 6. The first prelude step, discharged

§4 reduces the witness gap to `PreludeWF`.  Seven steps; this is the first of them, and the
only one over `VEnv.empty`.

**The remaining six are in `SetModel/PreludeWitness.lean`, and the forecast that used to
stand here was wrong three times over — each time by overstating the cost.**  Kept, corrected,
because `docs/soundness-ledger.md` tracks this file's forecasts:

* "each `VIndField.WF` field — `binders_indep`, `level`, `pos` — wants its own one-line lemma":
  **no lemma was missing.**  `binders_indep` is `nofun` (both blocks' fields are
  non-recursive), `level` is `(VLevel.le_antisymm_iff.1 VLevel.imax_zero).1` from lemmas
  already in `Theory/VLevel.lean`, and the field the forecast omitted — **`hasType`** — was the
  one with content: `forallEDF` types a pi at `.sort (.imax u v)` while `F.lvl` is recorded as
  `.zero`, so a `defeqDF` through `sortDF … VLevel.imax_zero` is needed.
* "the three `.axiom` steps … spine derivations of the size `QuotInterp.lean` pays for
  `Quot.lift`": **12, 7 and 45 lines**, every step an `exact` of `constDF`/`appDF`/`bvar`, no
  rewriting and no transport.  What `QuotInterp.lean` pays for `Quot.lift` is its *model
  interpretation*, which is a different obligation from its type being a type.
* the `.quot` step: it needs **only** `env.QuotReady` (one `rfl`) and `addQuot = some env'`.
  Well-formedness of the four quotient constants is the *theorem* `addQuot_WF`
  (`Theory/Typing/QuotLemmas.lean`), not an obligation of `VDecl.WF.quot` — so it was the
  cheapest of the six, not a middle-cost one. -/

section PreludeSteps

set_option maxHeartbeats 1000000 in
/-- **The prelude's first step, discharged: `Eq` is a well-formed inductive block** — over
an *arbitrary* environment, because nothing in the block's data mentions a constant other
than its own type former (which `ctors` reads out of the staged environment `env₁`).

This is one of the seven obligations `PreludeWF` decomposes into (§4), and the first one:
`preludeRev_eq` puts `.induct eqIndDecl` last in the `VEnv.WF'` list, i.e. first
chronologically, and it is the only step over `VEnv.empty`.

The proof is entirely by the introduction rules — `sortDF`, `bvar`, `forallEDF`, `constDF`
and three `appDF`s for `Eq α a a` — with no rewriting and no transport, which is the
`docs/soundness-ledger.md` prediction about spine arithmetic holding once more. -/
theorem eqIndDecl_WF (env : VEnv) : VInductDecl'.WF env eqIndDecl := by
  constructor
  case types_ne => simp [eqIndDecl]
  case params =>
    show OnCtx [VExpr.bvar 0, VExpr.sort (.param 0)] _
    exact ⟨⟨trivial, ⟨_, .sortDF (by decide) (by decide) (.refl _)⟩⟩, ⟨.param 0, .bvar .zero⟩⟩
  case isLE => intro _; exact Or.inr ⟨_, rfl, Or.inr ⟨_, rfl, by intro i F hF; simp at hF⟩⟩
  case types =>
    intro T hT
    simp only [eqIndDecl, List.mem_cons, List.not_mem_nil, or_false] at hT
    subst hT
    have hty : VEnv.IsType env 1 [] (VExpr.forallE (.sort (.param 0))
        (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) := by
      refine .forallE ⟨_, .sortDF (by decide) (by decide) (.refl _)⟩ ?_
      refine .forallE ⟨.param 0, .bvar .zero⟩ ?_
      refine .forallE ⟨.param 0, .bvar (.succ .zero)⟩ ?_
      exact ⟨_, .sortDF (by decide) (by decide) (.refl _)⟩
    refine { indices := ?_, isType := hty, canon := hty }
    show OnCtx [VExpr.bvar 1, VExpr.bvar 0, VExpr.sort (.param 0)] _
    exact ⟨⟨⟨trivial, ⟨_, .sortDF (by decide) (by decide) (.refl _)⟩⟩,
      ⟨.param 0, .bvar .zero⟩⟩, ⟨.param 0, .bvar (.succ .zero)⟩⟩
  case ctors =>
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp only [eqIndDecl, List.getElem?_cons_zero, Option.some.injEq] at hT
      subst hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      have hEq : env₁.constants ``Eq = some ⟨1, VExpr.forallE (.sort (.param 0))
          (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ :=
        VEnv.addConstList_constants (cs := eqIndDecl.typeConsts) he
          (``Eq, ⟨1, _⟩) (by simp [eqIndDecl, VInductDecl'.typeConsts])
      refine { params_len := rfl, params_eq := ?_, fields := nofun, args_len := rfl,
               args_fresh := ?_, args_ty := ?_, result := ?_ }
      · exact .succ (.succ .zero (.sortDF (by decide) (by decide) (.refl _))) (.bvar .zero)
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        subst ha; trivial
      · exact .cons (.bvar .zero) .nil
      · have hE : VEnv.HasType env₁ 1 [VExpr.bvar 0, VExpr.sort (.param 0)]
            (.const ``Eq [.param 0]) (VExpr.forallE (.sort (.param 0))
              (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) :=
          .constDF hEq (by intro l hl; simp at hl; subst hl; decide)
            (by intro l hl; simp at hl; subst hl; decide) rfl (.cons (by rfl) .nil)
        exact ((hE.appDF (.bvar (.succ .zero))).appDF (.bvar .zero)).appDF (.bvar .zero)

/-- **…and the innermost history exists.**  `VEnv.WF'` reaches an environment declaring the
`Eq` block from `VEnv.empty`.  This is `PreludeWF` for the one-element suffix of
`leanPrelude.reverse`, i.e. the base case of the seven. -/
theorem exists_eqIndDecl_history : ∃ env : VEnv, VEnv.WF' [VDecl.induct eqIndDecl] env :=
  ⟨_, .decl (.induct (eqIndDecl_WF _) rfl) .empty⟩

end PreludeSteps

end Lean4Lean.SetModel

/-! ## Axiom census -/

#print axioms Lean4Lean.SetModel.consistent_of_inputs
#print axioms Lean4Lean.SetModel.leanTTConsistent_of_inputs
#print axioms Lean4Lean.SetModel.upper_bound_of_inputs
#print axioms Lean4Lean.SetModel.leanTTConsistent_of_no_leanWF
#print axioms Lean4Lean.SetModel.oracleInput_of_no_leanWF
#print axioms Lean4Lean.SetModel.upper_bound_vacuous_of_no_leanWF
#print axioms Lean4Lean.SetModel.exists_wf'_of_append
#print axioms Lean4Lean.SetModel.exists_leanWF_iff
#print axioms Lean4Lean.SetModel.preludeRev_eq
#print axioms Lean4Lean.SetModel.exists_oracleFits_unit
#print axioms Lean4Lean.SetModel.unitEnv_history_noUnsafe
#print axioms Lean4Lean.SetModel.eqIndDecl_WF
#print axioms Lean4Lean.SetModel.exists_eqIndDecl_history
