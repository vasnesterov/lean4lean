import Lean4Lean.Theory.SetModel.InaccChainOmega
import Lean4Lean.Theory.MutualDefUnsound

/-!
# `ModelFitsInput` is **false**, and the repaired input

`CnstRecursion.lean` §7 reduces H2 to two inputs:

    upper_bound_of (hA : InaccModelInput) (hB : ModelFitsInput) :
      Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent

`docs/vacuity-ledger.md` row 11b records `ModelFitsInput` as "row-2-shaped: a proved
theorem whose second hypothesis is false exactly when it has anything to say", and names
`not_modelFitsInput` as the witness — **but no such theorem existed**.  This file supplies
it, and then supplies the repair.

## The defect

`ModelFitsInput` asks for `ModelFits κ env ds` at *every* `ds` with `VEnv.WF' ds env` and
`∀ d ∈ ds, d.noUnsafe`.  `noUnsafe` excludes exactly one `VDecl` former, `.unsafeDef`; it
does **not** exclude `.axiom`.  And `VDecl.WF env (.axiom ci) env'` asks only that `ci`'s
type *be a type* — never that it be inhabited.  So the one-declaration history

    axiom Bad : ∀ p : Prop, p

is `VEnv.WF'` and `noUnsafe` (`badAx_history`, `badAx_noUnsafe`), and at it `OracleFits`'
`.axiom` clause asks the oracle for an element of `⟦∀ p : Prop, p⟧ = ∅` — refuted by
`CnstRecursion.not_oracleOK_falseProp`.  Hence `not_modelFits_badAx`, and hence
`not_modelFitsInput`: `upper_bound_of` proves its conclusion from a hypothesis that is
false as soon as a model exists at all.

The same argument kills `leanTTConsistent_of`'s hypothesis `H` verbatim
(`not_modelFits_uniform`), so this is not a defect of the §7 packaging only.

Two things the refutation does *not* use, worth stating because they are the two live
model-side unknowns and neither is implicated:

* it does not build a `PropSplit` — `ModelFits` is an existential, so the `L` is
  *received* and then handed straight to `not_oracleOK_falseProp`;
* it does not touch `InductOracleOK`.  The list has no `.induct` step at all.

## The repair

`leanTTConsistent` quantifies over `env.LeanWF`, which is *strictly* narrower: the user
part of the history must be `VDecl.isPure`, and `.axiom` is the one former that is
`noUnsafe` but not `isPure` (`MutualDefUnsound.lean` pins this).  So the fix is to
quantify the input over exactly that: `PureOverPrelude`, i.e. the standard prelude
followed by pure steps.  `leanWF_iff` shows the pair `VEnv.WF' ds env ∧ PureOverPrelude ds`
*is* `env.LeanWF`, so nothing is given away.

* `leanTTConsistent_of_lean` — the reduction, re-run at the narrowed input.
* `upper_bound_of_lean` — §7 assembled from it, and `upper_bound_of_omega` the same with
  `InaccModelInput` replaced by the chain-free `ModelExistsInput` of
  `InaccChainOmega.lean`.
* `not_pureOverPrelude_badAx` and `axiom_mem_pureOverPrelude` — the refutation route is
  **blocked**, and not merely at this one witness: *every* axiom in a Lean history is one
  of the prelude's three.
* `pureOverPrelude_prelude` — and the narrowed input is not trivially true: the prelude is
  itself a `PureOverPrelude` history, and it contains three `.induct` steps, so the
  `.induct` residual survives the repair unchanged.

## What this file does **not** establish

`ModelFitsLeanInput` is **not** shown satisfiable, and this file gives no positive bound
on it.  Both of its known unknowns survive the narrowing untouched:

1. `ModelFits` demands a `PropSplit env 0` with `L.Stable`; per `docs/model-interface.md`
   nothing in the tree exhibits one, and `PropSplitAudit.exists_propSplit` reduces it to
   `VEnv.PropUniq` / `VEnv.PropTypeAgree`, both open.  §2's refutation deliberately does
   not use this — it *receives* `L` from `ModelFits`' existential — so the two are
   independent, and the narrowing settles neither.
2. `axiom_mem_pureOverPrelude` closes the `.axiom` route, so a refutation of
   `ModelFitsLeanInput` would have to come from an `.induct` step: some `VInductDecl'.WF`
   block one of whose declared constants is uninhabited in the model.  Whether any such
   block exists is exactly the open question `InductOracleAudit.lean` §5 records — its
   `consts`-field bound is "open at a `WF` block".  So the honest summary is: `.axiom` can
   no longer refute Input B, and whether anything else can is the residual's own question.

The two-way bound this file *does* carry is on `PureOverPrelude`, and it is checked in both
directions: false at `[.axiom badAx]` (`not_pureOverPrelude_badAx`) and true at
`leanPrelude.reverse` (`pureOverPrelude_prelude`).
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. The witness: one axiom of type `∀ p : Prop, p` -/

namespace ModelFitsAudit

/-- `axiom Bad : ∀ p : Prop, p`.  Nothing about it is exotic: `falseProp_isType` says its
type is a type over *any* environment, which is all `VDecl.WF`'s `.axiom` rule asks. -/
def badAx : VConstVal := { name := `Bad, uvars := 0, type := falseProp }

/-- The environment after that one axiom, in the shape `addConst` produces. -/
def badEnv : VEnv where
  constants n := if `Bad = n then some ⟨0, falseProp⟩ else none
  defeqs _ := False

theorem badAx_toVConstant : badAx.toVConstant = ⟨0, falseProp⟩ := rfl

theorem badEnv_add : VEnv.empty.addConst badAx.name badAx.toVConstant = some badEnv := rfl

theorem badAx_WF : badAx.toVConstant.WF VEnv.empty := falseProp_isType _

theorem badAx_decl_WF : VDecl.WF VEnv.empty (.axiom badAx) badEnv :=
  .axiom badAx_WF badEnv_add

/-- **A certified one-declaration history.**  This is a list the soundness induction is
entitled to visit under `ModelFitsInput`'s hypotheses. -/
theorem badAx_history : VEnv.WF' [.axiom badAx] badEnv := .decl badAx_decl_WF .empty

theorem badAx_noUnsafe : ∀ d ∈ [VDecl.axiom badAx], d.noUnsafe := by
  intro d hd; simp only [List.mem_singleton] at hd; subst hd; trivial

/-- …and it is **not** `isPure`, which is what the repair below turns on. -/
theorem badAx_not_isPure : ¬ (VDecl.axiom badAx).isPure := id

/-- The environment really is inconsistent, so the oracle is being asked for something
that cannot exist — this is not an artefact of the interpretation. -/
theorem badEnv_not_consistent : ¬ badEnv.Consistent :=
  fun h ↦ h ⟨.const `Bad [], VEnv.IsDefEq.constDF (ci := ⟨0, falseProp⟩) rfl nofun nofun rfl .nil⟩

end ModelFitsAudit

/-! ## 2. The refutation -/

section Refute

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {κ : ℕ → V}

open ModelFitsAudit

/-- **`ModelFits` is refuted at the one-axiom history.**  Note which hypothesis does the
work: only `hκ`, which `ModelFitsInput` hands over itself. -/
theorem not_modelFits_badAx (hκ : ∀ m : ℕ, IsInaccessibleChain m κ) :
    ¬ ModelFits κ badEnv [.axiom badAx] := by
  intro h
  obtain ⟨ls, L, o, R, _, _, _, hfits⟩ := h
  rw [show OracleFits L κ ls o [VDecl.axiom badAx]
      = (OracleStepOK L κ ls o (.axiom badAx) [] ∧ True) from rfl] at hfits
  exact not_oracleOK_falseProp (ls := ls) hκ L o _ `Bad hfits.1

/-- **`leanTTConsistent_of`'s hypothesis `H` is jointly contradictory with its `hκ`.**  So
the vacuity is in the uniform quantification over `VEnv.WF' ∧ noUnsafe`, not in §7's
packaging of it. -/
theorem not_modelFits_uniform (hκ : ∀ m : ℕ, IsInaccessibleChain m κ) :
    ¬ ∀ (env : VEnv) (ds : List VDecl), VEnv.WF' ds env → (∀ d ∈ ds, d.noUnsafe) →
      ModelFits κ env ds :=
  fun H ↦ not_modelFits_badAx hκ (H badEnv [.axiom badAx] badAx_history badAx_noUnsafe)

end Refute

/-- **Row 11b, witnessed.**  `ModelFitsInput` is false as soon as `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` is
consistent and `InaccModelInput` turns that into a model — i.e. exactly when
`upper_bound_of` has anything to say.  So `upper_bound_of` is a vacuous reduction. -/
theorem not_modelFitsInput (hA : InaccModelInput)
    (hc : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰) : ¬ ModelFitsInput :=
  hA (¬ ModelFitsInput) (fun _ _ _ _ _ κ hκ hB ↦
    not_modelFits_badAx hκ
      (hB _ κ hκ ModelFitsAudit.badEnv [.axiom ModelFitsAudit.badAx]
        ModelFitsAudit.badAx_history ModelFitsAudit.badAx_noUnsafe)) hc

/-- The same with `InaccModelInput` replaced by the chain-free input of
`InaccChainOmega.lean`: model existence alone already refutes `ModelFitsInput`. -/
theorem not_modelFitsInput_of_modelExists (h : ModelExistsInput)
    (hc : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰) : ¬ ModelFitsInput :=
  not_modelFitsInput (inaccModelInput_of_modelExists h) hc

/-! ## 3. The repair: quantify over Lean histories, which is what the target needs -/

/-- `ds` is a *Lean* history: the standard prelude, then `isPure` steps only.  Exactly the
list-side half of `VEnv.LeanWF`. -/
def PureOverPrelude (ds : List VDecl) : Prop :=
  ∃ ds' : List VDecl, ds = ds' ++ leanPrelude.reverse ∧ ∀ d ∈ ds', d.isPure

/-- **Nothing is given away.**  `VEnv.LeanWF` is precisely the conjunction of the two
hypotheses the narrowed input takes. -/
theorem leanWF_iff {env : VEnv} :
    env.LeanWF ↔ ∃ ds, VEnv.WF' ds env ∧ PureOverPrelude ds := by
  constructor
  · exact fun ⟨ds, hwf, hp⟩ ↦ ⟨_, hwf, ds, rfl, hp⟩
  · rintro ⟨_, hwf, ds', rfl, hp⟩
    exact ⟨ds', hwf, hp⟩

theorem noUnsafe_of_pureOverPrelude {ds : List VDecl} (h : PureOverPrelude ds) :
    ∀ d ∈ ds, d.noUnsafe := by
  obtain ⟨ds', rfl, hp⟩ := h
  intro d hd
  rcases List.mem_append.1 hd with hd | hd
  · exact VDecl.isPure.noUnsafe (hp d hd)
  · exact leanPrelude_noUnsafe d (List.mem_reverse.1 hd)

section Repair

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **The reduction, re-run at the narrowed input.**  Word for word
`CnstRecursion.leanTTConsistent_of` with `noUnsafe` strengthened to `PureOverPrelude`;
the proof is the same, because `leanTTConsistent`'s own quantifier already supplies it. -/
theorem leanTTConsistent_of_lean (κ : ℕ → V) (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (H : ∀ (env : VEnv) (ds : List VDecl), VEnv.WF' ds env → PureOverPrelude ds →
      ModelFits κ env ds) :
    leanTTConsistent := by
  intro env hlw
  obtain ⟨ds, hwf, hp⟩ := leanWF_iff.1 hlw
  obtain ⟨ls, L, o, R, hS, hR, hRd, hfits⟩ := H env ds hwf hp
  exact consistent_of hκ L o hS hR hRd hwf (noUnsafe_of_pureOverPrelude hp) hfits

end Repair

/-- **Input B, narrowed.**  `ModelFitsInput` with `noUnsafe` replaced by
`PureOverPrelude`. -/
def ModelFitsLeanInput : Prop :=
  ∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
    (κ : ℕ → V), (∀ m : ℕ, IsInaccessibleChain m κ) →
    ∀ (env : VEnv) (ds : List VDecl), VEnv.WF' ds env → PureOverPrelude ds →
      ModelFits κ env ds

/-- **§7, reassembled at the narrowed input.**  Replaces `upper_bound_of`. -/
theorem upper_bound_of_lean (hA : InaccModelInput) (hB : ModelFitsLeanInput) :
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent := fun hc ↦
  hA leanTTConsistent (fun V _ _ _ _ κ hκ ↦ leanTTConsistent_of_lean κ hκ (hB V κ hκ)) hc

/-- …and with `hκ` discharged by `InaccChainOmega.lean`, so that the *whole* model-side
input is `ModelExistsInput` (pure completeness, chain-free) plus `ModelFitsLeanInput`. -/
theorem upper_bound_of_omega (hA : ModelExistsInput) (hB : ModelFitsLeanInput) :
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent :=
  upper_bound_of_lean (inaccModelInput_of_modelExists hA) hB

/-! ## 4. The repair is not a dodge, and it is not a trivialisation -/

/-- **The witness is excluded** — by length alone, `[.axiom badAx]` is no Lean history. -/
theorem not_pureOverPrelude_badAx : ¬ PureOverPrelude [.axiom ModelFitsAudit.badAx] := by
  rintro ⟨ds', he, -⟩
  have := congrArg List.length he
  simp [leanPrelude] at this

/-- **And the route is closed in general**: every `.axiom` in a Lean history is one of the
prelude's three.  So no re-run of §2's argument at a different axiom is available; a
refutation of `ModelFitsLeanInput` would have to refute one of `propext`,
`Classical.choice`, `Quot.sound`, or an `.induct`/`.quot` obligation. -/
theorem axiom_mem_pureOverPrelude {ds : List VDecl} {ci : VConstVal}
    (h : PureOverPrelude ds) (hm : VDecl.axiom ci ∈ ds) :
    ci = propextConst ∨ ci = choiceConst ∨ ci = quotSoundConst := by
  obtain ⟨ds', rfl, hp⟩ := h
  rcases List.mem_append.1 hm with hd | hd
  · exact absurd (hp _ hd) id
  · have := List.mem_reverse.1 hd
    simp only [leanPrelude, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h | h | h | h
    · nomatch h
    · nomatch h
    · injection h with h; subst h; tauto
    · nomatch h
    · injection h with h; subst h; tauto
    · nomatch h
    · injection h with h; subst h; tauto

/-- **Not trivially true.**  The prelude is itself a Lean history, and it carries three
`.induct` steps, so `ModelFitsLeanInput` still contains the `.induct` residual and the
prelude's own axiom obligations.  Narrowing the quantifier removed the refutation, not the
content. -/
theorem pureOverPrelude_prelude : PureOverPrelude leanPrelude.reverse :=
  ⟨[], by simp, nofun⟩

theorem induct_mem_prelude : VDecl.induct eqIndDecl ∈ leanPrelude.reverse := by
  simp [leanPrelude]

end Lean4Lean.SetModel
