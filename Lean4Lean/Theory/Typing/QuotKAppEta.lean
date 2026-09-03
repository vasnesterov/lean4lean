import Lean4Lean.Theory.Typing.PatAppParams
import Lean4Lean.Theory.Typing.KEtaDiamond
import Lean4Lean.Theory.Typing.DescendConstSpineK

/-!
# The `keta` case of `ParRedK.constApp_inv` IS reachable inside `Theory/` — `hole-free`

**This file exists because a claim in the tree is wrong, and the wrong claim is load-bearing.**

`Theory/Typing/DescendConstSpineK.lean`'s `propLoop_no_etaK` carries this docstring:

> `EtaK` fires only where an `.app` pattern is registered (`EtaK.matches_head`), and **every
> `Params` instance in `Theory/` has a δ-only table** — `refNoPat`, `cycNoPat`, and
> `propLoopParams`' explicit table … the first instance that would test it is
> `Verify/QuotAppParams.lean`'s `quotParams`, which `Theory/` may not import.

The *theorem* `propLoop_no_etaK` is true — it is a statement at `propLoopParams` alone.  Its
**docstring is false**, and so is the sequencing advice built on it (that file's §6 item 1, and
`docs/handoff-descend.md` §3.1).  The enumeration is missing a fourth `Theory/` instance:
`Theory/Typing/PatAppParams.lean`'s **`appParams`** (`:221`), which registers **two `.app`
patterns** (`appParams_pat_app`, `appParams_pat_app2`), is `VEnv.WF`-backed (`cycEnv_wf`), and —
unlike `quotParams` — carries **no holes at all**.  Its own header says so in the first line:
"`appParams`: the first `Params` instance that registers `.app` patterns".

So the check that was believed to need `Verify/` runs here, one import away, `sorryAx`-free.  It
is a `Theory/` file and imports nothing from `Verify/`.

## Naming

The file is called `QuotKAppEta` rather than `AppKEta` only because this round's ownership rule
restricted new files to the `QuotK` prefix.  Nothing in it is about the quotient rule; the
`quotParams` half of the round is `Verify/Typing/QuotKEta.lean`.

## What is measured here, and what it is *not* evidence of

At `appParams`:

| fact | name |
| --- | --- |
| `EtaK` is **inhabited** — hole-free | `appParams_etaK_here`, `appParams_etaK_stuck` |
| its redex **is** a constant spine, so `constApp_inv`'s `keta` branch is entered | `cycG_mkApp`, `appStuck_mkApp` |
| the branch's hypothesis **fails** at that head | `appParams_not_patFreeHead` |
| and it must: without the hypothesis the lemma is **false**, through `keta` alone | `appParams_keta_refutes_unhypothesised` |
| the hypothesis still holds at every other head, and the lemma fires there | `appParams_patFreeHead`, `appParams_constApp_inv_fires` |

`appParams_keta_refutes_unhypothesised` is the sharpest form of the control: it takes
`ParRedK.constApp_inv`'s statement **with `PatFreeHead` deleted** and derives `False` from it.
The witness is `KStep.stuck_fires`' redex `C (.bvar 0)` — a `C`-headed spine whose single
argument is a *variable*, reducing by `K⁺` to `C D2`.  A variable parallel-reduces only to
itself (`appParams_parRedK_bvar`, whose `keta` case is `EtaK.not_bvar`), so the argument-wise
`Forall₂` the conclusion demands cannot hold.

**What this is not.**  It is **not** evidence that a real Lean environment reaches the `keta`
case, and it must not be quoted as such.  `Params` constrains its table only in one direction
(`extra_pat`: every rule of `env` is registered), so a `Params` instance may register patterns
the environment has no rule for — and `appParams` does exactly that: `cycEnv` carries **no
defeq at all** (`AppPat.extra` is discharged by `cycEnv_no_defeqs`), while `AppPat` claims the
two rules `C D ⟶ C D2` and `C D2 ⟶ C D`.  That is a legitimate instance and an **artificial rule
table**.  The witness at the *canonical* table — the real `Quot.lift`/`Quot.mk` rule of a real
`Environment` — is `Verify/Typing/QuotKEta.lean`, and it costs the `PiInv` hole.  The two
together are the honest reading: hole-free at an artificial table, canonical but hole-tainted at
the real one.

## Axioms

Everything below measures `[propext, Classical.choice, Quot.sound]` or less, with an empty hole
cone — `Classical.choice` enters through `cycEnv_wf.ordered`, exactly as `PatAppParams.lean`'s
header records for its own declarations.  Readings are in `docs/handoff-quotk.md`.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

/-! ## 1. The redexes are constant spines

`constApp_inv`'s `keta` branch is entered only for a term that is syntactically
`(VExpr.const c ls).mkApp as`.  These are `rfl`s. -/

theorem cycG_mkApp : cycG = (VExpr.const `C []).mkApp [.const `D []] := rfl
theorem cycG2_mkApp : cycG2 = (VExpr.const `C []).mkApp [.const `D2 []] := rfl

/-- `KStep.stuck_fires`' redex, as a spine.  Its single argument is a **variable**, which is what
makes it a counterexample rather than merely a witness. -/
theorem appStuck_mkApp :
    (VExpr.app (.const `C []) (.bvar 0)) = (VExpr.const `C []).mkApp [.bvar 0] := rfl

theorem cycQ_headConst : cycQ.headConst = `C := rfl
theorem cycQ2_headConst : cycQ2.headConst = `C := rfl

section
attribute [local instance] appParams

/-! ## 2. `EtaK` is inhabited in `Theory/`, hole-free -/

/-- **`EtaK` is inhabited at a `Theory/` instance**, in one line from `PatAppParams.lean`.

**Credit, and the sharper form of the correction above:** this is *not* the tree's first concrete
`EtaK` inhabitant.  `Theory/Typing/KEtaDiamond.lean:276` has carried
`appParams_etaK_under : EtaK [] (.const `C []) (.lam (.const `P []) cycG2)` since **2026-09-01**,
two days *before* `DescendConstSpineK.lean` landed the claim that no `Theory/` instance can reach
the `keta` case — and `KEta.lean:881`'s own docstring points straight at it.  So §3.1 of
`docs/handoff-descend.md` was refuted at the moment it was written, by a file in the same
directory and in the same `EtaK` programme.  `appParams_keta_refutes_unhypothesised_pre` below
shows that pre-existing witness alone settles the question. -/
theorem appParams_etaK_here : EtaK [] cycG cycG2 := .here appParams_kstep_toD2

/-- The witness this file adds, and why it is worth adding beside
`KEtaDiamond.appParams_etaK_under`: the `K⁺` step at a **stuck** redex, whose argument is a
*variable*.  The pre-existing witness violates `constApp_inv`'s conclusion by *shape* (its reduct
is a `.lam`, so `VExpr.constApp_ne_lam` closes it); this one violates it *argument-wise*, at the
same head and arity, which is the case a shape-only guard would miss. -/
theorem appParams_etaK_stuck :
    EtaK appCtx ((VExpr.const `C []).mkApp [.bvar 0]) cycG2 :=
  .here appParams_stuck_fires.2

/-- …hence a `ParRedK` derivation whose only step is the ninth constructor. -/
theorem appParams_parRedK_keta :
    ParRedK appCtx ((VExpr.const `C []).mkApp [.bvar 0]) cycG2 :=
  .keta_step appParams_etaK_stuck

/-! ## 3. The hypothesis, both ways -/

/-- The rule head is not rule-free. -/
theorem appParams_not_patFreeHead : ¬ PatFreeHead `C := fun h => h _ _ AppPat.d cycQ_headConst

/-- Every other head is.  Both registered patterns have head `C`, so this is exact. -/
theorem appParams_patFreeHead {c : Lean.Name} (hc : c ≠ `C) : PatFreeHead c := by
  intro p r h
  cases h
  · exact fun h' => hc (cycQ_headConst ▸ h').symm
  · exact fun h' => hc (cycQ2_headConst ▸ h').symm

/-! ## 4. The control: without `PatFreeHead` the lemma is false through `keta` alone -/

/-- A variable parallel-reduces only to itself.  The `keta` case is `EtaK.not_bvar`; the `extra`
case dies because both registered patterns are `.app`, and `Pattern.Matches` has no `.bvar`. -/
theorem appParams_parRedK_bvar {Γ : List VExpr} {i : Nat} {o : VExpr}
    (h : ParRedK Γ (.bvar i) o) : o = .bvar i := by
  cases h with
  | bvar => rfl
  | extra hp hm _ _ => cases hp <;> nomatch hm
  | keta hη _ => exact absurd hη EtaK.not_bvar

/-- **Anti-strawman.**  The hypothesis of `appParams_keta_refutes_unhypothesised` is
`ParRedK.constApp_inv`'s statement with `hc` and nothing else removed: here is the *hypothesised*
statement, written out in the same shape and proved **by** `ParRedK.constApp_inv`. -/
theorem appParams_constApp_inv_statement_holds :
    ∀ {Γ : List VExpr} {c : Lean.Name}, PatFreeHead c →
      ∀ {ls : List VLevel} {as : List VExpr} {e' : VExpr},
      ParRedK Γ ((VExpr.const c ls).mkApp as) e' →
      ∃ as', e' = (VExpr.const c ls).mkApp as' ∧ List.Forall₂ (ParRedK Γ) as as' := by
  intro Γ c hc ls as e' H
  exact ParRedK.constApp_inv hc H

/-- **`ParRedK.constApp_inv` with its hypothesis deleted is FALSE, and the `keta` constructor is
what refutes it.**  `propLoop_constApp_inv_needs_hyp` is the same control for the `extra`
constructor; this is the one the `keta` case needed and no instance in the tree could give.

The `extra` constructor also refutes the hypothesis-free statement at this instance, and
`propLoop_constApp_inv_needs_hyp` already refutes it that way at `propLoopParams`; the content
here is that the **ninth** constructor independently requires the hypothesis, so a repair that
guarded `extra` alone would not save the lemma.

Per `ForallInvPrice.lean`'s discipline: this refutes the *hypothesis-free* statement, not
`ParRedK.constApp_inv`.  The instance is legitimate (`cycEnv_wf`), the table is non-empty
(`AppPat.d`), and `PatFreeHead `C`` simply fails here (`appParams_not_patFreeHead`), while it
holds at every other head (`appParams_patFreeHead`). -/
theorem appParams_keta_refutes_unhypothesised
    (H : ∀ {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {e' : VExpr},
      ParRedK Γ ((VExpr.const c ls).mkApp as) e' →
      ∃ as', e' = (VExpr.const c ls).mkApp as' ∧ List.Forall₂ (ParRedK Γ) as as') : False := by
  obtain ⟨as', he, hf⟩ := H appParams_parRedK_keta
  cases hf with
  | cons h1 h2 =>
    cases h2
    obtain rfl := appParams_parRedK_bvar h1
    simp [VExpr.mkApp] at he

/-- **The tree could have run this check on 2026-09-01.**  The same refutation from
`KEtaDiamond.appParams_etaK_under` alone: its subject `.const `C []` is the spine
`(.const `C []).mkApp []`, its reduct is a `.lam`, and `VExpr.constApp_ne_lam` (already in
`PatKHead.lean`) closes it.  Three lines, no new witness, no `Verify/` import.

This is the measurement `DescendConstSpineK.lean` §3, `docs/handoff-descend.md` §3.1 and this
round's own brief all said was unreachable from `Theory/`. -/
theorem appParams_keta_refutes_unhypothesised_pre
    (H : ∀ {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {e' : VExpr},
      ParRedK Γ ((VExpr.const c ls).mkApp as) e' →
      ∃ as', e' = (VExpr.const c ls).mkApp as' ∧ List.Forall₂ (ParRedK Γ) as as') : False := by
  obtain ⟨as', he, -⟩ := H (as := []) (ParRedK.keta_step appParams_etaK_under)
  exact VExpr.constApp_ne_lam he.symm

/-! ## 5. The theorem itself still fires here -/

/-- A spine on a rule-free head with a β-redex inside it really reduces. -/
theorem appParams_parRedK_pSpine :
    ParRedK [] ((VExpr.const `P []).mkApp
        [.app (.lam (.const `P []) (.bvar 0)) (.const `D [])])
      ((VExpr.const `P []).mkApp [.const `D []]) :=
  .app .const (.beta .bvar .const)

/-- **Positive control.**  At a rule-free head the lemma applies to a reduction that moves, so
`appParams` is not an instance where `constApp_inv` is vacuous for want of reductions — only its
`keta` branch is, and `keta_branch_unreachable` (`Verify/Typing/QuotKEta.lean`) says that is a
theorem rather than a gap. -/
theorem appParams_constApp_inv_fires :
    ∃ as', ((VExpr.const `P []).mkApp [.const `D []]) = (VExpr.const `P []).mkApp as' ∧
      List.Forall₂ (ParRedK []) [.app (.lam (.const `P []) (.bvar 0)) (.const `D [])] as' :=
  ParRedK.constApp_inv (appParams_patFreeHead (by decide)) appParams_parRedK_pSpine

/-- Instance-level vacuity, the sharp form: `EtaK` is inhabited here, and still fires at no spine
on a rule-free head. -/
theorem appParams_no_etaK_at_patFree {Γ : List VExpr} {c : Lean.Name} (hc : c ≠ `C)
    {ls : List VLevel} {as : List VExpr} {e' : VExpr} :
    ¬ EtaK Γ ((VExpr.const c ls).mkApp as) e' :=
  fun h => EtaK.constApp_free (appParams_patFreeHead hc) h

end

end VEnv

end Lean4Lean
