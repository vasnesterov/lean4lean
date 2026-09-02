import Lean4Lean.Theory.SetModel.EqRecLarge

/-!
# The shared witness at the three recursor cells: which fail, and what a repair costs

`EqRecLarge.lean` §8 established that `SetModel.preludeWitness` — the *joint* witness for
`EqSpec`/`IffSpec`/`NonemptySpec`, and the assignment `PreludeOracle.lean` uses **byte for byte**
as its oracle (`NEAudit.neOracle`) — **fails** `InductOracleOK`'s `consts` cell at `Eq.rec` on the
`u.eval ls ≠ 0` slice, because its entry there is `•` and `•` is excluded.

This file answers the three questions that decides what to do about it.

1. **Does the same gap hit `Iff.rec` and `Nonempty.rec`?**  §1: `Iff.rec` **yes**, and it is now
   machine-checked rather than reasoned.  §2: `Nonempty.rec` **no**, and that is not an accident —
   `nonemptyIndDecl.isLE = false` (`NEAudit.ne_isLE`), so there is no elimination universe to
   branch on and `•` is the *correct* value, already proved
   (`NEAudit.pt_mem_interp_NE_recType`).  So the repair is **two cells, not three**.
2. **What would the witness have to become?**  §3 exhibits it: `preludeWitnessR`, identical to
   `preludeWitness` except that `Eq.rec` gets `EqLargeAudit.eqRecVal`.  §4 re-proves, at
   `preludeWitnessR`, every statement about `preludeWitness` that the change touches, so the
   cost is **measured by running it** rather than estimated.
3. **Does anything depend on the recursor entries being `•`?**  §5: one thing does, and it is
   named — `NEAudit.neOracle_eq_empty_of_not_mem`, whose statement is *refuted* by the repair
   and which `NEAudit.cnstOf_preludeTail` consumes.  §5 shows the repaired shape and that the
   two extra hypotheses it needs are available at the one use site.

**What this file does not do.**  It does not edit `PreludeSpec.lean`.  The reason is not caution,
it is an **import cycle**, measured off `grep ^import`: `eqRecFn` is defined in `EqRecLarge.lean`,
which sits seven files downstream of `PreludeSpec.lean`
(`PreludeSpec ← PreludeOracle ← IffOracle ← EqOracle ← EqZeroSlice ← EqTypeFormer ←
EqRecNecessity ← EqRecLarge`).  Putting `eqRecVal` into `preludeWitness` therefore requires
*relocating* the whole six-layer `mkLam` nest (`EqLargeAudit.motSet`, `lamH`, `lamB`, `lamM`,
`lamF`, `lamA`, `eqRecFn` and the three definability lemmas of `EqRecLarge` §2) up into
`PreludeSpec.lean` first.  Nothing in those definitions needs anything `PreludeSpec.lean` does
not already import — they use only `mkLam`, `mkForallType`, their `_definable` lemmas
(`Definability.lean`) and `eqFn` (`PreludeSpec.lean` itself) — so the relocation is mechanical;
but it is a relocation, and it is the reason the repair is not a one-line edit.
-/

namespace Lean4Lean.SetModel.RecGap

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

/-! ## 1. `Iff.rec`: the same gap, now measured

`PreludeOracle.lean` §13 records `preludeWitness_iffRec_empty` (the entry is `∅`) and says in
its own docstring: "*This is a fact about the assignment, not yet a refutation of
`InductOracleOK` at those blocks*".  It is now a refutation.

The cost was **one rewrite**: `IffAudit.pt_not_mem_interp_iffRecType_of_ne` already exists and,
unlike its `Eq` and `Unit` counterparts, carries **no** hypothesis about an inhabitant of any
parameter space — `Iff`'s outermost recursor binder is a parameter over `Prop` and `∅ ∈ U κ 0`
holds at every `κ`.  So the `Iff.rec` refutation is strictly *cheaper* than the `Eq.rec` one. -/

section IffGap

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

variable {u : VLevel} (hu : u.WF nv) (hle : iffEnv ≤ envF)

include hu hle in
/-- **The `Iff.rec` cell FAILS at the pre-repair assignment on the `≠ 0` slice** — the twin of
`EqLargeAudit.preludeWitnessPt_not_mem_interp_eqRecType`, and with one hypothesis fewer (no
parameter-space inhabitant).

Stated at `SetModel.preludeWitnessPt`.  When this section was written that assignment *was*
`preludeWitness`; the repair this file prices has since been performed in `PreludeSpec.lean`, and
the pre-repair assignment is preserved there under the new name precisely so this refutation keeps
a subject.  `preludeWitnessPt` is not a straw man: it meets all three prelude specifications and
agrees with the repaired witness at all three type formers. -/
theorem preludeWitnessPt_not_mem_interp_iffRecType (hn : u.eval ls ≠ 0) :
    (preludeWitnessPt (V := V) κ ls).cnst ``Iff.rec [u] ∉
      (interp (preludeWitnessPt κ ls) L [] ((iffIndDecl.recType 0).instL [u])).toFun ∅ := by
  rw [preludeWitnessPt_cnst_iffRec]
  exact IffAudit.pt_not_mem_interp_iffRecType_of_ne L (preludeWitnessPt κ ls) hu hle hn

/-! The positive half — that the *repaired* `preludeWitness` passes this cell — cannot be stated
here: it needs `IffLargeAudit.iffRecFn_mem_interp_iffRecType`, and `IffRecLarge.lean` imports this
file.  It is `IffLargeAudit.preludeWitness_mem_interp_iffRecType`. -/

end IffGap

/-! ## 2. `Nonempty.rec`: **no gap**, and not by luck

The brief's third cell was flagged as *reasoning, not a run*.  Measured, it is not a gap at all,
and the reason is already `rfl` in the tree: `NEAudit.ne_isLE : nonemptyIndDecl.isLE = false` and
`NEAudit.ne_elimLvl : nonemptyIndDecl.elimLvl = .zero`.  A small eliminator has **no elimination
universe to branch on** — `recUvars = 1` and the one level is the block's own — so
`Nonempty.rec`'s whole type is a proposition at *every* instantiation and `•` is the correct
value, unconditionally in `u`.  `NEAudit.pt_mem_interp_NE_recType` proves it; all that is needed
here is to say it at the shared witness rather than at `NEAudit.neM`, which is the same object
(`NEAudit.neM_eq`, `rfl`).

**So the repair is two cells (`Eq.rec`, `Iff.rec`), not three.**

*Where the anti-vacuity control stands at this cell.*  The `EqRecNec.recCell_discriminates` form —
one parameter tuple, membership at the good witness and failure at a bad one — is **not**
available here and cannot be, in the form "a bad *value*": the type is a proposition, so
`mem_interp_forallE_prop_iff` makes every member of the interpretation equal to `•`, and excluding
any `w ≠ •` is free.  The informative control has to vary the *model*, and at this block that
control is **prose**: `PreludeOracle.lean:905` asserts "a constant-true `Nonempty` satisfies the
constructor and fails here", and the machine-checked analogue of
`EqRecNec.not_pt_mem_interp_eqRecType_badTrue` at `nonemptyIndDecl` **does not exist**.  What does
exist, and is a run, is the faithfulness the cell consumes: `NEAudit.nonemptyFn_zero_empty` and
`NEAudit.nonemptyFn_zero_true` pin both branches of the squash at `U₀`. -/

section NEGap

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

theorem preludeWitness_cnst_neRec (us : List VLevel) :
    (preludeWitness (V := V) κ ls).cnst ``Nonempty.rec us = (pt : V) := by
  simp [preludeWitness, pt]

variable {u : VLevel} (hu : u.WF nv) (hle : nonemptyEnv ≤ envF)

include hu hle in
/-- **The `Nonempty.rec` cell HOLDS at `preludeWitness`, at every level** — no branch, no side
condition.  Contrast §1 and `EqLargeAudit.preludeWitness_not_mem_interp_eqRecType`, both of which
are refutations on a `≠ 0` slice that this block does not have. -/
theorem preludeWitness_mem_interp_neRecType :
    (preludeWitness (V := V) κ ls).cnst ``Nonempty.rec [u] ∈
      (interp (preludeWitness κ ls) L [] ((nonemptyIndDecl.recType 0).instL [u])).toFun ∅ := by
  rw [preludeWitness_cnst_neRec, ← NEAudit.neM_eq]
  exact NEAudit.pt_mem_interp_NE_recType L κ ls hu hle

end NEGap

/-! ## 3. The repaired witness

What `preludeWitness` has to become for its `Eq.rec` entry to be `eqRecFn` on the `≠ 0` branch
and `•` on the `= 0` branch is exactly this: one more `if` arm, holding
`EqLargeAudit.eqRecVal κ ls`, which is itself
`fun | [u, v] => if u.eval ls = 0 then • else eqRecFn κ (u.eval ls) (v.eval ls) | _ => ∅`.
The brief guessed that shape and the guess is right.

`Iff.rec` is **not** repaired here, and this is the second half of the answer to "how much does
the fix cost": there is no `iffRecFn` anywhere in the tree (checked by `grep` over
`Lean4Lean/**.lean`; `lean_local_search` is broken in this environment).  §1 refutes the
`Iff.rec` cell but nothing yet *satisfies* it, so its arm cannot be written.  See §6 for what
building `iffRecFn` costs.

`preludeWitnessR` is a **measuring instrument**, not a replacement: it lives downstream so that
the census in §4 can be run.  The real edit is the relocation described in the file header. -/

section Repaired

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **`preludeWitness` with a level-branching `Eq.rec` entry.**  Identical to `preludeWitness` in
its first three arms and in its fallback. -/
noncomputable def preludeWitnessR (κ : ℕ → V) (ls : List ℕ) : ModelData V where
  κ := κ
  ls := ls
  cnst := fun n us ↦
    if n = ``Eq then (match us with | [w] => eqFn κ (w.eval ls) | _ => ∅)
    else if n = ``Iff then (match us with | [] => (iffFn : V) | _ => ∅)
    else if n = ``Nonempty then (match us with | [w] => nonemptyFn κ (w.eval ls) | _ => ∅)
    else if n = ``Eq.rec then EqLargeAudit.eqRecVal κ ls us
    else ∅

end Repaired

/-! ## 4. The census, **measured**: what the repair costs

Every statement below is an existing result about `preludeWitness`, restated at
`preludeWitnessR` with the **same proof term**, so the entries marked *verbatim* are measured
transfers rather than estimates.  The count:

| existing result | file | verdict |
|---|---|---|
| `SetModel.preludeWitness_eq` | `PreludeSpec` | verbatim |
| `SetModel.preludeWitness_iff` | `PreludeSpec` | verbatim |
| `SetModel.preludeWitness_nonempty` | `PreludeSpec` | verbatim |
| `SetModel.preludeSpec_satisfiable` | `PreludeSpec` | verbatim |
| `EqTFAudit.preludeWitness_cnst_eq` | `EqTypeFormer` | verbatim, still `rfl` |
| `EqTFAudit.preludeWitness_congr_Eq` | `EqTypeFormer` | verbatim |
| `EqTFAudit.mem_interp_EqType_preludeWitness` | `EqTypeFormer` | verbatim |
| `EqTFAudit.oracleOK_Eq` | `EqTypeFormer` | verbatim |
| `NEAudit.neOracle_NE` / `_intro` / `_rec` | `PreludeOracle` | proof needs no change (`simp`) |
| `NEAudit.neM_eq` | `PreludeOracle` | **definitional; `neOracle` becomes the repaired one** |
| `EqLargeAudit.preludeWitness_mem_interp_eqRecType_of_zero` | `EqRecLarge` | statement survives, **one extra rewrite** |
| `NEAudit.preludeWitness_eqRec_empty` | `PreludeOracle` | **REFUTED** — replaced by §4.2 |
| `NEAudit.neOracle_eq_empty_of_not_mem` | `PreludeOracle` | **REFUTED** — needs one more hypothesis (§5) |
| `EqLargeAudit.preludeWitness_cnst_eqRec` | `EqRecLarge` | **REFUTED** — replaced by §4.2 |
| `EqLargeAudit.preludeWitness_not_mem_interp_eqRecType` | `EqRecLarge` | **REMOVED, not repaired** (§4.4) |

So: **four statements refuted or removed, one proof needing an extra step, everything else
verbatim.**  `NEAudit.preludeWitness_iffRec_empty` and §1's theorems are *unaffected* by this
repair, because it does not touch the `Iff.rec` arm.

### 4.1 The three specifications transfer verbatim

This is the answer to "which become easier": none of the three gets easier, but none gets harder
either, and that is the point — `EqSpec`/`IffSpec`/`NonemptySpec` read `M.cnst` only at `Eq`,
`Iff` and `Nonempty`, so an arm added *after* those three is invisible to them.  Each proof below
is byte-for-byte `PreludeSpec.lean`'s. -/

section Census

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

theorem preludeWitnessR_eq (κ : ℕ → V) (ls : List ℕ) (u : VLevel) :
    EqSpec (preludeWitnessR κ ls) u := fun _ hα _ ha _ hb ↦ eqFn_value hα ha hb

theorem preludeWitnessR_iff (κ : ℕ → V) (ls : List ℕ) :
    IffSpec (preludeWitnessR κ ls) := fun _ hp _ hq ↦ iffFn_value hp hq

theorem preludeWitnessR_nonempty (κ : ℕ → V) (ls : List ℕ) (u : VLevel) :
    NonemptySpec (preludeWitnessR κ ls) u := fun _ hα ↦ nonemptyFn_value hα

/-- `preludeSpec_satisfiable`, verbatim, at the repaired witness. -/
theorem preludeSpecR_satisfiable (κ : ℕ → V) (ls : List ℕ) :
    ∃ M : ModelData V, M.κ = κ ∧ M.ls = ls ∧
      (∀ u, EqSpec M u) ∧ IffSpec M ∧ (∀ u, NonemptySpec M u) :=
  ⟨preludeWitnessR κ ls, rfl, rfl, preludeWitnessR_eq κ ls,
    preludeWitnessR_iff κ ls, preludeWitnessR_nonempty κ ls⟩

/-- `EqTFAudit.preludeWitness_cnst_eq` is `rfl` at `preludeWitness`; **it is still `rfl` here.**
That is the one thing the added arm could plausibly have broken (the type-former cell needs the
value's *identity*, not just its applied values — `EqTFAudit.eqSpec_not_sufficient`), and it does
not: the `Eq` test is the first arm, so the new one never enters the reduction. -/
theorem preludeWitnessR_cnst_eq (κ : ℕ → V) (ls : List ℕ) (w : VLevel) :
    (preludeWitnessR (V := V) κ ls).cnst ``Eq [w] = eqFn κ (w.eval ls) := rfl

/-! ### 4.2 The two refuted `∅`-statements, in their repaired shape -/

/-- The replacement for `NEAudit.preludeWitness_eqRec_empty` and
`EqLargeAudit.preludeWitness_cnst_eqRec`, both of which are `∀ us, … = ∅ / = •` and are refuted
by the repair. -/
theorem preludeWitnessR_cnst_eqRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitnessR (V := V) κ ls).cnst ``Eq.rec us = EqLargeAudit.eqRecVal κ ls us := by
  simp [preludeWitnessR]

/-- On the `Prop` slice the repaired entry is still `•`, which is why
`EqLargeAudit.preludeWitness_mem_interp_eqRecType_of_zero`'s *statement* survives the repair. -/
theorem preludeWitnessR_cnst_eqRec_zero (κ : ℕ → V) (ls : List ℕ) {u v : VLevel}
    (h0 : u.eval ls = 0) :
    (preludeWitnessR (V := V) κ ls).cnst ``Eq.rec [u, v] = (pt : V) := by
  rw [preludeWitnessR_cnst_eqRec, EqLargeAudit.eqRecVal_pair, if_pos h0]

/-- The `Iff.rec` and `Nonempty.rec` arms are untouched: the repair is *not* a repair of §1. -/
theorem preludeWitnessR_cnst_iffRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitnessR (V := V) κ ls).cnst ``Iff.rec us = (pt : V) := by
  simp [preludeWitnessR, pt]

theorem preludeWitnessR_cnst_neRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitnessR (V := V) κ ls).cnst ``Nonempty.rec us = (pt : V) := by
  simp [preludeWitnessR, pt]

end Census

/-! ### 4.5 The three `EqTypeFormer` consequences, transferred — **run, not reasoned**

`preludeWitnessR_cnst_eq` being `rfl` (§4.1) is what these three rest on, but "rests on" is an
argument; below they are compiled.  `EqTFAudit.mem_interp_EqType_preludeWitness` is the one that
could not have been taken on trust: its statement mentions `interp (preludeWitness κ ls)`, so it is
a statement about the *whole* assignment and not only about the `Eq` arm. -/

section TypeFormerTransfer

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-- **The one row of the census that does NOT transfer verbatim**, and the only one found by
running rather than by reading.  `EqTFAudit.preludeWitness_congr_Eq`'s proof is

```lean
  rcases hd with _ | ⟨h, ht⟩
  · rfl
  rcases ht with _ | ⟨h2, ht2⟩
  · rw [preludeWitness_cnst_eq, preludeWitness_cnst_eq, VLevel.equiv_def.mp h ls]
  · rfl
```

and at `preludeWitnessR` the **last `rfl` hits a `(kernel) deterministic timeout`** — not an
elaboration timeout: the declaration elaborates and `#print axioms` reports it clean, and then the
kernel rejects it.  The degenerate branch (`us` of length ≥ 2, both sides `∅`) is the one that
blows up, because closing it by `rfl` asks the kernel to whnf the whole `if`-cascade including the
new arm's body.  The fix is to name the `Eq` arm once, by `simp`, and never let `rfl` see the
cascade — after which the branch closes by `rw`'s own `rfl`. -/
theorem preludeWitnessR_cnst_Eq_arm (us : List VLevel) :
    (preludeWitnessR (V := V) κ ls).cnst ``Eq us
      = (match us with | [w] => eqFn κ (w.eval ls) | _ => (∅ : V)) := by
  simp [preludeWitnessR]

theorem preludeWitnessR_congr_Eq {us us' : List VLevel}
    (hd : List.Forall₂ (· ≈ ·) us us') :
    (preludeWitnessR (V := V) κ ls).cnst ``Eq us
      = (preludeWitnessR (V := V) κ ls).cnst ``Eq us' := by
  rcases hd with _ | ⟨h, ht⟩
  · rfl
  rcases ht with _ | ⟨h2, ht2⟩
  · rw [preludeWitnessR_cnst_eq, preludeWitnessR_cnst_eq, VLevel.equiv_def.mp h ls]
  · rw [preludeWitnessR_cnst_Eq_arm, preludeWitnessR_cnst_Eq_arm]

theorem mem_interp_EqType_preludeWitnessR {v : VLevel} (hv : v.WF nv) (hle : eqEnv ≤ envF) :
    (preludeWitnessR (V := V) κ ls).cnst ``Eq [v] ∈
      (interp (preludeWitnessR κ ls) L [] (EqTFAudit.eqTypeFormerType v)).toFun ∅ := by
  rw [preludeWitnessR_cnst_eq]
  exact EqTFAudit.eqFn_mem_interp_EqType hv hle

theorem oracleOK_Eq_preludeWitnessR (hle : eqEnv ≤ envF) :
    OracleOK L κ ls (preludeWitnessR κ ls).cnst (preludeWitnessR κ ls).cnst ``Eq
      ⟨1, .forallE (.sort (.param 0))
        (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ :=
  oracleOK_of (L := L)
    (fun _ _ hd ↦ preludeWitnessR_congr_Eq κ ls hd)
    (fun {us} hw hlen ↦ by
      obtain ⟨w, rfl⟩ := NEAudit.eq_singleton_of_length_one hlen
      exact mem_interp_EqType_preludeWitnessR L κ ls (hw w (List.mem_singleton.2 rfl)) hle)

end TypeFormerTransfer

/-! ### 4.3 The payoff: the `Eq.rec` cell at a **single** witness

`EqLargeAudit.oracleOK_EqRec` carries two assignments — an ambient `c` (pinned by `EqSpec`) and a
separate oracle `o` (pinned by `ho : ∀ us, o ``Eq.rec us = eqRecVal κ ls us`) — precisely because
`preludeWitness` could not supply the second.  At `preludeWitnessR` the two collapse: `ho` is
§4.2 and `EqSpec` is §4.1, so the cell is an `OracleOK` at one assignment, in the same shape as
`EqTFAudit.oracleOK_Eq`.  **This is the whole content of the repair**, and it is the deliverable
the corner's assembly needs. -/

section Payoff

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

/-- **`OracleOK` at `Eq.rec`, both level slices, at the repaired shared witness** — no side
oracle parameter, no chain hypothesis, no chosen `κ` (`Above` is discharged by `Above.pure`
inside `oracleOK_of`, so the statement is at an arbitrary `κ : ℕ → V`). -/
theorem oracleOK_EqRec_preludeWitnessR (hle : eqEnv ≤ envF) :
    OracleOK L κ ls (preludeWitnessR κ ls).cnst (preludeWitnessR κ ls).cnst ``Eq.rec
      ⟨eqIndDecl.recUvars, eqIndDecl.recType 0⟩ :=
  EqLargeAudit.oracleOK_EqRec L κ ls hle
    (fun w ↦ preludeWitnessR_eq κ ls w) (preludeWitnessR_cnst_eqRec κ ls)

end Payoff

/-! ### 4.4 `preludeWitness_not_mem_interp_eqRecType` is REMOVED, not repaired

Worth saying plainly, because a costing that lists it as "needs re-proof" is wrong in kind:
`EqLargeAudit.preludeWitness_not_mem_interp_eqRecType` says the shared witness *fails* the cell.
After the repair that statement is **false**, and there is nothing to re-prove — what survives is
`EqAudit.pt_not_mem_interp_eqRecType_of_ne`, a statement about the *value* `•`, which is already
in the tree and is what the refutation was really about.

The discriminating control the trap list demands is then available in the
`EqRecNec.recCell_discriminates` form and at the **actual shared witness** rather than an abstract
value: one `L`, one `M = preludeWitnessR κ ls`, one `(u, v)`, one interpretation — the repaired
entry is in it and `•` (what `preludeWitness` supplies at the same tuple) is not.

Note where each hypothesis goes.  The *positive* half needs no parameter-space inhabitant; the
*exclusion* does (`hx`), and that asymmetry is `EqRecLarge` §7's, unchanged.  So `hx` here is
load-bearing for the negative half only, and no `κ` is chosen: `hx` is a hypothesis about the
given `κ`, not a construction of one. -/

section Discriminate

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

include hu hv hle in
/-- **The repair discriminates.**  At one parameter tuple: the repaired witness' `Eq.rec` entry is
in the interpretation, and `preludeWitness`' entry (`•`) is not. -/
theorem repair_discriminates (hn : u.eval ls ≠ 0) {x : V} (hx : x ∈ U κ (v.eval ls)) :
    (preludeWitnessR (V := V) κ ls).cnst ``Eq.rec [u, v] ∈
        (interp (preludeWitnessR κ ls) L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ ∧
      (preludeWitnessPt (V := V) κ ls).cnst ``Eq.rec [u, v] ∉
        (interp (preludeWitnessR κ ls) L [] ((eqIndDecl.recType 0).instL [u, v])).toFun ∅ := by
  refine ⟨?_, ?_⟩
  · rw [preludeWitnessR_cnst_eqRec, EqLargeAudit.eqRecVal_pair, if_neg hn]
    exact EqLargeAudit.eqRecFn_mem_interp_eqRecType hu hv hle (preludeWitnessR_eq κ ls v) hn
  · rw [preludeWitnessPt_cnst_eqRec]
    exact EqAudit.pt_not_mem_interp_eqRecType_of_ne L (preludeWitnessR κ ls) hu hv hle hn hx

include L hu hv hle in
/-- …and the two entries really are different sets, so the conjunction above is not a statement
about one set under two names. -/
theorem repair_changes_the_value (hn : u.eval ls ≠ 0) {x : V} (hx : x ∈ U κ (v.eval ls)) :
    (preludeWitnessR (V := V) κ ls).cnst ``Eq.rec [u, v]
      ≠ (preludeWitnessPt (V := V) κ ls).cnst ``Eq.rec [u, v] := by
  intro h
  exact (repair_discriminates L κ ls hu hv hle hn hx).2
    (h ▸ (repair_discriminates L κ ls hu hv hle hn hx).1)

end Discriminate

/-! ## 5. The one thing that *depends* on the entries being `∅`

The brief's third question — "is there a reason the witness was `else ∅`, i.e. does anything
*depend* on the recursor entries being `•`?" — has a two-part answer, and the parts point opposite
ways.

**Yes, at `Nonempty.rec`:** `NEAudit.oracleOK_NE_rec` and `NEAudit.mem_interp_consts_NE` both
rewrite with `NEAudit.neOracle_rec : neOracle κ ls recN us = •` and then apply
`NEAudit.pt_mem_interp_NE_recType`.  That is a genuine dependency, it is load-bearing for the one
`.induct` step of the prelude that is discharged today, and §2 says it is *correct* — so it is not
a conflict, it is a constraint: **the fallback must stay `∅` at `Nonempty.rec`.**  Both cells the
repair touches are at other names, so nothing there breaks.

**And one place depends on the *fallback's shape* rather than on any particular entry:**
`NEAudit.neOracle_eq_empty_of_not_mem`, whose statement is

```lean
(h1 : m ≠ ``Eq) (h2 : m ≠ ``Iff) (h3 : m ≠ ``Nonempty) → neOracle κ ls m us = ∅
```

This is **refuted** by the repair, at `m := ``Eq.rec`` and `us := [u, v]` with `u.eval ls ≠ 0`
(§5.2 below is the machine-checked refutation).  Its only consumer is
`NEAudit.cnstOf_preludeTail`, and §5.1/§5.3 show the repaired shape and that the consumer can
supply the extra hypothesis — so this is a **cheap extension, not a conflict**. -/

section Fallback

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-! ### 5.1 The repaired fallback statement -/

/-- `NEAudit.neOracle_eq_empty_of_not_mem` with the one extra hypothesis the repair forces. -/
theorem preludeWitnessR_cnst_empty_of_not_mem (κ : ℕ → V) (ls : List ℕ) {m : Name}
    (h1 : m ≠ ``Eq) (h2 : m ≠ ``Iff) (h3 : m ≠ ``Nonempty) (h4 : m ≠ ``Eq.rec)
    (us : List VLevel) : (preludeWitnessR (V := V) κ ls).cnst m us = (∅ : V) := by
  simp [preludeWitnessR, h1, h2, h3, h4]

/-! ### 5.2 …and `h4` is **necessary**, not defensive

Without it the statement is false.  This is the control that separates "the repair costs one
extra hypothesis" from "the repair costs one extra hypothesis that could have been avoided". -/

section Necessary

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

include L hu hv hle in
/-- **The repaired witness' `Eq.rec` entry is not `∅` on the `≠ 0` slice**, so `h4` above cannot
be dropped.  `hx` is a hypothesis *about the given* `κ` — no `κ` is chosen here, and this is a
negative control, so the three-point scale of `docs/vacuity-ledger.md` applies to it and not to
§4.3's obligation. -/
theorem eqRec_arm_ne_empty (hn : u.eval ls ≠ 0) {x : V} (hx : x ∈ U κ (v.eval ls)) :
    (preludeWitnessR (V := V) κ ls).cnst ``Eq.rec [u, v] ≠ (pt : V) := by
  rw [preludeWitnessR_cnst_eqRec, EqLargeAudit.eqRecVal_pair, if_neg hn]
  exact EqLargeAudit.eqRecFn_ne_pt L (preludeWitnessR κ ls) hu hv hle
    (preludeWitnessR_eq κ ls v) hn hx

end Necessary

/-! ### 5.3 The consumer can supply it

`NEAudit.cnstOf_preludeTail` reaches `neOracle_eq_empty_of_not_mem` in the branch where `m` is in
*none* of the four steps' name lists, and derives each `≠` from the corresponding `∉`.  The same
derivation gives `h4`, because `Eq.rec` **is** one of `eqIndDecl`'s names — measured below.  So the
repair does not obstruct `cnstOf_preludeTail`; it adds one line to its proof. -/

theorem eqRec_mem_eqIndDecl_allNames : ``Eq.rec ∈ eqIndDecl.allNames := by
  simp only [VInductDecl'.allNames, VInductDecl'.allConsts, VInductDecl'.recConsts,
    List.map_append, List.mem_append]
  right
  simp [eqIndDecl]
  rfl

theorem iffRec_mem_iffIndDecl_allNames : ``Iff.rec ∈ iffIndDecl.allNames := by
  simp only [VInductDecl'.allNames, VInductDecl'.allConsts, VInductDecl'.recConsts,
    List.map_append, List.mem_append]
  right
  simp [iffIndDecl]
  rfl

end Fallback

/-! ## 6. What `Iff.rec`'s arm would cost — priced, not built

§1 refutes the `Iff.rec` cell; §3 could not repair it because no `iffRecFn` exists.  Here is the
price, read off the shapes `PreludeOracle.lean` §13 already measured by `rfl`.

* **Five `mkLam` layers**, against `Eq.rec`'s six: `NEAudit.iff_recType` shows two parameters
  (both over `.sort .zero`, i.e. `UProp` — *not* `U κ n`, which is a simplification), the motive,
  one minor premise, the major premise.  `iffIndDecl.recUvars = 1` (`NEAudit.iff_recUvars`), so
  the `if` keys on the single elimination level and `eqRecVal`'s two-element `match` becomes a
  one-element one.
* **A `motSet` analogue that is one layer shallower.**  `Iff`'s block has no index
  (`NEAudit.iff_indices : … = []`), so the motive's domain is a *single* `mkForallType` over
  `⟦Iff a b⟧` rather than `Eq`'s nested pair.  Its inner domain is where `IffSpec` gets spent, as
  `EqLargeAudit.motSet_eq_interp_motTyE` spends `EqSpec`.
* **One genuinely new cost: the minor premise's domain.**  `IffAudit.minTyI` is
  `∀ (mp : a → b), (b → a) → motive (Iff.intro a b mp mpr)` — two nested function spaces and an
  application of the *constructor*, where `Eq`'s minor premise was `motive a (Eq.refl α a)` with
  `Eq.refl` a proof that `interp` discards.  So the `Iff` slice needs the constructor's denotation
  (`•`, since `Iff.intro`'s type is a proposition) to be identified inside the motive's argument —
  a step with no counterpart in `EqRecLarge.lean`.
* **The `≠ 0` exclusion is already free** (`IffAudit.pt_not_mem_interp_iffRecType_of_ne`, no
  parameter-space inhabitant), and the level-branch obstruction is already proved
  (`IffAudit.no_level_uniform_value`), so none of the surrounding scaffolding has to be rebuilt.

**And one thing that is genuinely unknown at `Iff.rec`, which §1 does not settle.**  §1 is a
*negation*, and a negation is free if the interpretation is empty.  At `Eq.rec` that worry is
answered — `EqLargeAudit.eqRecFn_mem_interp_eqRecType` exhibits a member, so the cell is provably
satisfiable and the gap is provably *repairable*.  At `Iff.rec` no member is exhibited anywhere, so
§1 leaves open which of two things is true: the cell is satisfiable by an `iffRecFn` nobody has
written, or `⟦Iff.rec's type⟧` is empty at `u.eval ls ≠ 0` and the block's obligation is
**unsatisfiable**.  Either way `preludeWitness` fails it, so §1 stands as a refutation of the
shared witness; but it is not yet evidence that the repair *exists*.  Building `iffRecFn` settles
that, and that is the thing to pick up first. -/

end Lean4Lean.SetModel.RecGap

/-! ## 7. Axiom audit, **by namespace**

Not by filename: `PreludeSpec.lean` declares into `Lean4Lean.SetModel`, not
`Lean4Lean.SetModel.PreludeSpec`, and two names in earlier handoffs are *unknown constant* for
exactly that reason.  Every name below is `Lean4Lean.SetModel.RecGap.*`. -/

#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessPt_not_mem_interp_iffRecType
#print axioms Lean4Lean.SetModel.RecGap.preludeWitness_cnst_neRec
#print axioms Lean4Lean.SetModel.RecGap.preludeWitness_mem_interp_neRecType
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_eq
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_iff
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_nonempty
#print axioms Lean4Lean.SetModel.RecGap.preludeSpecR_satisfiable
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_cnst_eq
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_cnst_eqRec
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_cnst_eqRec_zero
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_cnst_iffRec
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_cnst_neRec
#print axioms Lean4Lean.SetModel.RecGap.oracleOK_EqRec_preludeWitnessR
#print axioms Lean4Lean.SetModel.RecGap.repair_discriminates
#print axioms Lean4Lean.SetModel.RecGap.repair_changes_the_value
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_cnst_empty_of_not_mem
#print axioms Lean4Lean.SetModel.RecGap.eqRec_arm_ne_empty
#print axioms Lean4Lean.SetModel.RecGap.eqRec_mem_eqIndDecl_allNames
#print axioms Lean4Lean.SetModel.RecGap.iffRec_mem_iffIndDecl_allNames
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_congr_Eq
#print axioms Lean4Lean.SetModel.RecGap.mem_interp_EqType_preludeWitnessR
#print axioms Lean4Lean.SetModel.RecGap.oracleOK_Eq_preludeWitnessR
#print axioms Lean4Lean.SetModel.RecGap.preludeWitnessR_cnst_Eq_arm
