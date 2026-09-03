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

/-! ## 3--4. **RETIRED**: `preludeWitnessR` and everything stated at it

`preludeWitnessR` was a *measuring instrument*: a copy of `SetModel.preludeWitness` with the
`Eq.rec` arm repaired, living downstream so that `PreludeSpec.lean` could stay untouched while the
repair was priced.  The relocation it priced has been performed --
`SetModel.preludeWitness` now carries both recursor arms, in the η-contracted shape
(`docs/handoff-setmodel.md` §22.4) -- so every statement this section used to make is now available
at the assignment `PreludeOracle.lean` actually uses:

| retired | superseded by |
|---|---|
| `preludeWitnessR`, `preludeWitnessR_eq/_iff/_nonempty`, `preludeSpecR_satisfiable` | `SetModel.preludeWitness`, `preludeWitness_eq/_iff/_nonempty`, `preludeSpec_satisfiable` |
| `preludeWitnessR_cnst_eq/_eqRec/_iffRec/_neRec` (`simp`) | `preludeWitness_cnst_Eq/_cnst_eqRec/_cnst_iffRec/_cnst_neRec` (all `rfl`) |
| `preludeWitnessR_cnst_Eq_arm` + `preludeWitnessR_congr_Eq`'s `rw` detour | `preludeWitness_congr_Eq`, whose degenerate branch is `rfl` again -- the kernel trap §4.5 worked around **no longer exists** in the η-contracted shape |
| `mem_interp_EqType_preludeWitnessR`, `oracleOK_Eq_preludeWitnessR` | `EqTFAudit.mem_interp_EqType_preludeWitness`, `EqTFAudit.oracleOK_Eq` |
| `oracleOK_EqRec_preludeWitnessR` | `IffLargeAudit.oracleOK_EqRec_preludeWitness` |
| `repair_discriminates`, `repair_changes_the_value` | `IffLargeAudit.installed_repair_discriminates`, `installed_repair_changes_the_iffRec_value` -- which discriminate at **both** recursor cells, at one `L`, one `κ`, one `ls`, one level tuple and one `interp` |

**§1's `preludeWitnessPt_not_mem_interp_iffRecType` is NOT retired**, and neither is
`SetModel.preludeWitnessPt`: repairing `preludeWitness` in place destroys the `∉` half of every
discriminating lemma unless the pre-repair assignment is kept as a named negative control.  That is
the trap §22.13 records; do not "simplify" it away. -/

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

/-! ### 5.1 The repaired fallback statement — **installed**, so retired here

`preludeWitnessR_cnst_empty_of_not_mem` is superseded by `SetModel.preludeWitness_cnst_empty`,
which carries **two** extra hypotheses (`m ≠ ``Eq.rec` and `m ≠ ``Iff.rec`) because the installed
repair touches both recursor cells, not one.  `NEAudit.neOracle_eq_empty_of_not_mem` already has
them, and `NEAudit.cnstOf_preludeTail` already supplies them. -/

/-! ### 5.2 …and `h4` is **necessary**, not defensive

Without it the statement is false.  This is the control that separates "the repair costs one
extra hypothesis" from "the repair costs one extra hypothesis that could have been avoided". -/

section Necessary

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv) (hle : eqEnv ≤ envF)

include L hu hv hle in
/-- **The shared witness' `Eq.rec` entry is not `∅` on the `≠ 0` slice**, so `h4` in
`SetModel.preludeWitness_cnst_empty` cannot be dropped.  `hx` is a hypothesis *about the given* `κ` — no `κ` is chosen here, and this is a
negative control, so the three-point scale of `docs/vacuity-ledger.md` applies to it and not to
§4.3's obligation. -/
theorem eqRec_arm_ne_empty (hn : u.eval ls ≠ 0) {x : V} (hx : x ∈ U κ (v.eval ls)) :
    (preludeWitness (V := V) κ ls).cnst ``Eq.rec [u, v] ≠ (pt : V) := by
  rw [preludeWitness_cnst_eqRec, EqLargeAudit.eqRecVal_pair, if_neg hn]
  exact EqLargeAudit.eqRecFn_ne_pt L (preludeWitness κ ls) hu hv hle
    (preludeWitness_eq κ ls v) hn hx

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
#print axioms Lean4Lean.SetModel.RecGap.eqRec_arm_ne_empty
#print axioms Lean4Lean.SetModel.RecGap.eqRec_mem_eqIndDecl_allNames
#print axioms Lean4Lean.SetModel.RecGap.iffRec_mem_iffIndDecl_allNames
