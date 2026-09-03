/-
# `ConsumeTeleOffK`: §T15.8's own-head marking, checked — and half of it refuted

`docs/handoff-hyptrim.md` §5 item 5 flags §T15.8's own-head marking as resting on
`Theory/Inductive/RecTyped.lean`'s three `_off_K` theorems and says:

> what is **not** checked here is that (B)'s closures consume them in the shape they are stated
> in.  That composition is the next thing someone will assume and should not.

Two findings, and they point in opposite directions.

1. **The composition was already in the tree**, in `RecTyped.lean` itself, ~370 lines below the
   three theorems: `VEnv.recConstsR_wf_of_recHargsD` (`RecTyped.lean:773`) refines
   `VEnv.recConstsR_wf_of_entriesD` and closes each off-`K` branch with a **bare `exact`** —
   `motiveEntry_defeq_off_K` at `:809`, `VIndRestore.minorEntry_defeq_off_K` at `:821`,
   `recBody_defeq_off_K` at `:828`.  No `simpa`, no massaging.  §1 below restates the three fits
   as named theorems so the claim is citable rather than buried in a tactic block.

2. **But the marking itself overstates, and this file refutes the overstatement.**
   `NestedTele.lean` §T15.8 says `RecTyped.lean` proves the off-`K` branch of all three entry
   families **"from `OwnId` alone"**, and lists the own-head entries of all three as
   **"discharged"**.  That is true of two of the three.  `VIndRestore.minorEntry_defeq_off_K`
   takes a **`TeleDefEq` hypothesis** — `MinorFldDefEq`, one of the four open data families of
   `RecTyped.lean` §5 — so the minor entry off `K` is a *reduction*, not a discharge.  §2 shows
   this is not a technicality: at the canonical parameterised block the two telescopes
   **differ after `substC σ` and `liftTele`**, so nothing reflexive closes it there.

`minorEntry_defeq_off_K`'s own docstring says exactly this ("the *only* residual is the
field-telescope defeq … this is **not** vacuous work"), and `RecTyped.lean` §5 demands `hfldD` at
**every** `q`, off `K` included.  So `RecTyped.lean` is accurate throughout; it is §T15.8's
*summary* of it that is wrong, and §T15.8 is the text a reader quotes.
-/
import Lean4Lean.Theory.Inductive.RecTyped

namespace Lean4Lean

/-! ## §1 The three off-`K` families fit (B)'s closure verbatim

Each statement below is literally the corresponding hypothesis slot of
`VEnv.recConstsR_wf_of_entriesD` (`NestedTele.lean:2236`) — `σ` fixed at `R.csubst D K`, which is
the closure's own substitution rather than the `_off_K` theorems' generic one — guarded to the
off-`K` members, and each is closed by `exact`.  Nothing is restated in a convenient shape.

The `hrec` hypothesis is what the closure derives from its `hsrc` (`RecTyped.lean:794`); it is
carried here as a hypothesis so these three say only what they are about. -/

section
variable {E₂ e₂ : VEnv} {D : VInductDecl'} {R : VIndRestore} {K : List Name}

/-- **`recConstsR_wf_of_entriesD`'s `hmot` slot, off `K`** — free. -/
theorem offK_fits_hmot (he₂ : e₂.Ordered)
    (hσ : (R.csubst D K).WFD E₂ e₂ D.recUvars) (hown : R.OwnId D K)
    (hrec : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) :
    ∀ (t : Nat) (Tt : VIndType), D.types[t]? = some Tt → Tt.name ∉ K → t < D.nm →
      ∃ u, e₂.IsDefEq D.recUvars
        (((D.motives.map (VExpr.substC · (R.csubst D K))).take t).reverse
          ++ ((D.atRecTele D.params).map (VExpr.substC · (R.csubst D K))).reverse)
        ((D.motiveType t).substC (R.csubst D K))
        ((D.motiveTypeR R t).substC (R.csubst D K)) (.sort u) := fun _ _ hTt hKt ht =>
  motiveEntry_defeq_off_K he₂ hσ hown (VInductDecl'.getD_types hT) (hrec j T hT) hTt hKt ht

/-- **`recConstsR_wf_of_entriesD`'s `hbody` slot, off `K`** — free. -/
theorem offK_fits_hbody (he₂ : e₂.Ordered)
    (hσ : (R.csubst D K).WFD E₂ e₂ D.recUvars) (hown : R.OwnId D K)
    (hrec : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∉ K → ∃ v : VLevel,
      e₂.IsDefEq D.recUvars
        (((D.atRecTele D.params ++ D.motives ++ D.minors ++
            VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
            (VExpr.substC · (R.csubst D K))).reverse)
        ((VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
              (VExpr.bvars 0 T.indices.length))
            ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
              (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC (R.csubst D K))
        ((VExpr.forallE (D.tyAppR' R j (T.indices.length + D.nmin + D.nm)
              (VExpr.bvars 0 T.indices.length))
            ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
              (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC (R.csubst D K)) (.sort v) :=
  fun j T hT hK => recBody_defeq_off_K he₂ hσ hown (hrec j T hT) hT hK

/-- **`recConstsR_wf_of_entriesD`'s `hmin` slot, off `K` — and `hfld` is a HYPOTHESIS here.**

Compare `offK_fits_hmot`/`offK_fits_hbody`, which take no data at all.  This one carries
`R.MinorFldDefEq D (R.csubst D K) e₂ q C` at every off-`K` entry, which is why §T15.8's
"discharged"/"free"/"from `OwnId` alone" is wrong for this family.  §2 shows the hypothesis is
not idly stated. -/
theorem offK_fits_hmin (he₂ : e₂.Ordered)
    (hσ : (R.csubst D K).WFD E₂ e₂ D.recUvars) (hσc : (R.csubst D K).Closed)
    (hown : R.OwnId D K)
    (hrec : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    (hfld : ∀ (q t : Nat) (C : VIndCtor), D.ctorsAll[q]? = some (t, C) →
      R.MinorFldDefEq D (R.csubst D K) e₂ q C) :
    ∀ (q t : Nat) (C : VIndCtor) (Tt : VIndType), D.ctorsAll[q]? = some (t, C) →
      D.types[t]? = some Tt → Tt.name ∉ K → C ∈ Tt.ctors → q < D.minors.length →
      ∃ u, e₂.IsDefEq D.recUvars
        (((D.minors.map (VExpr.substC · (R.csubst D K))).take q).reverse
          ++ ((D.motives.map (VExpr.substC · (R.csubst D K))).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · (R.csubst D K))).reverse))
        ((D.minorType q t C).substC (R.csubst D K))
        ((D.minorTypeR R q t C).substC (R.csubst D K)) (.sort u) :=
  fun q t C _ hq hTt hKt hC hqlt =>
    VIndRestore.minorEntry_defeq_off_K he₂ hσ hσc hown (VInductDecl'.getD_types hT)
      (hrec j T hT) hTt hKt hC hq hqlt (hfld q t C hq)

end

/-! ## §2 The refutation, at the canonical parameterised block

§T15.8's sentence is *"off `K` the entries are **free** … from `OwnId` alone"*.  For the minor
family that is false, and the witness is the block the rest of this corner is measured at.

`ntreeAux` has `nm = 2`, `np = 1`, `K = [`_nested.List_1]`.  Member `0` is the block's own head
`NTree`, whose name is **not** in `K` (`InductiveDeclExamples.ntree_recTyped_hK_false`), and
`ctorsAll[0]` is its constructor `NTree.node`.  So `q = 0` is an off-`K` minor entry — and it is
exactly the entry whose field telescope moves, because `NTree.node`'s recursive field is the
`List (NTree α)` occurrence the restoration rewrites.

`RecTyped.lean`'s `ntree_node_fieldTypesR_ne` already says the two `atRecTele` telescopes differ.
That is **not** enough on its own: `MinorFldDefEq` compares them after `substC σ` **and** under
`liftTele (D.nm + q)`, and a σ that mapped the companion constant onto the restored form would
collapse the difference and make `hfld` free after all by `TeleDefEq.of_eq`.  It does not. -/

namespace InductiveDeclExamples

/-- The off-`K` minor entry of `ntreeAux` is `q = 0`, at the block's own head. -/
theorem ntree_ctorsAll_zero : ntreeAux.ctorsAll[0]? = some (0, ntreeNode) := rfl

/-- …and `q = 0` is a real minor entry. -/
theorem ntree_zero_lt_minors : 0 < ntreeAux.minors.length := by decide

/-- **`MinorFldDefEq`'s two telescopes at the off-`K` entry are NOT equal** — after `substC σ`
and under `liftTele`, which is the shape `minorEntry_defeq_off_K` consumes.

So `hfld` at `q = 0` is not closable by `TeleDefEq.refl` or `TeleDefEq.of_eq`, and the off-`K`
minor entry of the canonical parameterised nested block is **not** free.  This is the machine
check behind §2's claim; `ntree_node_fieldTypesR_ne` is the same fact one `substC` short. -/
theorem ntree_offK_minorFld_telescopes_ne :
    VExpr.liftTele (ntreeAux.nm + 0)
        ((ntreeAux.atRecTele (ntreeNode.fields.map (·.type))).map
          (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK)))
      ≠ VExpr.liftTele (ntreeAux.nm + 0)
        ((ntreeAux.atRecTele (ntreeNode.fieldTypesR ntreeAux ntreeRestore)).map
          (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK))) := by
  decide

/-- …and the substitution is not the empty one at this block, which is the trap that would have
made the previous theorem hold for an uninteresting reason. -/
theorem ntree_csubst_hits_companion :
    ntreeRestore.csubst ntreeAux ntreeK `_nested.List_1 ≠ none := by decide

/-! ### §2b Both branches of §5's `by_cases hK` are live at this block

`RecTyped.lean` §5 splits every entry family on `T.name ∈ K`.  A composition check that only
inspects the statements cannot tell whether the off-`K` branch is reachable at a real block — and
if it were not, §1 would be fitting a dead branch.  It is reachable, and so is the other one:
`ntreeAux` has **one member on each side**.  So `ntreeAux_obligationB_of_bundles`, which is §5
instantiated at this block, exercises the off-`K` composition rather than stepping over it. -/

/-- Member `0` (`NTree`, the block's own head) is **off** `K`. -/
theorem ntree_member_zero_off_K : (ntreeAux.types.getD 0 default).name ∉ ntreeK := by decide

/-- Member `1` (the companion) is **in** `K`, so neither branch is the only one. -/
theorem ntree_member_one_in_K : (ntreeAux.types.getD 1 default).name ∈ ntreeK := by decide

end InductiveDeclExamples

/-! ## §3 What this file does and does not claim

* **Claimed, and machine-checked:** the three `_off_K` theorems fit
  `VEnv.recConstsR_wf_of_entriesD`'s three hypothesis slots at `σ = R.csubst D K` with no
  reshaping (§1) — and that fit was *already* consumed in `RecTyped.lean` §5 before this file
  existed, so `docs/handoff-hyptrim.md` §5 item 5's "next thing someone will assume" was already
  true when it was written.
* **Claimed, and machine-checked:** `NestedTele.lean` §T15.8's "off `K` the entries are free …
  from `OwnId` alone", and its listing of the own-head entries of **all three** families as
  "discharged", is **false for the minor family**.  `minorEntry_defeq_off_K` takes
  `MinorFldDefEq`, and at `ntreeAux`'s off-`K` entry that hypothesis is not reflexive (§2).
  §T15.8's own residual list already carries `hfld` as a separate item, so the *arithmetic* of
  the residual is unaffected; the *wording* is what misleads.
* **Not claimed:** that `MinorFldDefEq` at `q = 0` is inhabited or refuted.  It is neither here.
  `RecTyped.lean`'s `ntree_minorFld_nil` inhabits it at `q = 1` (`nlistNil`, no fields) and
  discloses that as degenerate; §2 is the complementary *lower* bound — the entry where it is not
  degenerate is also the entry where nothing reflexive closes it.
* **Not claimed:** anything about the **non-`D`** closures `recConstsR_wf_of_entries` /
  `recConstsR_wf_of_blocks` that §T15.8 names.  Their entry slots are textually identical to the
  `D` ones (only `hσ` differs, `WF` for `WFD`), so §1 transports along `CSubst.WF.wfd`; but
  §T15.3a records those two as **vacuous in `hσ`** at every parameterised block, so the `D`
  closure is the one the composition has to fit and the one §1 is stated at. -/

end Lean4Lean

/-! ## §4 Axiom lines -/
#print axioms Lean4Lean.offK_fits_hmot
#print axioms Lean4Lean.offK_fits_hbody
#print axioms Lean4Lean.offK_fits_hmin
#print axioms Lean4Lean.InductiveDeclExamples.ntree_ctorsAll_zero
#print axioms Lean4Lean.InductiveDeclExamples.ntree_zero_lt_minors
#print axioms Lean4Lean.InductiveDeclExamples.ntree_offK_minorFld_telescopes_ne
#print axioms Lean4Lean.InductiveDeclExamples.ntree_csubst_hits_companion
#print axioms Lean4Lean.InductiveDeclExamples.ntree_member_zero_off_K
#print axioms Lean4Lean.InductiveDeclExamples.ntree_member_one_in_K
