import Lean4Lean.Theory.Typing.LiftTrimWitness

/-!
# `WFRippleWitness` — the retired `ntreeAux_WF` wrapper, instantiated where its hypothesis fails

`InductiveDeclExamples.ntreeAux_WF` used to be

    (h : VEnv.empty.addInduct' listDecl = some env₁) → ntreeAux.WF env₁

with `h` unused.  On 2026-09-03 the hypothesis-free `ntreeAux_WF'` replaced it at all 32 of its
application sites (14 files) and the wrapper was deleted; `docs/handoff-wfripple.md` records the
ripple.  A deleted hypothesis changes what a statement *says*, so the strengthening is instantiated
rather than asserted, and instantiated at an environment where the removed hypothesis is
**refuted** — so the old form had no instance there at all.

`Theory/Typing/LiftTrimWitness.lean` §3 already gives the bare `ntreeAux.WF badEnv`.  What is new
here is that the strengthened form is *consumed at a real block*: `badEnv` really does stage the
real nested block `ntreeAux`, and the `ctors` field of `ntreeAux_WF'` really does hand back
`VIndCtor.WF` for both of the auxiliary member's constructors in that staging.  That is the field
the 32 re-pointed sites reach through, and it is the one a wrapper could not have delivered had
the hypothesis been load-bearing.

Nothing here is a `sorry`, and nothing here closes a census hole.
-/

namespace Lean4Lean

open InductiveDeclExamples

namespace WFRipple

/-! ## 1. The retired hypothesis has no instance at `badEnv` -/

/-- The hypothesis the wrapper carried, refuted at `badEnv` (`LiftTrimWitness.lean` §1: `badEnv`
declares `bad : #0`, so it is not `Ordered`, while `listEnv_ordered` turns the equation into
`badEnv.Ordered`). -/
theorem hyp_refuted : ¬ (VEnv.empty.addInduct' listDecl = some badEnv) :=
  not_addInduct_badEnv

/-! ## 2. …yet the real nested block stages into it

`addIndTypes` is `addConstList` over `typeConsts`, and the only obstruction is a name clash.
`badEnv` holds exactly `bad`, so `NTree` and `_nested.List_1` are both fresh. -/

/-- The auxiliary block's two type constants go into `badEnv`. -/
theorem stage_badEnv : ∃ et, badEnv.addIndTypes ntreeAux = some et :=
  VEnv.addConstList_eq_some_iff.2 (by refine ⟨?_, by decide⟩; decide)

/-! ## 3. The `ctors` field of `ntreeAux_WF'`, at that staging

This is the substantive instance: `VInductDecl'.WF.ctors` is what the re-pointed sites use, and
at `badEnv` it is reachable only through the hypothesis-free form. -/

/-- The auxiliary member `_nested.List_1` of the block, as `ntreeAux.types[1]?` gives it. -/
def auxMember : VIndType :=
  { name := `_nested.List_1,
    type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
    indices := [], ctors := [nlistNil, nlistCons] }

theorem auxMember_eq : ntreeAux.types[1]? = some auxMember := rfl

/-- **`nlistCons` is a well-formed constructor in a `badEnv`-staging of the block.** -/
theorem nlistCons_WF_badEnv {et : VEnv} (hst : badEnv.addIndTypes ntreeAux = some et) :
    nlistCons.WF et ntreeAux 1 auxMember :=
  ntreeAux_WF'.ctors et hst 1 auxMember auxMember_eq nlistCons
    (List.mem_cons_of_mem _ List.mem_cons_self)

/-- …and so is `nlistNil`. -/
theorem nlistNil_WF_badEnv {et : VEnv} (hst : badEnv.addIndTypes ntreeAux = some et) :
    nlistNil.WF et ntreeAux 1 auxMember :=
  ntreeAux_WF'.ctors et hst 1 auxMember auxMember_eq nlistNil List.mem_cons_self

/-- The two halves together, with the staging existentially quantified: **at an environment where
the retired hypothesis is false**, the real block stages and both of the auxiliary member's
constructors are well-formed in the staging. -/
theorem ctors_WF_at_refuting_env :
    ¬ (VEnv.empty.addInduct' listDecl = some badEnv) ∧
      ∃ et, badEnv.addIndTypes ntreeAux = some et ∧
        nlistNil.WF et ntreeAux 1 auxMember ∧ nlistCons.WF et ntreeAux 1 auxMember :=
  ⟨hyp_refuted, stage_badEnv.imp fun _ hst =>
    ⟨hst, nlistNil_WF_badEnv hst, nlistCons_WF_badEnv hst⟩⟩

end WFRipple

end Lean4Lean

/-! ## 4. Axiom lines

Names read off this file's own `namespace` lines. -/
#print axioms Lean4Lean.WFRipple.hyp_refuted
#print axioms Lean4Lean.WFRipple.stage_badEnv
#print axioms Lean4Lean.WFRipple.auxMember_eq
#print axioms Lean4Lean.WFRipple.nlistNil_WF_badEnv
#print axioms Lean4Lean.WFRipple.nlistCons_WF_badEnv
#print axioms Lean4Lean.WFRipple.ctors_WF_at_refuting_env
