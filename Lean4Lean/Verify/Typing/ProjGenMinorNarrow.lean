import Lean4Lean.Verify.Typing.ProjGenMinor
import Lean4Lean.Verify.Typing.Lemmas

/-!
# The collapse test for `realMinor_hasType_gen`

`ORCHESTRATOR.md` working rule 5: *a claimed generalisation is not one until the collapse
test passes* — can the generalised statement's quantifiers be instantiated so that it
degenerates into the target it claims to generalise?

`realMinor_hasType_gen` (`ProjGenMinor.lean`) claims to be `projMinor_hasType`
(`Verify/Typing/Lemmas.lean`) with the induction-hypothesis block bound.  The theorem below
is that claim, machine-checked: at a block satisfying `VEnv.IsStructure` — one type, one
constructor, no recursive fields, so `nm = 1`, `q = 0`, `j = 0` and `nr = 0` — the
*generalised* conclusion is discharged, and it is discharged **by the narrow theorem**, whose
statement it therefore contains.

**This module is deliberately separate.**  `projMinor_hasType`'s axiom cone reaches `sorryAx`
through `Theory/Typing/UniqueTyping.lean` (`IsDefEqU.trans`/`.of_l`, gated on
`IsDefEqU.weakN_iff`), so anything proved here inherits that; `ProjGenMinor.lean` and
`ProjGenMinorWitness.lean` have measured **empty** hole cones and must keep them.
-/

namespace Lean4Lean

open VExpr

/-- **The collapse test, machine-checked.**  `realMinor_hasType_gen`'s conclusion at the
narrow instance `q = 0`, `j = 0`, `mots = [projMotiveTerm …]` is exactly what
`projMinor_hasType` proves.

The two rewrites are the whole of the collapse: `realMinor_norec` turns the generalised term
into `projMinor` (`H.noRec` is what supplies its hypothesis), and `List.append_nil` closes the
empty accumulator.  Nothing else has to be reconciled — which is the point: had the
generalised statement quantified over a *different* telescope or a different body index, no
rewrite would have made these two conclusions meet. -/
theorem realMinor_hasType_narrow {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : VEnv.WF env) (hI : D.IotaCtx env) (H : env.IsStructure S D T C)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U) (hcl : D.ProjClosed T C)
    {i : Nat} (hi : i < C.fields.length)
    (hlv : ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) → (C.fields.getD k default).lvl.inst us
      ≈ D.elimLvl.inst (D.projLvls C us k))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasType env U S D T C us k)
    {Γ ps : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasType U Γ
      (D.realMinor (D.projLvls C us i) (ps ++ [projMotiveTerm D T C us ps i] ++ []) i 0 C)
      (VExpr.instAll ((D.minorType 0 0 C).instL (D.projLvls C us i))
        (ps ++ [projMotiveTerm D T C us ps i] ++ [])) := by
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ h3
  rw [D.realMinor_norec (us := us) (i := i) (q := 0) (ps := ps)
      (mots := [projMotiveTerm D T C us ps i]) (acc := [])
      H.noRec (by simp [H.nm_eq]) rfl hself, List.append_nil]
  exact projMinor_hasType henv hI H h3 h7 hcl i hi hlv hIH hΓ hps hpsA

end Lean4Lean
