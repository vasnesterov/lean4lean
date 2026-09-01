import Lean4Lean.Verify.Typing.ProjGenBlock
import Lean4Lean.Verify.Typing.Lemmas

/-!
# Instrument 7 on `padMinors_hasArgs`: its `hreal` premise is satisfiable

`padMinors_hasArgs`/`padMinors_hasArgs_take` (`ProjGenBlock.lean`) type every *padding* minor
of `projCoreG`'s block outright and take the **real** minor's typing as the premise `hreal`.
A premise is invisible to every instrument in this tree (`docs/vacuity-ledger.md` §0's seventh
blindness, and row 107e), so it has to be exhibited rather than assumed satisfiable.

Below it is exhibited: at a `VEnv.IsStructure` block — one type, one constructor, no recursive
fields — `hreal` is **exactly** `projMinor_hasType`'s conclusion, and this file derives it.
`D.ctorsAll = [(0, C)]` forces `q = 0` and `C' = C`, `take 0 = []`, and
`VInductDecl'.realMinor_norec` identifies the real minor with `C.projMinor`.

This module is kept apart from `ProjGenBlock.lean` for the reason `ProjGenSwapNarrow.lean` is
kept apart from `ProjGenSwap.lean`: `projMinor_hasType`'s cone carries
`{weakN_iff, forallE_inv_stratified}`, and the block lemmas themselves must not.

**What this does not test.**  At `nmin = 1` the block has a single entry, so the *padding*
branch of `padMinors_hasArgs_take` is never taken here and the accumulator is always `[]` —
the same blindness `docs/vacuity-ledger.md` row 111c records for `iota_law_of_gen`.  What
excludes a slot error in the padding branch is `padMinorsAux_getElem`, an equation about a
definite list.
-/

namespace Lean4Lean

open VExpr

/-- **`hreal`, at a narrow block.**  The premise `padMinors_hasArgs` cannot discharge, shown
satisfiable at every `IsStructure` instance. -/
theorem padMinors_hreal_narrow {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : VEnv.WF env) (hI : D.IotaCtx env) (H : env.IsStructure S D T C)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U) (hcl : D.ProjClosed T C)
    {i : Nat} (hi : i < C.fields.length)
    (hlv : ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
      (C.fields.getD k default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us k))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasType env U S D T C us k)
    {Γ ps : List VExpr} {X : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    ∀ q C', D.ctorsAll[q]? = some ((0 : Nat), C') →
      env.HasType U Γ
        (D.realMinor (D.projLvls C us i)
          (ps ++ [projMotiveTerm D T C us ps i]
            ++ (D.padMinors (D.projLvls C us i) ps [projMotiveTerm D T C us ps i] X i 0).take q)
          i q C')
        (VExpr.instAll ((D.minorType q 0 C').instL (D.projLvls C us i))
          (ps ++ [projMotiveTerm D T C us ps i]
            ++ (D.padMinors (D.projLvls C us i) ps [projMotiveTerm D T C us ps i]
                  X i 0).take q)) := by
  have hall : D.ctorsAll = [((0 : Nat), C)] := by
    simp [VInductDecl'.ctorsAll, H.types, H.ctors]
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ h3
  intro q C' hqC
  rw [hall] at hqC
  match q with
  | 0 =>
    obtain rfl : C = C' := by simpa using hqC
    rw [List.take_zero,
      D.realMinor_norec (us := us) (q := 0) H.noRec (by simp [H.nm_eq]) rfl hself,
      List.append_nil]
    exact projMinor_hasType henv hI H h3 h7 hcl i hi hlv hIH hΓ hps hpsA
  | q+1 => simp at hqC

end Lean4Lean
