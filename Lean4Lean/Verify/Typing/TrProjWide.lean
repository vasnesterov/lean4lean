import Lean4Lean.Verify.Typing.ProjGenTerm
import Lean4Lean.Verify.Typing.Lemmas

/-!
# `TrProjG`: the `TrProj` widening of ledger row 107d option (d), with `noRec` kept

`docs/vacuity-ledger.md` row 107d rules that when `TrProj` (`Verify/Typing/Expr.lean:82`) is
widened from `VEnv.IsStructure` to `VEnv.IsStructureG` — dropping `types : D.types = [T]` and
gaining a block index `j` — the widening should be **option (d)**: carry the target's typing as
an **eleventh field** of the constructor, so that `TrProj.wf` becomes a projection and wall 2
(`projTermG_hasType`) is relocated rather than required.  Ruling (iii) of that row bundles the
`noRec` drop (`C.recFields = []`) into the same move.

Row 174b splits the two, and this file is the split executed: the relation below **keeps
`noRec`**, so the eleventh field is not a recorded hypothesis at all — it is *derivable*, from
`VEnv.IsStructureG.projTermG_hasType` (`Verify/Typing/ProjGenTerm.lean`, proved 2026-09-03).
That is `TrProjG.mk'` below, and it is what row 107e's instrument-7 flag asked for: the field
whose falsity would have made the widened `TrProj.wf` *false* is a theorem here, at every
instance the smart constructor covers.

**`TrProj` itself is not touched.**  This is a new predicate beside it; §"collapse" relates the
two in both directions, and `TrProjWideWitness.lean` fires the new one where the old one cannot
reach.
-/

namespace Lean4Lean

open VExpr

variable (env : VEnv) (U : Nat) in
/-- **The widened `TrProj`.**  Field for field the same as `TrProj` (`Verify/Typing/Expr.lean`)
except:

* `env.IsStructure S D T C` becomes `env.IsStructureG S D j T C` — the singleton-block field
  `types : D.types = [T]` is gone, and a **block index** `j` appears;
* `C.recFields = []` is carried **explicitly** (`IsStructureG` dropped it; `EtaStructSpineG`
  re-adds it the same way).  This is the half of row 107d ruling (iii) that is *not* taken;
* the target is `D.projTermG T C us ps ιs i j e`, not `D.projTerm T C us ps ιs i e`;
* there is an **eleventh field**: the target's own typing (row 107d's option (d)).

The eleventh field is redundant — `TrProjG.mk'` builds the relation without it — and it is kept
in the constructor anyway, because that is what makes `TrProjG.wf` hole-free and hypothesis-free
(no `VEnv.WF`, no `OnCtx`, no `VExpr.WF` of the major premise). -/
inductive TrProjG : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop
  | mk {S : Lean.Name} {D T C us ps ιs Γ e i j} :
    env.IsStructureG S D j T C →
    C.recFields = [] →
    env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ ιs)) →
    us.length = D.uvars → ps.length = D.np → ιs.length = T.indices.length →
    i < C.fields.length →
    (∀ l ∈ us, l.WF U) →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs →
    (D.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    env.HasType U Γ (D.projTermG T C us ps ιs i j e)
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e)) →
    TrProjG Γ S i e (D.projTermG T C us ps ιs i j e)

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr}

/-! ## What option (d) buys: `wf` with no hypotheses at all -/

/-- **`TrProj.wf` under option (d).**  Compare `TrProj.wf` (`Verify/Typing/Lemmas.lean:1583`),
which needs `VEnv.WF env`, `OnCtx Γ (env.IsType U)` and `VExpr.WF env U Γ e`, and whose cone
carries `weakN_iff` and `forallE_inv_stratified` through `projTerm_hasType`.  Here it is
`cases`-and-project.

Row 107e's warning applies to this statement and is answered by `mk'` below, **not** by this
one: a greener axiom set here means only that the content moved into a hypothesis. -/
theorem TrProjG.wf (H : TrProjG env U Γ s i e e') : VExpr.WF env U Γ e' := by
  cases H with | mk _ _ _ _ _ _ _ _ _ _ _ htgt => exact ⟨_, htgt⟩

/-- The widened relation still certifies `IsStructureG` for the projected name — the analogue of
`TrProj.isStructure`, which is what `inferProj.WF` reads off the predicate. -/
theorem TrProjG.isStructureG (H : TrProjG env U Γ s i e e') :
    ∃ D j T C, env.IsStructureG s D j T C := by
  cases H with | mk hS => exact ⟨_, _, _, _, hS⟩

/-! ## The eleventh field, discharged

This is the round's content.  With `noRec` kept, wall 2 applies, so the eleventh field follows
from the other ten. -/

/-- **The eleventh field discharged: the ten-field smart constructor.**

Every field of `TrProj.mk` (with `IsStructure` widened to `IsStructureG` and `noRec` added
back), plus the two side conditions `projTermG_hasType` needs and `TrProj.wf` already took —
`VEnv.WF env` and `OnCtx Γ (env.IsType U)` — and the eleventh field is *produced*, not assumed.

So option (d) is not a relocation of wall 2 at this generality: at a `noRec` block wall 2 is
proved (`VEnv.IsStructureG.projTermG_hasType`, `Verify/Typing/ProjGenTerm.lean`), and the extra
field costs the caller nothing it did not already have to supply to `TrProj.wf`.

Two qualifications, both measured (`docs/handoff-trproj-wide.md` §0, §2.3):
* **proved is not hole-free.**  This lemma inherits `VEnv.IsDefEqU.weakN_iff` and
  `VEnv.IsDefEqU.forallE_inv_stratified` — wall 2's own two, which are also the *narrow*
  `projTerm_hasType`'s own two.  No new hole, and none traded.
* the discharge is *from* `VEnv.WF env`.  A caller who cannot supply that (and today nobody can,
  at any `addInduct'` environment) still faces the eleventh field as a real hypothesis, which is
  the open half of ledger row 107e's flag. -/
theorem TrProjG.mk' {S : Lean.Name} {D T C us ps ιs} {j : Nat}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hS : env.IsStructureG S D j T C) (hrec : C.recFields = [])
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ ιs)))
    (h3 : us.length = D.uvars) (h4 : ps.length = D.np) (h5 : ιs.length = T.indices.length)
    (hi : i < C.fields.length) (h7 : ∀ l ∈ us, l.WF U)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hιsA : env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs)
    (hF : D.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
      (C.fields.getD k default).lvl.inst us ≈ .zero) :
    TrProjG env U Γ S i e (D.projTermG T C us ps ιs i j e) :=
  .mk hS hrec he h3 h4 h5 hi h7 hpsA hιsA hF
    (hS.projTermG_hasType henv hrec h3 h7 i hi (projLvls_elim_of_F17 hF) hΓ he h4 h5 hpsA hιsA)

/-! ## Collapse: the widening contains the old relation

Direction 1 (`TrProj.toG`) is the one that matters for a *relation* widening — it says no
derivation is lost, i.e. the new predicate is a superset and the change is a generalisation
rather than a substitution.  It is fully discharged, at exactly the two side conditions
`TrProj.wf` itself already takes.

Direction 2 (`TrProjG.toNarrow`) is **conditional on a G4-shaped hypothesis** and is labelled as
such: see its docstring. -/

/-- **Collapse, direction 1: every `TrProj` derivation is a `TrProjG` derivation**, at block
index `0`, with the same major premise and the same target.

The eleventh field is supplied by the *narrow* `projTerm_hasType` (`Verify/Typing/Lemmas.lean`)
through `TrProj.wf`'s own route, so this direction does not depend on wall 2 having been proved
— it would have gone through before 2026-09-03 too.  `henv`/`hΓ` are exactly `TrProj.wf`'s. -/
theorem TrProj.toG (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (H : TrProj env U Γ s i e e') : TrProjG env U Γ s i e e' := by
  obtain @⟨_, D, T, C, us, ps, ιs, _, _, _, hS, he, h3, h4, h5, hi, h7, hpsA, hιsA, hF⟩ := H
  have heq := D.projTermG_eq_projTerm T C us ps ιs i e hS.types hS.ctors hS.noRec h3
  rw [← heq]
  exact .mk' henv hΓ hS.toG hS.noRec he h3 h4 h5 hi h7 hpsA hιsA hF

/-- **The target term is unchanged at a narrow block.**  `projTermG … 0 = projTerm`, so the
widening does not silently move the object being related — this is the reason direction 1 can
state the same `e'` on both sides. -/
theorem trProjG_target_eq_projTerm (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps ιs : List VExpr) (i : Nat) (e : VExpr)
    (htypes : D.types = [T]) (hctors : T.ctors = [C]) (hrec : C.recFields = [])
    (h3 : us.length = D.uvars) :
    D.projTermG T C us ps ιs i 0 e = D.projTerm T C us ps ιs i e :=
  D.projTermG_eq_projTerm T C us ps ιs i e htypes hctors hrec h3

/-- **Collapse, direction 2, and it is CONDITIONAL.**  A `TrProjG` derivation collapses to a
`TrProj` derivation at an environment where every `IsStructureG` certificate for the projected
name is also an `IsStructure` certificate.

`hsingle` is **ledger G4** in hypothesis form: `IsStructureG` existentially quantifies the block
in its `decl` field and carries no claim that a name belongs to at most one block, so nothing in
this tree discharges `hsingle` at any concrete environment — `trProj_at_MutField_needs_other_block`
(`Verify/TypeChecker/EtaStructG.lean:580`) hits the same wall from the other side.  **So this
direction is recorded as an implication, not used as evidence that the widening is faithful**;
direction 1 carries that weight.  Stated because a widening with only one direction available
should say which one is missing and why. -/
theorem TrProjG.toNarrow
    (hsingle : ∀ {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor},
      env.IsStructureG s D j T C → env.IsStructure s D T C)
    (H : TrProjG env U Γ s i e e') : TrProj env U Γ s i e e' := by
  obtain @⟨_, D, T, C, us, ps, ιs, _, _, _, j, hS, hrec, he, h3, h4, h5, hi, h7,
    hpsA, hιsA, hF, _⟩ := H
  have hS' := hsingle hS
  have hj : j = 0 := by
    have h := hS.types; rw [hS'.types] at h
    match j, h with
    | 0, _ => rfl
  subst hj
  rw [D.projTermG_eq_projTerm T C us ps ιs i e hS'.types hS'.ctors hrec h3]
  exact .mk hS' he h3 h4 h5 hi h7 hpsA hιsA hF

/-! ## Does the eleventh field transport?  The structural cluster, measured

Row 107c reports that six of `TrProj`'s structural lemmas "widen and were compiled" — but that
measurement was taken *without* an eleventh field.  Option (d) adds one, and every structural
lemma must now transport the target's typing too.  Two data points below: `mono` is free, and
`weak'` is not free but is **available**, from `projTermG_lift'` plus `lift'_instAll`. -/

/-- **`mono` transports the eleventh field for free.**  Compare `TrProj.mono`
(`Verify/Typing/Lemmas.lean:946`): one extra `.mono`. -/
theorem TrProjG.mono {env env' : VEnv} (hle : env ≤ env')
    (H : TrProjG env U Γ s i e e') : TrProjG env' U Γ s i e e' :=
  let .mk h1 hrec h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 := H
  .mk (h1.mono hle) hrec (h2.mono hle) h3 h4 h5 h6 h7 (h8.mono hle) (h9.mono hle) h10
    (h11.mono hle)

/-- **`weak'` transports it too**, at the same hypotheses as `TrProj.weak'`
(`Verify/Typing/Lemmas.lean:590`) — `Ordered env` and a `Ctx.Lift'`, *not* `VEnv.WF`/`OnCtx`.

This is the measurement that matters for pricing option (d): the eleventh field does **not**
force the structural cluster to re-derive the typing (which would have needed `VEnv.WF` and so
strengthened `weak'`'s hypotheses).  It transports, because the target's type is an `instAll` of
a field type that `ProjClosedG` already pins closed at `D.np + i`. -/
theorem TrProjG.weak' {n : Lift} {Γ' : List VExpr} (henv : VEnv.Ordered env)
    (W : Ctx.Lift' n Γ Γ') (H : TrProjG env U Γ s i e e') :
    TrProjG env U Γ' s i (e.lift' n) (e'.lift' n) := by
  obtain @⟨_, D, T, C, us, ps, ιs, _, _, _, j, h1, hrec, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11⟩ := H
  have hcl := h1.projClosedG henv
  have hclN := hcl.toProjClosed h1.types (by rw [h1.ctors]; exact List.mem_singleton_self _)
  rw [D.projTermG_lift' T C us hcl h1.types h1.ctors h4 h5 h6]
  refine .mk h1 hrec ?_ h3 (by simp [h4]) (by simp [h5]) h6 h7 ?_ ?_ h10 ?_
  · simpa [VExpr.lift'_mkApp, List.map_append, VExpr.lift'] using h2.weak' henv W
  · have := h8.weak' henv W
    rwa [VExpr.liftTele'_eq_self (VExpr.ClosedTele.map_instL hclN.params) Lift.Fixes.zero] at this
  · have := h9.weak' henv W
    rwa [VExpr.lift'_instAllTele₀
      (by simpa [h4] using VExpr.ClosedTele.map_instL hclN.indices)] at this
  · have hty := h11.weak' henv W
    rw [D.projTermG_lift' T C us hcl h1.types h1.ctors h4 h5 h6] at hty
    have hget : (C.fields.map (·.type))[i]? = some (C.fields.getD i default).type := by
      rw [List.getElem?_map, List.getElem?_eq_getElem h6]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h6]
    have hfcl : ((C.fields.getD i default).type.instL us).ClosedN
        (0 + (ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e).length) := by
      have := (VExpr.ClosedTele.getElem? hclN.fields hget).instL (ls := us)
      simpa [h4] using this
    have heq : (VExpr.instAll ((C.fields.getD i default).type.instL us)
          (ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e) 0).lift' n
        = VExpr.instAll ((C.fields.getD i default).type.instL us)
          ((ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e).map (·.lift' n)) 0 :=
      VExpr.lift'_instAll (k := 0) (ρ := n) hfcl
    have hmap : (ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e).map
          (·.lift' n)
        = ps.map (·.lift' n) ++ (List.range i).map
            fun m => D.projTermG T C us (ps.map (·.lift' n)) (ιs.map (·.lift' n)) m j
              (e.lift' n) := by
      rw [List.map_append, List.map_map]
      congr 1
      refine List.map_congr_left fun m hm => ?_
      exact D.projTermG_lift' T C us hcl h1.types h1.ctors h4 h5
        (Nat.lt_trans (List.mem_range.1 hm) h6)
    rw [heq, hmap] at hty
    exact hty

/-- `weakN` follows from `weak'` exactly as it does for `TrProj`. -/
theorem TrProjG.weakN {n k : Nat} {Γ' : List VExpr} (henv : VEnv.Ordered env)
    (W : Ctx.LiftN n k Γ Γ') (H : TrProjG env U Γ s i e e') :
    TrProjG env U Γ' s i (e.liftN n k) (e'.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using H.weak' henv (Ctx.liftN_iff_lift'.1 W)

end Lean4Lean
