import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Verify.Typing.StructureUniq

/-!
# The level slack of `TrProj.uniq`, discharged

`Verify/Typing/ProjSpineInv.lean` reduces `TrProj.uniq` to `VEnv.ProjTermCongr`, and then to
`VEnv.ProjDataCongr`: at a *fixed* subject, any two `TrProj` derivations for one structure name
produce definitionally equal encodings.  `VEnv.IsStructure.projData_uniq` says exactly how far
apart the two derivations' data can be:

* `StructureAgree` — everything `addInduct'` writes into a constant, pinned by equality;
* `StructureLvlAgree` — the `lvl` fields, pinned only up to `≈` (and equality there is
  *refuted*, see `StructureUniq.lean`'s `structureUniq_eq_false`);
* `List.Forall₂ (· ≈ ·)` on the recorded universe arguments `us`;
* `List.Forall₂ IsDefEqU` on the parameter and index spines.

This file closes everything on that list except the last item.  The tool is `EqUpToLevels`
(`Theory/Typing/Strong.lean`): two terms with the same skeleton whose `const`/`sort` levels are
pointwise `≈`.  `VEnv.IsDefEq.eqUpToLevels` turns that relation into definitional equality
given a typing of one side, so the whole "levels-only" half of the residual is *not* a
`mkAppDF`-over-the-recursor-telescope problem at all — it is structural.

## What is proved

1. `EqUpToLevels` is closed under the term formers the projection encoding uses: `mkApp`,
   `mkLams`, `instAll`, `instAllTele`, `bvars`, `List.map (·.liftN n k)`, `++`, and it is
   reflexive on any term whose levels are `LevelWF U` (`refl_levelWF`), and stable under
   instantiating *one* term at `≈`-equivalent level lists (`instL_of_wf`).
2. `VInductDecl'.projTerm_eqUpToLevels`: under `StructureAgree` + `StructureLvlAgree` and
   `≈` on `us`, the two encodings are `EqUpToLevels` — with the parameter, index and subject
   arguments related by `EqUpToLevels` rather than required equal, so the lemma is reusable
   for the spine half's base cases.
3. `VInductDecl'.projTerm_defeq_of_levels`: hence definitionally equal, given a typing of one
   side and `LevelWF` for the spines and subject (`VEnv.levelWF_of_hasType` supplies those
   from typings).

## What is left

Only the spine half: `ps₁ ≈ ps₂` and `ιs₁ ≈ ιs₂` pointwise *definitional* equality, at one
fixed record and one fixed level list.  That is the `VEnv.IsDefEq.mkAppDF`-over-`projArgs`
recursion, and it is the only part of `ProjTermCongr` that needs the `Verify/Typing/ProjGen*`
typing family.

Nothing in this file uses `VEnv.WF` beyond `Ordered` (via `eqUpToLevels`), and nothing here is
`sorry`-tainted on its own account: items 1 and 2 are purely syntactic.
-/

namespace Lean4Lean
open VExpr

namespace VEnv
namespace EqUpToLevels

theorem refl_levelWF {U : Nat} : ∀ {e : VExpr}, e.LevelWF U → EqUpToLevels U e e
  | .bvar _, _ => .bvar
  | .sort _, h => .sort h h rfl
  | .const _ _, h => .const h h (List.Forall₂.rfl fun _ _ => rfl)
  | .app _ _, h => .app (refl_levelWF h.1) (refl_levelWF h.2)
  | .lam _ _, h => .lam (refl_levelWF h.1) (refl_levelWF h.2)
  | .forallE _ _, h => .forallE (refl_levelWF h.1) (refl_levelWF h.2)

theorem instL_of_wf {U : Nat} {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) ls ls') :
    ∀ e : VExpr, EqUpToLevels U (e.instL ls) (e.instL ls')
  | .bvar _ => .bvar
  | .sort _ => .sort (.inst hls) (.inst hls') (VLevel.inst_congr rfl heq)
  | .const _ _ => .const
      (List.forall_mem_map.2 fun _ _ => .inst hls)
      (List.forall_mem_map.2 fun _ _ => .inst hls')
      (List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <|
        List.Forall₂.rfl fun _ _ => VLevel.inst_congr rfl heq)
  | .app _ _ => .app (instL_of_wf hls hls' heq _) (instL_of_wf hls hls' heq _)
  | .lam _ _ => .lam (instL_of_wf hls hls' heq _) (instL_of_wf hls hls' heq _)
  | .forallE _ _ => .forallE (instL_of_wf hls hls' heq _) (instL_of_wf hls hls' heq _)

theorem mkApp {U : Nat} {as as' : List VExpr} (has : List.Forall₂ (EqUpToLevels U) as as') :
    ∀ {f f' : VExpr}, EqUpToLevels U f f' → EqUpToLevels U (f.mkApp as) (f'.mkApp as') := by
  induction has with
  | nil => exact fun hf => hf
  | cons h _ ih => exact fun hf => ih (.app hf h)

theorem mkLams {U : Nat} {b b' : VExpr} : ∀ {As As' : List VExpr},
    List.Forall₂ (EqUpToLevels U) As As' → EqUpToLevels U b b' →
    EqUpToLevels U (VExpr.mkLams As b) (VExpr.mkLams As' b')
  | [], [], _, hb => hb
  | _ :: _, _ :: _, .cons h t, hb => .lam h (mkLams t hb)

theorem bvars {U lo n : Nat} : List.Forall₂ (EqUpToLevels U) (VExpr.bvars lo n) (VExpr.bvars lo n) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons .bvar ih

theorem map_liftN {U n k : Nat} : ∀ {ps ps' : List VExpr},
    List.Forall₂ (EqUpToLevels U) ps ps' →
    List.Forall₂ (EqUpToLevels U) (ps.map (·.liftN n k)) (ps'.map (·.liftN n k))
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h t => .cons h.weakN (map_liftN t)

theorem map_instL {U : Nat} {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U)
    (heq : List.Forall₂ (· ≈ ·) ls ls') : ∀ (es : List VExpr),
    List.Forall₂ (EqUpToLevels U) (es.map (VExpr.instL ls)) (es.map (VExpr.instL ls'))
  | [] => .nil
  | _ :: es => .cons (instL_of_wf hls hls' heq _) (map_instL hls hls' heq es)

theorem instAll {U : Nat} : ∀ {as as' : List VExpr} {e e' : VExpr} {k : Nat},
    EqUpToLevels U e e' → List.Forall₂ (EqUpToLevels U) as as' →
    EqUpToLevels U (VExpr.instAll e as k) (VExpr.instAll e' as' k)
  | [], [], _, _, _, he, _ => he
  | _ :: _, _ :: _, _, _, _, he, .cons h t => by
    rw [VExpr.instAll, VExpr.instAll, List.Forall₂.length_eq t]
    exact instAll (EqUpToLevels.instN h he) t

theorem instAllTele {U : Nat} : ∀ {As As' as as' : List VExpr} {k : Nat},
    List.Forall₂ (EqUpToLevels U) As As' → List.Forall₂ (EqUpToLevels U) as as' →
    List.Forall₂ (EqUpToLevels U) (VExpr.instAllTele As as k) (VExpr.instAllTele As' as' k)
  | [], [], _, _, _, _, _ => .nil
  | _ :: _, _ :: _, _, _, _, .cons h t, has =>
    .cons (instAll h has) (instAllTele t has)

theorem append {U : Nat} : ∀ {as as' bs bs' : List VExpr},
    List.Forall₂ (EqUpToLevels U) as as' → List.Forall₂ (EqUpToLevels U) bs bs' →
    List.Forall₂ (EqUpToLevels U) (as ++ bs) (as' ++ bs')
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, .cons h t, hb => .cons h (append t hb)

theorem map_type_instL (us : List VLevel) : ∀ l : List VIndField,
    l.map (fun F => F.type.instL us) = (l.map (·.type)).map (VExpr.instL us)
  | [] => rfl
  | _ :: l => by simp [map_type_instL us l]

end EqUpToLevels
end VEnv

theorem VIndField.Agree.getD_type : ∀ {l₁ l₂ : List VIndField},
    List.Forall₂ VIndField.Agree l₁ l₂ → ∀ k : Nat,
    (l₁.getD k default).type = (l₂.getD k default).type
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, .cons h t, k => by
    match k with
    | 0 => exact h.type
    | _+1 => exact VIndField.Agree.getD_type t _

theorem StructureAgree.fields_map_instL {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType}
    {C₁ C₂ : VIndCtor} (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂) (us : List VLevel) :
    C₁.fields.map (fun F => F.type.instL us) = C₂.fields.map (fun F => F.type.instL us) := by
  rw [VEnv.EqUpToLevels.map_type_instL, VEnv.EqUpToLevels.map_type_instL, hag.fields_map]

theorem StructureAgree.field_type {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂) (k : Nat) :
    (C₁.fields.getD k default).type = (C₂.fields.getD k default).type :=
  VIndField.Agree.getD_type hag.fields k

section
open VEnv
variable {U : Nat} {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
  {us₁ us₂ : List VLevel} {ps₁ ps₂ is₁ is₂ earlier₁ earlier₂ : List VExpr} {e₁ e₂ : VExpr}

theorem VInductDecl'.projLvls_forall₂ (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂)
    (hlv : StructureLvlAgree D₁ C₁ D₂ C₂) (hus : List.Forall₂ (· ≈ ·) us₁ us₂) (i : Nat) :
    List.Forall₂ (· ≈ ·) (D₁.projLvls C₁ us₁ i) (D₂.projLvls C₂ us₂ i) := by
  rw [VInductDecl'.projLvls, VInductDecl'.projLvls, hag.isLE]
  split
  · exact .cons (VLevel.inst_congr (hlv.fields i) hus) hus
  · exact hus

theorem VInductDecl'.projLvls_levelWF (hu₁ : ∀ l ∈ us₁, l.WF U) (i : Nat) :
    ∀ l ∈ D₁.projLvls C₁ us₁ i, l.WF U := by
  rw [VInductDecl'.projLvls]
  split
  · exact fun l hl => by
      rcases List.mem_cons.1 hl with rfl | hl
      · exact .inst hu₁
      · exact hu₁ _ hl
  · exact hu₁

theorem VIndType.projMotive_eqUpToLevels (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂)
    (hu₁ : ∀ l ∈ us₁, l.WF U) (hu₂ : ∀ l ∈ us₂, l.WF U) (hus : List.Forall₂ (· ≈ ·) us₁ us₂)
    (hps : List.Forall₂ (EqUpToLevels U) ps₁ ps₂)
    (his : List.Forall₂ (EqUpToLevels U) is₁ is₂)
    (hea : List.Forall₂ (EqUpToLevels U) earlier₁ earlier₂) (i : Nat) :
    EqUpToLevels U (T₁.projMotive C₁ us₁ ps₁ is₁ i earlier₁)
      (T₂.projMotive C₂ us₂ ps₂ is₂ i earlier₂) := by
  have hlen := List.Forall₂.length_eq his
  rw [VIndType.projMotive, VIndType.projMotive, hag.tyName, hag.indices, hag.field_type i, ← hlen]
  refine EqUpToLevels.mkLams
    (EqUpToLevels.instAllTele (EqUpToLevels.map_instL hu₁ hu₂ hus _) hps) (.lam ?_ ?_)
  · exact EqUpToLevels.mkApp
      (EqUpToLevels.append (EqUpToLevels.map_liftN hps) EqUpToLevels.bvars)
      (.const hu₁ hu₂ hus)
  · exact EqUpToLevels.instAll (EqUpToLevels.instL_of_wf hu₁ hu₂ hus _)
      (EqUpToLevels.append (EqUpToLevels.map_liftN hps) hea)

theorem VIndCtor.projMinor_eqUpToLevels (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂)
    (hu₁ : ∀ l ∈ us₁, l.WF U) (hu₂ : ∀ l ∈ us₂, l.WF U) (hus : List.Forall₂ (· ≈ ·) us₁ us₂)
    (hps : List.Forall₂ (EqUpToLevels U) ps₁ ps₂) (i : Nat) :
    EqUpToLevels U (C₁.projMinor us₁ ps₁ i) (C₂.projMinor us₂ ps₂ i) := by
  rw [VIndCtor.projMinor, VIndCtor.projMinor, EqUpToLevels.map_type_instL,
    EqUpToLevels.map_type_instL, hag.fields_map, hag.fields_length]
  exact EqUpToLevels.mkLams
    (EqUpToLevels.instAllTele (EqUpToLevels.map_instL hu₁ hu₂ hus _) hps) .bvar

theorem VInductDecl'.projCore_eqUpToLevels (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂)
    (hlv : StructureLvlAgree D₁ C₁ D₂ C₂)
    (hu₁ : ∀ l ∈ us₁, l.WF U) (hu₂ : ∀ l ∈ us₂, l.WF U) (hus : List.Forall₂ (· ≈ ·) us₁ us₂)
    (hps : List.Forall₂ (EqUpToLevels U) ps₁ ps₂)
    (his : List.Forall₂ (EqUpToLevels U) is₁ is₂)
    (hea : List.Forall₂ (EqUpToLevels U) earlier₁ earlier₂)
    (he : EqUpToLevels U e₁ e₂) (i : Nat) :
    EqUpToLevels U (D₁.projCore T₁ C₁ us₁ ps₁ is₁ i earlier₁ e₁)
      (D₂.projCore T₂ C₂ us₂ ps₂ is₂ i earlier₂ e₂) := by
  rw [VInductDecl'.projCore_eq, VInductDecl'.projCore_eq, hag.tyName]
  refine EqUpToLevels.mkApp ?_
    (.const (D₁.projLvls_levelWF hu₁ i) (D₂.projLvls_levelWF hu₂ i)
      (D₁.projLvls_forall₂ hag hlv hus i))
  exact EqUpToLevels.append (EqUpToLevels.append (EqUpToLevels.append hps
    (.cons (T₁.projMotive_eqUpToLevels hag hu₁ hu₂ hus hps his hea i)
      (.cons (C₁.projMinor_eqUpToLevels hag hu₁ hu₂ hus hps i) .nil))) his) (.cons he .nil)

theorem VInductDecl'.projArgs_eqUpToLevels (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂)
    (hlv : StructureLvlAgree D₁ C₁ D₂ C₂)
    (hu₁ : ∀ l ∈ us₁, l.WF U) (hu₂ : ∀ l ∈ us₂, l.WF U) (hus : List.Forall₂ (· ≈ ·) us₁ us₂) :
    ∀ (i : Nat) {ps₁ ps₂ is₁ is₂ : List VExpr},
      List.Forall₂ (EqUpToLevels U) ps₁ ps₂ → List.Forall₂ (EqUpToLevels U) is₁ is₂ →
      List.Forall₂ (EqUpToLevels U) (D₁.projArgs T₁ C₁ us₁ ps₁ is₁ i)
        (D₂.projArgs T₂ C₂ us₂ ps₂ is₂ i)
  | 0, _, _, _, _, _, _ => .nil
  | i+1, _, _, _, _, hps, his => by
    have hlen := List.Forall₂.length_eq his
    rw [VInductDecl'.projArgs, VInductDecl'.projArgs, ← hlen]
    refine EqUpToLevels.append
      (projArgs_eqUpToLevels hag hlv hu₁ hu₂ hus i hps his) (.cons ?_ .nil)
    exact D₁.projCore_eqUpToLevels hag hlv hu₁ hu₂ hus hps his
      (projArgs_eqUpToLevels hag hlv hu₁ hu₂ hus i (EqUpToLevels.map_liftN hps)
        EqUpToLevels.bvars) .bvar i

theorem VInductDecl'.projTerm_eqUpToLevels (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂)
    (hlv : StructureLvlAgree D₁ C₁ D₂ C₂)
    (hu₁ : ∀ l ∈ us₁, l.WF U) (hu₂ : ∀ l ∈ us₂, l.WF U) (hus : List.Forall₂ (· ≈ ·) us₁ us₂)
    (hps : List.Forall₂ (EqUpToLevels U) ps₁ ps₂)
    (his : List.Forall₂ (EqUpToLevels U) is₁ is₂) (he : EqUpToLevels U e₁ e₂) (i : Nat) :
    EqUpToLevels U (D₁.projTerm T₁ C₁ us₁ ps₁ is₁ i e₁)
      (D₂.projTerm T₂ C₂ us₂ ps₂ is₂ i e₂) := by
  have hlen := List.Forall₂.length_eq his
  rw [VInductDecl'.projTerm, VInductDecl'.projTerm, ← hlen]
  exact D₁.projCore_eqUpToLevels hag hlv hu₁ hu₂ hus hps his
    (D₁.projArgs_eqUpToLevels hag hlv hu₁ hu₂ hus i (EqUpToLevels.map_liftN hps)
      EqUpToLevels.bvars) he i

/-! ### From `EqUpToLevels` to definitional equality -/

theorem VEnv.levelWF_of_hasType {env : VEnv} {Γ : List VExpr} {e A : VExpr}
    (henv : VEnv.Ordered env) (hΓ : OnCtx Γ (env.IsType U)) (h : env.HasType U Γ e A) :
    e.LevelWF U := (h.levelWF (VEnv.CtxStrong.strong henv hΓ).levelWF).1

theorem VEnv.eqUpToLevels_refl_of_hasType {env : VEnv} {Γ : List VExpr} {e A : VExpr}
    (henv : VEnv.Ordered env) (hΓ : OnCtx Γ (env.IsType U)) (h : env.HasType U Γ e A) :
    EqUpToLevels U e e :=
  EqUpToLevels.refl_levelWF (VEnv.levelWF_of_hasType henv hΓ h)

/-- **The record slack of `ProjDataCongr`, discharged.**  Two structure records that satisfy
`StructureAgree` and `StructureLvlAgree`, at `≈`-equivalent level arguments and the *same*
parameters, indices and subject, encode definitionally equal projections. -/
theorem VInductDecl'.projTerm_defeq_of_levels {env : VEnv} {Γ : List VExpr} {i : Nat}
    {ps ιs : List VExpr} {e X : VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hag : StructureAgree D₁ T₁ C₁ D₂ T₂ C₂) (hlv : StructureLvlAgree D₁ C₁ D₂ C₂)
    (hu₁ : ∀ l ∈ us₁, l.WF U) (hu₂ : ∀ l ∈ us₂, l.WF U) (hus : List.Forall₂ (· ≈ ·) us₁ us₂)
    (hps : ∀ p ∈ ps, p.LevelWF U) (hιs : ∀ x ∈ ιs, x.LevelWF U) (he : e.LevelWF U)
    (hty : env.HasType U Γ (D₁.projTerm T₁ C₁ us₁ ps ιs i e) X) :
    env.IsDefEqU U Γ (D₁.projTerm T₁ C₁ us₁ ps ιs i e) (D₂.projTerm T₂ C₂ us₂ ps ιs i e) :=
  ⟨_, VEnv.IsDefEq.eqUpToLevels henv.ordered hΓ hty
    (D₁.projTerm_eqUpToLevels hag hlv hu₁ hu₂ hus
      (List.Forall₂.rfl fun p hp => EqUpToLevels.refl_levelWF (hps p hp))
      (List.Forall₂.rfl fun x hx => EqUpToLevels.refl_levelWF (hιs x hx))
      (EqUpToLevels.refl_levelWF he) i)⟩

end
end Lean4Lean
