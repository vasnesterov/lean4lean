import Lean4Lean.Verify.Typing.StructureUniq

/-!
# `VEnv.RecTypeResidual`, proved: ledger G4 closes

`Verify/Typing/StructureUniq.lean` reduced `VEnv.StructureUniq` (ledger G4) to three
syntactic equations,

    D₁.params = D₂.params ∧ T₁.indices = T₂.indices ∧ C₁.name = C₂.name

packaged as `VEnv.RecTypeResidual`, and proved `VEnv.structureUniq_of` off it.  This file
supplies the residual, so `VEnv.StructureUniq` follows from `VEnv.WF` alone
(`VEnv.WF.structureUniq`).

**What makes it work, and why the earlier attempt (`RecTypeInj`) could not.**
`recTypeInj_false` shows that the recursor's declared type does *not* determine
`VIndCtor.params`; the three equations above are exactly the part it does determine, and the
one environment fact needed is **level well-formedness of the parameter and index
telescopes**, which `RecTypeInj` had no way to state.  It is what inverts
`VInductDecl'.atRec` — the re-indexing of a stored telescope into the recursor's universe
numbering (F10) — on the nose: re-instantiate at `.zero :: VLevel.params uvars` and
`VInductDecl'.selfLvls_inst` collapses the round trip.

The peel itself needs **no new injectivity machinery**: `mkPi_inj_of_arity`,
`mkApp_inj_of_arity`, `piArity_mkApp` and `List.append_inj` do all of it, and
`VInductDecl'.motives_eq`/`minors_eq` (`Theory/Inductive/StructureClosed.lean`) already
collapse the two singleton blocks.  Two genuinely missing primitives are added here:
`VExpr.liftTele_inj` and `atRec`/`atRecTele` injectivity.

Route:

* §1 the two missing primitives.
* §2 `atRec` is injective on `LevelWF D.uvars` terms.
* §3 level well-formedness of `D.params` and `T.indices`, off `IsStructure.decl`.
* §4 `D.recType 0` peels into the four telescope blocks.
* §5 `D.minorType 0 0 C` peels to the constructor application, giving `C.name`.
* §6 the residual, and G4.
-/

namespace Lean4Lean

open VExpr

/-! ## 1. Missing telescope primitives -/

namespace VExpr

/-- Lifting a declaration-order telescope is injective. -/
theorem liftTele_inj : ∀ {As Bs : List VExpr} {n k : Nat},
    liftTele n As k = liftTele n Bs k → As = Bs
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | A :: As, B :: Bs, n, k, h => by
    simp only [liftTele_cons, List.cons.injEq] at h
    rw [liftN_inj.1 h.1, liftTele_inj h.2]

end VExpr

/-- `OnCtx` with a context-independent predicate is membership. -/
theorem onCtx_forall_mem {P : VExpr → Prop} : ∀ {Γ : List VExpr},
    OnCtx Γ (fun _ A => P A) → ∀ A ∈ Γ, P A
  | [], _, _, h => nomatch h
  | _ :: _, ⟨h1, h2⟩, _, hmem => by
    rcases List.mem_cons.1 hmem with rfl | hmem
    · exact h2
    · exact onCtx_forall_mem h1 _ hmem

/-! ## 2. `atRec` is invertible on level-well-formed terms

`atRec e = e.instL D.selfLvls`, and `selfLvls` is a shift of the block's own universe
parameters, so it has a left inverse: instantiate at `.zero :: VLevel.params uvars` (or at
`VLevel.params uvars` when `isLE = false`).  `selfLvls_inst` is exactly that computation;
`LevelWF.instL_id` then cancels the residual `instL (params uvars)`. -/

namespace VInductDecl'

/-- The inverse level list for `atRec`. -/
def unRecLvls (D : VInductDecl') : List VLevel :=
  if D.isLE then VLevel.zero :: VLevel.params D.uvars else VLevel.params D.uvars

theorem selfLvls_map_unRecLvls (D : VInductDecl') :
    D.selfLvls.map (VLevel.inst D.unRecLvls) = VLevel.params D.uvars :=
  D.selfLvls_inst VLevel.zero VLevel.params_length

/-- **`atRec` is injective on terms whose levels are the block's own.** -/
theorem atRec_inj (D : VInductDecl') {e₁ e₂ : VExpr}
    (h₁ : e₁.LevelWF D.uvars) (h₂ : e₂.LevelWF D.uvars)
    (h : D.atRec e₁ = D.atRec e₂) : e₁ = e₂ := by
  have key := congrArg (VExpr.instL D.unRecLvls) h
  simp only [VInductDecl'.atRec, VExpr.instL_instL, D.selfLvls_map_unRecLvls] at key
  rwa [h₁.instL_id, h₂.instL_id] at key

/-- …and so is `atRecTele`. -/
theorem atRecTele_inj (D : VInductDecl') : ∀ {As Bs : List VExpr},
    (∀ A ∈ As, A.LevelWF D.uvars) → (∀ B ∈ Bs, B.LevelWF D.uvars) →
    D.atRecTele As = D.atRecTele Bs → As = Bs
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [VInductDecl'.atRecTele] at h
  | _ :: _, [], _, _, h => by simp [VInductDecl'.atRecTele] at h
  | A :: As, B :: Bs, h₁, h₂, h => by
    rw [VInductDecl'.atRecTele, VInductDecl'.atRecTele, List.map_cons, List.map_cons] at h
    obtain ⟨e1, e2⟩ := List.cons.inj h
    have hA : A = B := D.atRec_inj (h₁ _ (by simp)) (h₂ _ (by simp)) e1
    have hAs : As = Bs := D.atRecTele_inj
      (fun A hA => h₁ A (by simp [hA])) (fun B hB => h₂ B (by simp [hB])) e2
    rw [hA, hAs]

end VInductDecl'

/-! ## 3. Level well-formedness of the stored telescopes

`IsStructure.decl` carries `D.WF env₀` for some `env₀ ≤ env`; `VIndType.WF.indices` is an
`OnCtx` over `T.indices.reverse ++ D.params.reverse`, which `CtxStrong.strong` upgrades and
`CtxStrong.levelWF` reads off. -/

variable {env : VEnv} {S : Lean.Name} {D : VInductDecl'} {T : VIndType} {C : VIndCtor}

theorem VEnv.IsStructure.levelWF (henv : env.Ordered) (H : env.IsStructure S D T C) :
    (∀ A ∈ D.params, A.LevelWF D.uvars) ∧ (∀ A ∈ T.indices, A.LevelWF D.uvars) := by
  obtain ⟨env₀, env₁, hWF, hadd, hle⟩ := H.decl
  have hle₀ : env₀ ≤ env := (VEnv.addInduct'_le hadd).trans hle
  have hT : T ∈ D.types := by rw [H.types]; exact List.mem_singleton_self _
  have hidx : OnCtx (T.indices.reverse ++ D.params.reverse) (env.IsType D.uvars) :=
    OnCtx.mono (fun hh => hh.mono hle₀) (hWF.types T hT).indices
  have key := onCtx_forall_mem (P := fun A => A.LevelWF D.uvars)
    (CtxStrong.strong henv hidx).levelWF
  refine ⟨fun A hA => key A ?_, fun A hA => key A ?_⟩ <;> simp [List.mem_append, hA]

/-! ## 4. Peeling the recursor type -/

namespace VInductDecl'

/-- The recursor's binder telescope, as one list. -/
def recTele (D : VInductDecl') (T : VIndType) : List VExpr :=
  D.atRecTele D.params ++ D.motives ++ D.minors ++
    liftTele (D.nm + D.nmin) (D.atRecTele T.indices)

/-- `recType 0`, with the block's single type substituted and the major premise folded into
the binder telescope.  A restatement of the definition, nothing more. -/
theorem recType_zero_eq (D : VInductDecl') (T : VIndType) (hT : D.types.getD 0 default = T) :
    D.recType 0 = mkPi (D.recTele T ++
        [D.tyApp' 0 (T.indices.length + D.nmin + D.nm) (bvars 0 T.indices.length)])
      ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - 0))).mkApp
        (bvars 1 T.indices.length ++ [.bvar 0])) := by
  rw [VInductDecl'.recType]
  simp only [hT, recTele, VExpr.mkPi_append, VExpr.mkPi_cons, VExpr.mkPi_nil]

end VInductDecl'

/-! ## 5. Peeling a minor premise -/

namespace VInductDecl'

/-- With no recursive fields there are no induction hypotheses. -/
theorem ihTypes_eq_nil (D : VInductDecl') (C : VIndCtor) (h : C.recFields = []) (q : Nat) :
    D.ihTypes q C = [] := by simp [ihTypes, h]

/-- `minorType 0 0 C` for a structure: the ih block is empty, so the whole minor premise is
the field telescope over one constructor application. -/
theorem minorType_zero_eq (D : VInductDecl') (C : VIndCtor) (h : C.recFields = []) :
    D.minorType 0 0 C = mkPi (liftTele (D.nm + 0) (D.atRecTele (C.fields.map (·.type))))
      ((VExpr.bvar (0 + C.fields.length + 0 + (D.nm - 1 - 0))).mkApp
        (C.args.map (fun a => shift (D.nm + 0) 0 C.fields.length (D.atRec a)) ++
          [D.ctorApp' C (0 + C.fields.length + (D.nm + 0)) (bvars 0 C.fields.length)])) := by
  rw [VInductDecl'.minorType]
  simp only [D.ihTypes_eq_nil C h, List.length_nil, List.append_nil]

end VInductDecl'

/-! ## 6. The residual, and G4 -/

/-- **`VEnv.RecTypeResidual`, proved.**

The recursor's declared type is one `mkPi` over
`atRecTele params ++ motives ++ minors ++ liftTele 2 (atRecTele indices) ++ [major]`, whose
body is `motive indices major`.  Because the two derivations' recursor types are equal
(`IsStructure.fingerprint`):

* the body's spine length gives `T₁.indices.length = T₂.indices.length`, and then the
  telescope's total length gives `D₁.np = D₂.np`;
* with all four block lengths equal (`motives_eq`/`minors_eq` make the middle two
  singletons), `List.append_inj` splits the telescope, handing over `atRecTele params`,
  `minors` and `liftTele 2 (atRecTele indices)` blockwise;
* `atRecTele_inj` (§2, on the strength of §3) inverts the level re-indexing, giving
  `D.params` and `T.indices` on the nose;
* `noRec` kills the ih telescope of the single minor premise, and the constructor
  application at the end of its body carries `C.name`. -/
theorem VEnv.recTypeResidual_of_wf {env : VEnv} (henv : VEnv.WF env) : env.RecTypeResidual := by
  intro S D₁ D₂ T₁ T₂ C₁ C₂ H₁ H₂
  obtain ⟨hu, -, -, hrt⟩ := H₁.fingerprint H₂
  have hisLE := H₁.isLE_eq H₂
  have hsl : D₁.selfLvls = D₂.selfLvls := by simp [VInductDecl'.selfLvls, hu, hisLE]
  have hnm₁ := H₁.nm_eq; have hnm₂ := H₂.nm_eq
  have hnmin₁ := H₁.nmin_eq; have hnmin₂ := H₂.nmin_eq
  -- the two singleton blocks
  have hlm₁ : D₁.motives.length = 1 := by rw [VInductDecl'.motives_eq H₁]; rfl
  have hlm₂ : D₂.motives.length = 1 := by rw [VInductDecl'.motives_eq H₂]; rfl
  have hlmin₁ : D₁.minors.length = 1 := by rw [VInductDecl'.minors_eq H₁]; rfl
  have hlmin₂ : D₂.minors.length = 1 := by rw [VInductDecl'.minors_eq H₂]; rfl
  rw [D₁.recType_zero_eq T₁ H₁.typesD, D₂.recType_zero_eq T₂ H₂.typesD] at hrt
  obtain ⟨hTele, hinner⟩ := VExpr.mkPi_inj_of_arity
    (VExpr.piArity_mkApp rfl) (VExpr.piArity_mkApp rfl) hrt
  -- the motive's spine gives the index count
  obtain ⟨-, hargs⟩ :=
    VExpr.mkApp_inj_of_arity (f := VExpr.bvar _) (g := VExpr.bvar _) rfl rfl hinner
  have hni : T₁.indices.length = T₂.indices.length := by
    have := congrArg List.length hargs; simp at this; omega
  -- the telescope's length gives the parameter count
  have hlenT : (D₁.recTele T₁).length = (D₂.recTele T₂).length := by
    have := congrArg List.length hTele
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  have hnp : D₁.params.length = D₂.params.length := by
    simp only [VInductDecl'.recTele, List.length_append, VInductDecl'.length_atRecTele,
      VExpr.length_liftTele, hlm₁, hlm₂, hlmin₁, hlmin₂] at hlenT
    omega
  have hRT : D₁.recTele T₁ = D₂.recTele T₂ := (List.append_inj hTele hlenT).1
  -- split the four blocks
  rw [VInductDecl'.recTele, VInductDecl'.recTele] at hRT
  obtain ⟨hRT', hidxBlock⟩ := List.append_inj hRT (by
    simp only [List.length_append, VInductDecl'.length_atRecTele, hlm₁, hlm₂, hlmin₁, hlmin₂,
      hnp])
  obtain ⟨hRT'', hminBlock⟩ := List.append_inj hRT' (by
    simp only [List.length_append, VInductDecl'.length_atRecTele, hlm₁, hlm₂, hnp])
  have hparBlock := (List.append_inj hRT'' (by
    simp only [VInductDecl'.length_atRecTele, hnp])).1
  -- level well-formedness of the stored telescopes
  obtain ⟨hwp₁, hwi₁⟩ := H₁.levelWF henv.ordered
  obtain ⟨hwp₂, hwi₂⟩ := H₂.levelWF henv.ordered
  rw [← hu] at hwp₂ hwi₂
  have hatR : ∀ As : List VExpr, D₂.atRecTele As = D₁.atRecTele As := by
    intro As; simp [VInductDecl'.atRecTele, hsl]
  -- parameters
  have hpar : D₁.params = D₂.params :=
    D₁.atRecTele_inj hwp₁ hwp₂ (by rw [hparBlock, hatR])
  -- indices
  have hidx : T₁.indices = T₂.indices := by
    rw [hnm₁, hnm₂, hnmin₁, hnmin₂] at hidxBlock
    exact D₁.atRecTele_inj hwi₁ hwi₂ (by rw [VExpr.liftTele_inj hidxBlock, hatR])
  -- the constructor's name, off the single minor premise
  rw [VInductDecl'.minors_eq H₁, VInductDecl'.minors_eq H₂] at hminBlock
  have hmin := (List.cons.inj hminBlock).1
  rw [D₁.minorType_zero_eq C₁ H₁.noRec, D₂.minorType_zero_eq C₂ H₂.noRec] at hmin
  obtain ⟨-, hmbody⟩ := VExpr.mkPi_inj_of_arity
    (VExpr.piArity_mkApp rfl) (VExpr.piArity_mkApp rfl) hmin
  obtain ⟨-, hmargs⟩ :=
    VExpr.mkApp_inj_of_arity (f := VExpr.bvar _) (g := VExpr.bvar _) rfl rfl hmbody
  have hcapp := (List.append_inj hmargs (by
    have := congrArg List.length hmargs; simp at this ⊢; omega)).2
  have hcapp' := (List.cons.inj hcapp).1
  rw [VInductDecl'.ctorApp', VInductDecl'.ctorApp'] at hcapp'
  have hconst := (VExpr.mkApp_inj_of_arity (f := VExpr.const C₁.name D₁.selfLvls)
    (g := VExpr.const C₂.name D₂.selfLvls) rfl rfl hcapp').1
  exact ⟨hpar, hidx, (VExpr.const.inj hconst).1⟩

/-- **Ledger G4, closed.**  `VEnv.StructureUniq` from `VEnv.WF` alone. -/
theorem VEnv.WF.structureUniq {env : VEnv} (henv : VEnv.WF env) : env.StructureUniq :=
  VEnv.structureUniq_of henv (VEnv.recTypeResidual_of_wf henv)

end Lean4Lean
