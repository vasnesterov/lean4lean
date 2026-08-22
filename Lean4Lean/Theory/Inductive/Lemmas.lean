import Lean4Lean.Theory.Inductive.Decl
import Lean4Lean.Theory.Typing.Meta

/-!
# Metatheory groundwork for `addInduct_WF`

Three groups, in dependency order.

1. **Level re-indexing** (`§ atRec`).  `IsDefEq.instL` already exists
   (`Theory/Typing/Lemmas.lean:595`); what is missing is its specialisation to
   `VInductDecl'.atRec`, together with the syntactic algebra saying that `atRec` commutes
   with the telescope operations and turns `tyApp` into `tyApp'`.  This is what lets a
   `WF` fact stated at the block's own universe numbering type the recursor at the
   recursor's numbering.

2. **Staging** (`§ addConstList`, `§ staging`).  `addIndTypes`/`addIndCtors`/`addIndRecs`
   are all `addConstList`, so the bookkeeping is proved once: monotonicity, what the
   resulting `constants` map is, which names were added, `Ordered` preservation, and
   `addInduct' env D = some _ ↔ D.allNames` fresh and duplicate-free.

3. **Well-formedness of the generated types** (`§ telescopes`, `§ generated types`).
   The telescope typing library (`OnCtx.append_right`, `IsType.mkPi`, `HasType.mkApp'`,
   `HasType.appBVars`), then the inductive types' and constructors' constants, then the
   pieces of the recursor case that are within reach.

`addInduct_WF` itself lives in `Theory/Typing/InductiveLemmas.lean` and is deliberately
not here.
-/

namespace Lean4Lean

open VExpr (mkPi mkLams mkApp bvars liftTele instTele shift shiftTele instAll)

/-! ## Generic list/telescope helpers -/

theorem List.foldlM_option_append {f : α → β → Option α} :
    ∀ {l₁ : List β} {l₂ : List β} {a : α},
      (l₁ ++ l₂).foldlM f a = (l₁.foldlM f a).bind (l₂.foldlM f ·)
  | [], _, a => rfl
  | b :: l₁, l₂, a => by
    simp only [List.cons_append, List.foldlM_cons]
    cases f a b with
    | none => simp
    | some a' => simp

/-! ## `OnCtx` over telescopes -/

theorem OnCtx.append_right : ∀ {Δ Γ}, OnCtx (Δ ++ Γ) P → OnCtx Γ P
  | [], _, h => h
  | _ :: _, _, h => OnCtx.append_right h.1

theorem OnCtx.head_of_append {Δ Γ : List VExpr} (h : OnCtx (Δ ++ A :: Γ) P) : P Γ A :=
  (OnCtx.append_right h).2

/-- Reassociate a declaration-order telescope's context: `(A :: As).reverse ++ Γ` is
`As.reverse ++ (A :: Γ)`. -/
theorem VExpr.tele_ctx_cons (A : VExpr) (As Γ : List VExpr) :
    (A :: As).reverse ++ Γ = As.reverse ++ (A :: Γ) := by simp

/-! ## `atRec`: re-indexing from the block's universes to the recursor's -/

namespace VInductDecl'
variable (D : VInductDecl')

@[simp] theorem length_selfLvls : D.selfLvls.length = D.uvars := by simp [selfLvls]

@[simp] theorem length_ownLvls : D.ownLvls.length = D.uvars := by simp [ownLvls]

/-- The recursor's copy of the block's universe parameters is well-formed at
`recUvars`. -/
theorem selfLvls_wf : ∀ l ∈ D.selfLvls, l.WF D.recUvars := by
  simp only [selfLvls, recUvars, List.mem_map, List.mem_range]
  rintro _ ⟨i, hi, rfl⟩
  by_cases h : D.isLE <;> simp [h, VLevel.WF] <;> omega

/-- Instantiating the block's own parameters `ownLvls` by `selfLvls` gives `selfLvls`:
this is what turns `tyApp` into `tyApp'`. -/
@[simp] theorem ownLvls_inst_selfLvls :
    D.ownLvls.map (VLevel.inst D.selfLvls) = D.selfLvls :=
  VLevel.inst_map_id (by simp)

@[simp] theorem atRecTele_nil : D.atRecTele [] = [] := rfl
@[simp] theorem atRecTele_cons :
    D.atRecTele (A :: As) = D.atRec A :: D.atRecTele As := rfl
@[simp] theorem length_atRecTele : (D.atRecTele As).length = As.length := by simp [atRecTele]
@[simp] theorem atRecTele_append :
    D.atRecTele (As ++ Bs) = D.atRecTele As ++ D.atRecTele Bs := by simp [atRecTele]
@[simp] theorem atRecTele_reverse :
    D.atRecTele As.reverse = (D.atRecTele As).reverse := by simp [atRecTele]
theorem atRecTele_map (f : α → VExpr) (l : List α) :
    D.atRecTele (l.map f) = l.map (fun a => D.atRec (f a)) := by simp [atRecTele, atRec]

/-! ### `atRec` commutes with the telescope algebra -/

@[simp] theorem atRec_sort : D.atRec (.sort u) = .sort (u.inst D.selfLvls) := rfl
@[simp] theorem atRec_bvar : D.atRec (.bvar i) = .bvar i := rfl
@[simp] theorem atRec_app : D.atRec (.app f a) = .app (D.atRec f) (D.atRec a) := rfl
@[simp] theorem atRec_lam : D.atRec (.lam A b) = .lam (D.atRec A) (D.atRec b) := rfl
@[simp] theorem atRec_forallE :
    D.atRec (.forallE A b) = .forallE (D.atRec A) (D.atRec b) := rfl
@[simp] theorem atRec_const :
    D.atRec (.const c ls) = .const c (ls.map (VLevel.inst D.selfLvls)) := rfl

@[simp] theorem atRec_mkPi : D.atRec (mkPi As B) = mkPi (D.atRecTele As) (D.atRec B) := by
  simp [atRec, atRecTele]
@[simp] theorem atRec_mkLams :
    D.atRec (mkLams As b) = mkLams (D.atRecTele As) (D.atRec b) := by simp [atRec, atRecTele]
@[simp] theorem atRec_mkApp :
    D.atRec (f.mkApp as) = (D.atRec f).mkApp (as.map D.atRec) := by
  simp only [atRec, VExpr.instL_mkApp]; rfl
@[simp] theorem atRec_bvars : (bvars lo n).map D.atRec = bvars lo n :=
  VExpr.map_instL_bvars
@[simp] theorem atRec_liftN : D.atRec (e.liftN n k) = (D.atRec e).liftN n k :=
  VExpr.instL_liftN
@[simp] theorem atRec_liftTele :
    D.atRecTele (liftTele n As k) = liftTele n (D.atRecTele As) k := by
  simp [atRecTele, VExpr.instL_liftTele]
@[simp] theorem atRec_shift : D.atRec (shift off d i e j) = shift off d i (D.atRec e) j := by
  simp [VExpr.shift, atRec]
@[simp] theorem atRec_shiftTele :
    D.atRecTele (shiftTele off d i As j) = shiftTele off d i (D.atRecTele As) j := by
  simp [atRecTele, VExpr.instL_shiftTele]

/-- The point of `atRec`: it carries `tyApp` (block numbering) to `tyApp'` (recursor
numbering). -/
@[simp] theorem atRec_tyApp :
    D.atRec (D.tyApp j k args) = D.tyApp' j k (args.map D.atRec) := by
  simp [tyApp, tyApp']

@[simp] theorem atRec_canonType (T : VIndType) :
    D.atRec (T.canonType D) =
      mkPi (D.atRecTele D.params ++ D.atRecTele T.indices) (.sort (D.lvl.inst D.selfLvls)) := by
  simp [VIndType.canonType]

/-! ### The typing transport -/

variable {env : VEnv} {Γ : List VExpr}

/-- The context of a judgment transported by `atRec`. -/
abbrev atRecCtx (Γ : List VExpr) : List VExpr := Γ.map (VExpr.instL D.selfLvls)

theorem atRecCtx_eq_atRecTele : D.atRecCtx Γ = D.atRecTele Γ := rfl

theorem atRec_isDefEq (H : env.IsDefEq D.uvars Γ e₁ e₂ A) :
    env.IsDefEq D.recUvars (D.atRecCtx Γ) (D.atRec e₁) (D.atRec e₂) (D.atRec A) :=
  H.instL D.selfLvls_wf

theorem atRec_hasType (H : env.HasType D.uvars Γ e A) :
    env.HasType D.recUvars (D.atRecCtx Γ) (D.atRec e) (D.atRec A) :=
  H.instL D.selfLvls_wf

theorem atRec_isType (H : env.IsType D.uvars Γ A) :
    env.IsType D.recUvars (D.atRecCtx Γ) (D.atRec A) :=
  H.instL D.selfLvls_wf

theorem atRec_isDefEqU (H : env.IsDefEqU D.uvars Γ e₁ e₂) :
    env.IsDefEqU D.recUvars (D.atRecCtx Γ) (D.atRec e₁) (D.atRec e₂) :=
  H.instL D.selfLvls_wf

theorem atRec_onCtx (H : OnCtx Γ (env.IsType D.uvars)) :
    OnCtx (D.atRecCtx Γ) (env.IsType D.recUvars) :=
  OnCtx.instL D.selfLvls_wf H

end VInductDecl'

/-! ## `addConstList` -/

namespace VEnv

theorem addConst_constants_ne {env env' : VEnv} {name ci n}
    (h : env.addConst name ci = some env') (hn : name ≠ n) :
    env'.constants n = env.constants n := by
  unfold VEnv.addConst at h; split at h <;> cases h; simp [hn]

theorem addConst_constants_none {env env' : VEnv} {name ci}
    (h : env.addConst name ci = some env') : env.constants name = none := by
  unfold VEnv.addConst at h; split at h <;> simp_all

theorem addConst_eq_none' {env : VEnv} {name ci}
    (h : env.constants name = none) : ∃ env', env.addConst name ci = some env' := by
  unfold VEnv.addConst; rw [h]; exact ⟨_, rfl⟩

@[simp] theorem addConstList_nil {env : VEnv} : env.addConstList [] = some env := rfl

theorem addConstList_cons {env : VEnv} {c cs} :
    env.addConstList (c :: cs) = (env.addConst c.1 c.2).bind (·.addConstList cs) := by
  cases h : env.addConst c.1 c.2 <;> simp [addConstList, List.foldlM, h]

theorem addConstList_append {env : VEnv} {cs ds} :
    env.addConstList (cs ++ ds) = (env.addConstList cs).bind (·.addConstList ds) :=
  List.foldlM_option_append

theorem addConstList_le : ∀ {cs} {env env' : VEnv}, env.addConstList cs = some env' → env ≤ env'
  | [], _, _, h => by cases h; exact .rfl
  | _ :: _, _, _, h => by
    rw [addConstList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConst_le h1).trans (addConstList_le h2)

/-- A name not in the list is untouched. -/
theorem addConstList_constants_of_not_mem : ∀ {cs} {env env' : VEnv} {n},
    env.addConstList cs = some env' → n ∉ cs.map (·.1) → env'.constants n = env.constants n
  | [], _, _, _, h, _ => by cases h; rfl
  | c :: cs, env, env', n, h, hn => by
    rw [addConstList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    rw [List.map_cons, List.mem_cons, not_or] at hn
    rw [addConstList_constants_of_not_mem h2 hn.2,
      addConst_constants_ne h1 (fun e => hn.1 e.symm)]

/-- Every constant in the list ends up in the environment. -/
theorem addConstList_constants : ∀ {cs} {env env' : VEnv},
    env.addConstList cs = some env' → ∀ c ∈ cs, env'.constants c.1 = some c.2
  | [], _, _, _, _, hc => nomatch hc
  | c :: cs, env, env', h, d, hd => by
    rw [addConstList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    cases hd with
    | head => exact (addConstList_le h2).constants (addConst_self h1)
    | tail _ hd => exact addConstList_constants h2 d hd

/-- Success means every name was fresh *and* the list had no duplicate names. -/
theorem addConstList_fresh : ∀ {cs} {env env' : VEnv},
    env.addConstList cs = some env' →
    (∀ n ∈ cs.map (·.1), env.constants n = none) ∧ (cs.map (·.1)).Nodup
  | [], _, _, _ => ⟨by simp, by simp⟩
  | c :: cs, env, env', h => by
    rw [addConstList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    have hc : env.constants c.1 = none := addConst_constants_none h1
    obtain ⟨hfresh, hnd⟩ := addConstList_fresh h2
    have hne : c.1 ∉ cs.map (·.1) := fun hm => by
      have h3 := hfresh _ hm; rw [addConst_self h1] at h3; simp at h3
    refine ⟨?_, by rw [List.map_cons]; exact List.nodup_cons.2 ⟨hne, hnd⟩⟩
    rw [List.map_cons]
    rintro n hn
    rcases List.mem_cons.1 hn with rfl | hm
    · exact hc
    · rw [← addConst_constants_ne h1 (fun e => hne (e ▸ hm))]
      exact hfresh _ hm

theorem exists_addConstList : ∀ {cs : List (Name × VConstant)} {env : VEnv},
    (∀ n ∈ cs.map (·.1), env.constants n = none) → (cs.map (·.1)).Nodup →
    ∃ env', env.addConstList cs = some env'
  | [], _, _, _ => ⟨_, rfl⟩
  | c :: cs, env, hfresh, hnd => by
    rw [List.map_cons] at hfresh hnd
    obtain ⟨env₁, h1⟩ := addConst_eq_none' (ci := c.2) (hfresh _ (.head _))
    rw [List.nodup_cons] at hnd
    have key : ∀ n ∈ cs.map (·.1), env₁.constants n = none := fun n hn => by
      rw [addConst_constants_ne h1 (fun e => hnd.1 (e ▸ hn))]
      exact hfresh _ (.tail _ hn)
    obtain ⟨env₂, h2⟩ := exists_addConstList (env := env₁) (cs := cs) key hnd.2
    exact ⟨env₂, by rw [addConstList_cons, h1]; exact h2⟩

theorem addConstList_eq_some_iff {env : VEnv} {cs : List (Name × VConstant)} :
    (∃ env', env.addConstList cs = some env') ↔
      (∀ n ∈ cs.map (·.1), env.constants n = none) ∧ (cs.map (·.1)).Nodup :=
  ⟨fun ⟨_, h⟩ => addConstList_fresh h, fun ⟨h1, h2⟩ => exists_addConstList h1 h2⟩

theorem addConstList_ordered : ∀ {cs} {env env' : VEnv}, Ordered env →
    (∀ c ∈ cs, c.2.WF env) → env.addConstList cs = some env' → Ordered env'
  | [], _, _, h, _, e => by cases e; exact h
  | _ :: _, _, _, h, hw, e => by
    rw [addConstList_cons, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    refine addConstList_ordered (.const h (hw _ (.head _)) h1) (fun c hc => ?_) h2
    exact (hw c (.tail _ hc)).mono (addConst_le h1)

end VEnv

/-! ## Staging: `addIndTypes` / `addIndCtors` / `addIndRecs` / `addIndRules` -/

namespace VInductDecl'
variable (D : VInductDecl')

@[simp] theorem typeConsts_names : D.typeConsts.map (·.1) = D.blockNames := by
  simp [typeConsts, blockNames]

@[simp] theorem length_typeConsts : D.typeConsts.length = D.nm := by simp [typeConsts]
@[simp] theorem length_ctorConsts : D.ctorConsts.length = D.nmin := by simp [ctorConsts]
@[simp] theorem length_recConsts : D.recConsts.length = D.nm := by simp [recConsts]

theorem allConsts_names :
    D.allNames = D.blockNames ++ D.ctorConsts.map (·.1) ++ D.recConsts.map (·.1) := by
  simp [allNames, allConsts]

end VInductDecl'

namespace VEnv
variable {env env' : VEnv} {D : VInductDecl'}

theorem addIndTypes_le (h : env.addIndTypes D = some env') : env ≤ env' := addConstList_le h
theorem addIndCtors_le (h : env.addIndCtors D = some env') : env ≤ env' := addConstList_le h
theorem addIndRecs_le (h : env.addIndRecs D = some env') : env ≤ env' := addConstList_le h

/-! ### `addIndRules` -/

theorem addDefEqList_le : ∀ (dfs : List VDefEq) (env : VEnv), env ≤ dfs.foldl VEnv.addDefEq env
  | [], _ => .rfl
  | d :: dfs, env => addDefEq_le.trans (addDefEqList_le dfs (env.addDefEq d))

theorem addDefEqList_constants :
    ∀ (dfs : List VDefEq) (env : VEnv), (dfs.foldl VEnv.addDefEq env).constants = env.constants
  | [], _ => rfl
  | d :: dfs, env => addDefEqList_constants dfs (env.addDefEq d)

theorem addDefEqList_defeqs : ∀ (dfs : List VDefEq) (env : VEnv),
    ∀ df ∈ dfs, (dfs.foldl VEnv.addDefEq env).defeqs df
  | [], _, _, h => nomatch h
  | d :: dfs, env, df, hdf => by
    cases hdf with
    | head => exact (addDefEqList_le dfs (env.addDefEq d)).defeqs addDefEq_self
    | tail _ h => exact addDefEqList_defeqs dfs (env.addDefEq d) df h

theorem addDefEqList_ordered : ∀ (dfs : List VDefEq) (env : VEnv), Ordered env →
    (∀ df ∈ dfs, df.WF env) → Ordered (dfs.foldl VEnv.addDefEq env)
  | [], _, h, _ => h
  | d :: dfs, env, h, hw =>
    addDefEqList_ordered dfs (env.addDefEq d) (.defeq h (hw _ (.head _)))
      fun df hdf => (hw df (.tail _ hdf)).mono addDefEq_le

theorem addIndRules_le {env : VEnv} {D : VInductDecl'} : env ≤ env.addIndRules D :=
  addDefEqList_le ..

theorem addIndRules_constants {env : VEnv} {D : VInductDecl'} :
    (env.addIndRules D).constants = env.constants := addDefEqList_constants ..

theorem addIndRules_defeqs {env : VEnv} {D : VInductDecl'} :
    ∀ df ∈ D.iotaRules, (env.addIndRules D).defeqs df :=
  fun df h => addDefEqList_defeqs _ _ df h

theorem addIndRules_ordered {env : VEnv} {D : VInductDecl'} (h : Ordered env)
    (hw : ∀ df ∈ D.iotaRules, df.WF env) : Ordered (env.addIndRules D) :=
  addDefEqList_ordered _ _ h hw

/-- The three constant-adding stages, composed. -/
theorem addInduct'_eq (env : VEnv) (D : VInductDecl') :
    env.addInduct' D = (env.addConstList D.allConsts).map (·.addIndRules D) := by
  show (do
      let env ← env.addIndTypes D
      let env ← env.addIndCtors D
      let env ← env.addIndRecs D
      pure (env.addIndRules D)) = _
  simp only [addIndTypes, addIndCtors, addIndRecs, VInductDecl'.allConsts,
    addConstList_append]
  cases env.addConstList D.typeConsts <;> simp
  rename_i env₁; cases env₁.addConstList D.ctorConsts <;> simp
  rename_i env₂; cases env₂.addConstList D.recConsts <;> simp [Option.map]

theorem addInduct'_le (h : env.addInduct' D = some env') : env ≤ env' := by
  rw [addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  exact (addConstList_le h1).trans addIndRules_le

/-- `addInduct'` succeeds exactly when every name it would introduce is fresh and the
names are pairwise distinct. -/
theorem addInduct'_eq_some_iff :
    (∃ env', env.addInduct' D = some env') ↔
      (∀ n ∈ D.allNames, env.constants n = none) ∧ D.allNames.Nodup := by
  show _ ↔ (∀ n ∈ D.allConsts.map (·.1), env.constants n = none) ∧ (D.allConsts.map (·.1)).Nodup
  rw [← addConstList_eq_some_iff (cs := D.allConsts)]
  constructor
  · rintro ⟨env', h⟩
    rw [addInduct'_eq, Option.map_eq_some_iff] at h
    exact ⟨_, h.choose_spec.1⟩
  · rintro ⟨env₁, h⟩
    exact ⟨_, by rw [addInduct'_eq, h]; rfl⟩

theorem addInduct'_constants (h : env.addInduct' D = some env') :
    ∀ c ∈ D.allConsts, env'.constants c.1 = some c.2 := by
  rw [addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  intro c hc
  rw [addIndRules_constants]
  exact addConstList_constants h1 c hc

theorem addInduct'_defeqs (h : env.addInduct' D = some env') :
    ∀ df ∈ D.iotaRules, env'.defeqs df := by
  rw [addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, _, rfl⟩ := h
  exact addIndRules_defeqs

theorem addInduct'_constants_of_not_mem (h : env.addInduct' D = some env')
    (hn : n ∉ D.allNames) : env'.constants n = env.constants n := by
  rw [addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  rw [addIndRules_constants]
  exact addConstList_constants_of_not_mem h1 hn

/-- The block's type constants are present, with their stored types. -/
theorem addInduct'_types (h : env.addInduct' D = some env')
    (hT : T ∈ D.types) : env'.constants T.name = some ⟨D.uvars, T.type⟩ :=
  addInduct'_constants h _ <| by
    simp only [VInductDecl'.allConsts, List.mem_append]
    exact .inl (.inl (List.mem_map_of_mem hT))

/-- The block's constructors are present, at their derived types. -/
theorem addInduct'_ctors (h : env.addInduct' D = some env')
    (hC : (j, C) ∈ D.ctorsAll) : env'.constants C.name = some ⟨D.uvars, C.type D j⟩ :=
  addInduct'_constants h _ <| by
    simp only [VInductDecl'.allConsts, List.mem_append]
    exact .inl (.inr (List.mem_map_of_mem hC))

/-- The block's recursors are present, at `recType`. -/
theorem addInduct'_recs (h : env.addInduct' D = some env')
    (hT : (T, j) ∈ D.types.zipIdx) :
    env'.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ :=
  addInduct'_constants h _ <| by
    simp only [VInductDecl'.allConsts, List.mem_append]
    exact .inr (List.mem_map_of_mem hT)

end VEnv

/-! ## Telescope typing -/

namespace VEnv
variable {env : VEnv} {U : Nat}

/-- Introduce a whole declaration-order telescope of `∀`-binders. -/
theorem IsType.mkPi : ∀ {As : List VExpr} {Γ B},
    OnCtx (As.reverse ++ Γ) (env.IsType U) → env.IsType U (As.reverse ++ Γ) B →
    env.IsType U Γ (mkPi As B)
  | [], _, _, _, hB => hB
  | A :: As, Γ, B, hAs, hB => by
    rw [VExpr.tele_ctx_cons] at hAs hB
    exact IsType.forallE (OnCtx.head_of_append hAs) (IsType.mkPi hAs hB)

/-- Introduce a whole declaration-order telescope of `λ`-binders. -/
theorem HasType.mkLams : ∀ {As : List VExpr} {Γ b B},
    OnCtx (As.reverse ++ Γ) (env.IsType U) → env.HasType U (As.reverse ++ Γ) b B →
    env.HasType U Γ (mkLams As b) (mkPi As B)
  | [], _, _, _, _, hb => hb
  | A :: As, Γ, b, B, hAs, hb => by
    rw [VExpr.tele_ctx_cons] at hAs hb
    obtain ⟨_, hA⟩ := OnCtx.head_of_append hAs
    exact .lam hA (HasType.mkLams hAs hb)

variable (henv : Ordered env)
include henv

/-- **The workhorse.**  A function of type `mkPi As B`, weakened into the context of `As`
and applied to `As`' own variables, has type `B`.

This is the typing counterpart of `VExpr.instAll_liftN_bvars`. -/
theorem HasType.appBVars : ∀ {As : List VExpr} {Γ f B},
    OnCtx (As.reverse ++ Γ) (env.IsType U) → env.HasType U Γ f (mkPi As B) →
    env.HasType U (As.reverse ++ Γ) ((f.liftN As.length).mkApp (bvars 0 As.length)) B
  | [], _, f, B, _, hf => by simpa using hf
  | A :: As, Γ, f, B, hAs, hf => by
    rw [VExpr.tele_ctx_cons] at hAs ⊢
    obtain ⟨_, hA⟩ := OnCtx.head_of_append hAs
    -- one step: weaken `f` past `A` and apply it to `.bvar 0`
    have hf1 : env.HasType U (A :: Γ) (f.liftN 1) (.forallE (A.liftN 1) ((mkPi As B).liftN 1 1)) :=
      hf.weakN henv (.one (A := A))
    have hb : env.HasType U (A :: Γ) (.bvar 0) (A.liftN 1) := .bvar .zero
    have happ := hf1.app hb
    rw [VExpr.instN_bvar0] at happ
    have := HasType.appBVars (As := As) (Γ := A :: Γ) hAs happ
    rw [show ((VExpr.app (f.liftN 1) (.bvar 0)).liftN As.length).mkApp (bvars 0 As.length)
          = ((f.liftN (As.length + 1)).mkApp (bvars 0 (As.length + 1))) from by
        rw [VExpr.bvars_succ, VExpr.mkApp_cons]
        simp only [VExpr.liftN, liftVar, Nat.zero_add, Nat.add_zero,
          VExpr.liftN_liftN, Nat.add_comm 1 As.length, if_neg (Nat.lt_irrefl 0)]] at this
    simpa using this

end VEnv

/-! ## Well-formedness of the generated constants -/

variable {env env₁ : VEnv} {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {j : Nat}

/-- The stored type of an inductive type of the block is a well-formed constant. -/
theorem VIndType.WF.constant_wf (h : VIndType.WF env D T) :
    VConstant.WF env ⟨D.uvars, T.type⟩ := h.isType

/-- Stage 1: adding the block's type constants preserves `Ordered`. -/
theorem VInductDecl'.addIndTypes_ordered (henv : VEnv.Ordered env) (h : D.WF env)
    (he : env.addIndTypes D = some env₁) : VEnv.Ordered env₁ := by
  refine VEnv.addConstList_ordered henv (fun c hc => ?_) he
  simp only [VInductDecl'.typeConsts, List.mem_map] at hc
  obtain ⟨T, hT, rfl⟩ := hc
  exact (h.types T hT).constant_wf

/-- The context of a constructor's fields, transported from the block's parameter
telescope to the constructor's own (definitionally equal) copy of it. -/
theorem VIndCtor.WF.defeqCtx (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    ∀ {Δ : List VExpr}, OnCtx (Δ ++ D.params.reverse) (env₁.IsType D.uvars) →
      VEnv.IsDefEqCtx env₁ D.uvars [] (Δ ++ D.params.reverse) (Δ ++ C.params.reverse)
  | [], _ => h.params_eq.symm henv
  | _ :: _, hΔ => .succ (VIndCtor.WF.defeqCtx henv h hΔ.1) hΔ.2.choose_spec

/-! ## Saturated application

`HasArgs env U Γ As as` says that `as` instantiates the declaration-order telescope `As`:
each `aᵢ` is typed at `Aᵢ` with the earlier arguments already substituted.  This is the
hypothesis shape that makes `HasType.mkApp'` -- "apply a function of `mkPi` type to a whole
spine" -- statable, and `VExpr.instAll` (the β-normal form of a saturated `mkLams`) is
exactly the resulting type. -/

namespace VEnv

inductive HasArgs (env : VEnv) (U : Nat) (Γ : List VExpr) : List VExpr → List VExpr → Prop
  | nil : HasArgs env U Γ [] []
  | cons {A As a as} :
    env.HasType U Γ a A → HasArgs env U Γ (instTele a As) as →
    HasArgs env U Γ (A :: As) (a :: as)

theorem HasArgs.length_eq {env : VEnv} :
    ∀ {As as}, HasArgs env U Γ As as → As.length = as.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simpa using h.length_eq

/-- **Saturated application.**  Applying `f : mkPi As B` to a spine `as` instantiating `As`
gives `instAll B as`. -/
theorem HasType.mkApp' {env : VEnv} :
    ∀ {As as Γ f B}, env.HasArgs U Γ As as → env.HasType U Γ f (mkPi As B) →
      env.HasType U Γ (f.mkApp as) (instAll B as)
  | _, _, _, _, _, .nil, hf => hf
  | A :: As, a :: as, Γ, f, B, .cons ha has, hf => by
    have h1 := hf.app ha
    rw [VExpr.inst_mkPi_zero] at h1
    have hlen : as.length = As.length := has.length_eq.symm.trans VExpr.length_instTele
    rw [VExpr.mkApp_cons, VExpr.instAll_cons, Nat.zero_add, hlen]
    exact HasType.mkApp' has h1

end VEnv

/-! ## The constructor constants -/

variable {env₁ : VEnv} {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {j : Nat}

/-- The parameter context is well-formed, in the block's own copy of it. -/
theorem VIndCtor.WF.onCtxParams (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    OnCtx D.params.reverse (env₁.IsType D.uvars) := (h.params_eq.symm henv).isType

/-- Every prefix of the field telescope is a well-formed context over the block's
parameters. -/
theorem VIndCtor.WF.onCtxFields (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    ∀ i, OnCtx ((((C.fields.take i).map (·.type)).reverse) ++ D.params.reverse)
      (env₁.IsType D.uvars)
  | 0 => h.onCtxParams henv
  | i+1 => by
    rw [List.take_add_one, List.map_append, List.reverse_append, List.append_assoc]
    cases hF : C.fields[i]? with
    | none => simpa using h.onCtxFields henv i
    | some F =>
      refine ⟨h.onCtxFields henv i, F.lvl, ?_⟩
      simpa using (h.fields i F hF).hasType

theorem VIndCtor.WF.onCtxAllFields (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    OnCtx (((C.fields.map (·.type)).reverse) ++ D.params.reverse) (env₁.IsType D.uvars) := by
  simpa using h.onCtxFields henv C.fields.length

/-- **The constructor's stored type is well-formed.**  The content beyond `IsType.mkPi` is
the transport from the block's parameter telescope to the constructor's own copy of it
(F3): `VIndCtor.WF` states the fields and the result over `D.params`, while the stored type
binds `C.params`. -/
theorem VIndCtor.WF.isType (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    env₁.IsType D.uvars [] (C.type D j) := by
  have W := h.defeqCtx henv (Δ := (C.fields.map (·.type)).reverse) (h.onCtxAllFields henv)
  refine (VEnv.IsType.mkPi (As := C.params ++ C.fields.map (·.type)) ?_ ?_)
  · simpa using (W.symm henv).isType
  · simpa using VEnv.IsType.defeqDFC henv W ⟨_, h.result⟩

theorem VIndCtor.WF.constant_wf (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    VConstant.WF env₁ ⟨D.uvars, C.type D j⟩ := h.isType henv

/-! ### `ctorsAll` membership -/

theorem VInductDecl'.mem_ctorsAll (h : (j, C) ∈ D.ctorsAll) :
    ∃ T, D.types[j]? = some T ∧ C ∈ T.ctors := by
  simp only [VInductDecl'.ctorsAll, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨⟨T, j'⟩, hT, C', hC, rfl, rfl⟩ := h
  exact ⟨T, List.mk_mem_zipIdx_iff_getElem?.1 hT, hC⟩

/-- Stage 2: adding the block's constructors preserves `Ordered`. -/
theorem VInductDecl'.addIndCtors_ordered {env env₁ env₂ : VEnv} {D : VInductDecl'}
    (henv₁ : VEnv.Ordered env₁) (h : D.WF env) (he : env.addIndTypes D = some env₁)
    (he2 : env₁.addIndCtors D = some env₂) : VEnv.Ordered env₂ := by
  refine VEnv.addConstList_ordered henv₁ (fun c hc => ?_) he2
  simp only [VInductDecl'.ctorConsts, List.mem_map] at hc
  obtain ⟨⟨j, C⟩, hjC, rfl⟩ := hc
  obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hjC
  exact (h.ctors env₁ he j T hT C hC).constant_wf henv₁

/-! ## Level slack: `D.lvl` vs. the first type's result level

Design open question 7 asked whether `VLevel.LE` needs an `≈`-congruence in `VLevel.lean`.
It does not, on both counts below. -/

/-- `≤` on `VLevel` respects `≈` on both sides.  Nothing in `VLevel.lean` is needed beyond
`equiv_def`, so this can live downstream. -/
theorem VLevel.LE.congr {a a' b b' : VLevel} (h1 : a ≈ a') (h2 : b ≈ b') (h : a ≤ b) :
    a' ≤ b' := fun ls => by
  rw [← VLevel.equiv_def.1 h1 ls, ← VLevel.equiv_def.1 h2 ls]; exact h ls

/-- Consequently the field level condition transports along `≈` of the block's level: if
the spec's `D.lvl` and the kernel's `stats.resultLevel` differ, they differ only by `≈`,
and the condition is insensitive to that. -/
theorem VIndField.level_congr {l l' m : VLevel} (h : VLevel.imax m l ≤ l) (he : l ≈ l') :
    VLevel.imax m l' ≤ l' :=
  VLevel.LE.congr (VLevel.imax_congr (VLevel.equiv_def.2 fun _ => rfl) he) he h

/-! ## `IsDefEqType` -/

namespace VEnv
variable {env : VEnv}

theorem IsDefEqType.toU (h : env.IsDefEqType U Γ A B) : env.IsDefEqU U Γ A B :=
  let ⟨_, h⟩ := h; ⟨_, h⟩

theorem IsDefEqType.isType_l (h : env.IsDefEqType U Γ A B) : env.IsType U Γ A :=
  let ⟨_, h⟩ := h; ⟨_, h.hasType.1⟩

theorem IsDefEqType.isType_r (h : env.IsDefEqType U Γ A B) : env.IsType U Γ B :=
  let ⟨_, h⟩ := h; ⟨_, h.hasType.2⟩

theorem IsDefEqType.symm (h : env.IsDefEqType U Γ A B) : env.IsDefEqType U Γ B A :=
  let ⟨_, h⟩ := h; ⟨_, h.symm⟩

theorem IsDefEqType.instL (hls : ∀ l ∈ ls, l.WF U') (h : env.IsDefEqType U Γ A B) :
    env.IsDefEqType U' (Γ.map (VExpr.instL ls)) (A.instL ls) (B.instL ls) :=
  let ⟨_, h⟩ := h; ⟨_, h.instL hls⟩

theorem IsDefEqType.weak0 (henv : Ordered env) (h : env.IsDefEqType U [] A B) :
    env.IsDefEqType U Γ A B := let ⟨_, h⟩ := h; ⟨_, h.weak0 henv⟩

theorem IsDefEqType.mono (hle : env ≤ env') (h : env.IsDefEqType U Γ A B) :
    env'.IsDefEqType U Γ A B := let ⟨_, h⟩ := h; ⟨_, h.mono hle⟩

/-- Transport a typing judgment along a type-level definitional equality. -/
theorem IsDefEqType.defeq (h : env.IsDefEqType U Γ A B) (he : env.HasType U Γ e A) :
    env.HasType U Γ e B := let ⟨_, h⟩ := h; h.defeq he

end VEnv

/-! ## Entry points for the recursor case (D1)

These are exactly the two places where the level-instantiation lemma of item 1 does its
work: the block's type constants are declared at `D.uvars`, and the recursor is built at
`D.recUvars`. -/

variable {env : VEnv} {D : VInductDecl'} {T : VIndType}

/-- `atRec` of the canonical type of a block type, in the recursor's numbering. -/
theorem VIndType.WF.atRec_canon (h : VIndType.WF env D T) :
    env.IsDefEqType D.recUvars [] (D.atRec T.type) (D.atRec (T.canonType D)) := by
  have := h.canon.instL D.selfLvls_wf (ls := D.selfLvls)
  simpa [VInductDecl'.atRec] using this

/-- **D1, the constant half.**  `I_j.{selfLvls}` has the canonical pi-type at the
recursor's universe numbering.  This is where `IsDefEq.instL` is consumed: `WF.canon` is
stated at `D.uvars`, the recursor lives at `D.recUvars`. -/
theorem VIndType.WF.tyConst_hasType (henv : VEnv.Ordered env) (h : VIndType.WF env D T)
    (hc : env.constants T.name = some ⟨D.uvars, T.type⟩) {Γ : List VExpr} :
    env.HasType D.recUvars Γ (.const T.name D.selfLvls)
      (mkPi (D.atRecTele D.params ++ D.atRecTele T.indices)
        (.sort (D.lvl.inst D.selfLvls))) := by
  have h1 : env.HasType D.recUvars Γ (.const T.name D.selfLvls) (D.atRec T.type) :=
    VEnv.HasType.const hc D.selfLvls_wf (by simp)
  have h2 := (h.atRec_canon.weak0 henv).defeq h1
  rwa [VInductDecl'.atRec_canonType] at h2

/-- The block's parameter and index telescopes form a well-formed context at the
recursor's numbering. -/
theorem VIndType.WF.onCtxIndicesAtRec (h : VIndType.WF env D T) :
    OnCtx ((D.atRecTele T.indices).reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars) := by
  have := D.atRec_onCtx h.indices
  rwa [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse] at this

/-- The block's parameter telescope alone. -/
theorem VInductDecl'.WF.onCtxParamsAtRec (h : D.WF env) :
    OnCtx (D.atRecTele D.params).reverse (env.IsType D.recUvars) := by
  have := D.atRec_onCtx h.params
  rwa [VInductDecl'.atRecCtx, List.map_reverse] at this
