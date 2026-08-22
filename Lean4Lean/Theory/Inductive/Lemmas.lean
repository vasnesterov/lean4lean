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

/-!
## Two notes for anyone continuing this file

**1. Check `Theory/Inductive/Telescope.lean` before estimating.**  Twice in this
development a step was priced by its *shape* and turned out to be two applications of a
lemma that was already there with exactly the right side conditions.  `ih_telescope_eq`
was expected to need a closedness argument and collapses by `liftTele_liftTele`;
`indices_closed` was landed for it and then turned out not to be needed at all.  Grep the
telescope algebra first.

**2. Read the current `VEnv.Params` class, not `docs/design-inductive.md` §7.6.**  The
design describes four fields -- `pat_major_not_pi`, `pat_major_prop`, `pat_small`,
`pat_major_canonical` -- that **do not exist** in the class as it stands.  Their absence
retires M1, M2, M3, `VEnv.Sig`, and `IsDefEqU.const_forallE_inv`, i.e. both of the items the
design could see no route to.  What a `Params` instance needs from here is `addInduct_WF`,
which `addInduct'_ordered` (below) has reduced to D6 and E5.

**3. Plumbing habits that have each cost a round.**

* Prefer standalone `have`s with fully spelled-out statements over `conv_lhs => rw [...]`
  nested inside a `have := by`.  Where a rewrite needs an index lined up, take the length
  as an *equation* and `subst` it -- see `VExpr.map_instAll_bvars'`.
* Isolate arithmetic into named `omega` lemmas (`ih_param_offset`, `rec_tele_offset`,
  `rec_dom_offset`) so the assembly never reasons about offsets inline.
* Do not carry a redundant variable alongside the term it abbreviates.  Dropping `ni` in
  favour of `T.indices.length` in `motiveApp_hasType` removed a whole class of rewriting.
* `rw [VExpr.liftN]` unfolds only the outer constructor; use
  `simp only [VExpr.liftN, ...]` when a `liftN` is buried under one.
* `length_atRecTele` lives in `VInductDecl'`, not `VExpr`, and takes `D` explicitly.
-/

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

/-! ## B6: telescope weakening

Weakening a context by `n` binders at cut `k` weakens a declaration-order telescope over it
into `liftTele n · k`, and moves the cut past the telescope's own length. -/

/-- **B6.** -/
theorem Ctx.LiftN.tele : ∀ {As : List VExpr} {n k} {Γ Γ' : List VExpr},
    Ctx.LiftN n k Γ Γ' →
    Ctx.LiftN n (k + As.length) (As.reverse ++ Γ) ((liftTele n As k).reverse ++ Γ')
  | [], _, _, _, _, W => by simpa using W
  | A :: As, n, k, Γ, Γ', W => by
    rw [VExpr.tele_ctx_cons, VExpr.liftTele_cons, VExpr.tele_ctx_cons, List.length_cons,
      show k + (As.length + 1) = (k + 1) + As.length from by omega]
    exact Ctx.LiftN.tele (As := As) W.succ

namespace VEnv

/-- The `OnCtx` counterpart of B6: a well-formed telescope stays well-formed after the
context under it is weakened. -/
theorem OnCtx.weakTele {env : VEnv} {U n k} {Γ Γ' : List VExpr} (henv : Ordered env)
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U)) :
    ∀ {As : List VExpr}, OnCtx (As.reverse ++ Γ) (env.IsType U) →
      OnCtx ((liftTele n As k).reverse ++ Γ') (env.IsType U)
  | [], _ => by simpa using hΓ'
  | A :: As, hAs => by
    rw [VExpr.tele_ctx_cons] at hAs
    have hA : env.IsType U Γ A := OnCtx.head_of_append hAs
    rw [VExpr.liftTele_cons, VExpr.tele_ctx_cons]
    exact OnCtx.weakTele henv W.succ ⟨hΓ', hA.weakN henv W⟩ hAs

/-- **Two-block saturated application.**  Apply a *closed* `f : mkPi (As ++ Bs) R` to the
variables of `As` and of `Bs`, where `m` further binders were inserted between the two
blocks.  This is the shape every application in the recursor construction has: the
parameters sit at one offset and the indices/fields at another, with the motives and minors
in between. -/
theorem HasType.appBVars₂ {env : VEnv} {U m} {As Bs Γ₀ Γ₁ : List VExpr} {f R : VExpr}
    (henv : Ordered env) (hfc : VExpr.ClosedN f 0)
    (hf : env.HasType U Γ₀ f (mkPi (As ++ Bs) R))
    (hAs : OnCtx (As.reverse ++ Γ₀) (env.IsType U))
    (hBs : OnCtx (Bs.reverse ++ As.reverse ++ Γ₀) (env.IsType U))
    (W : Ctx.LiftN m 0 (As.reverse ++ Γ₀) Γ₁)
    (hΓ₁ : OnCtx Γ₁ (env.IsType U)) :
    env.HasType U ((liftTele m Bs).reverse ++ Γ₁)
      (f.mkApp (bvars (Bs.length + m) As.length ++ bvars 0 Bs.length))
      (R.liftN m Bs.length) := by
  -- step 1: apply to the `As` block
  rw [VExpr.mkPi_append] at hf
  have h1 := HasType.appBVars henv hAs hf
  rw [hfc.liftN_eq (Nat.zero_le _)] at h1
  -- step 2: weaken past the `m` inserted binders
  have h2 := h1.weakN henv W
  rw [VExpr.liftN_mkApp_bvars_lo (Nat.le_refl 0), hfc.liftN_eq (Nat.zero_le _),
    VExpr.liftN_mkPi, Nat.zero_add] at h2
  -- step 3: apply to the `Bs` block
  have hBs' : OnCtx ((liftTele m Bs).reverse ++ Γ₁) (env.IsType U) :=
    OnCtx.weakTele henv W hΓ₁ (by rw [← List.append_assoc]; exact hBs)
  have h3 := HasType.appBVars henv hBs' h2
  rw [VExpr.liftN_mkApp_bvars_lo (Nat.zero_le _), hfc.liftN_eq (Nat.zero_le _),
    ← VExpr.mkApp_append] at h3
  simpa using h3

end VEnv

/-! ## `HasArgs` for a `bvars` spine

The recursor's ι-rules and induction-hypothesis *values* apply a constant to a mixture of
variable blocks and genuine terms, so `appBVars₂` is not enough there and a real `HasArgs`
for a variable block is needed.  A telescope `As` sitting contiguously in the context, `k`
binders down, is instantiated by its own variables `bvars k |As|` -- against the telescope
re-indexed as `liftTele (k + |As|) As`, which is exactly what `Lookup` assigns. -/

namespace VExpr

/-- Instantiating a freshly-inserted variable one cut below where it was inserted. -/
theorem inst_bvar_liftN : ∀ (e : VExpr) (m j : Nat),
    (e.liftN (m+1) (j+1)).inst (.bvar m) j = e.liftN m j
  | .bvar i, m, j => by
    show instVar (liftVar (m+1) i (j+1)) (VExpr.bvar m) j = VExpr.bvar (liftVar m i j)
    rcases Nat.lt_or_ge i j with h | h
    · rw [liftVar_lt (show i < j+1 by omega), liftVar_lt h]
      simp only [instVar, if_pos h]
    · rcases Nat.eq_or_lt_of_le h with rfl | h
      · rw [liftVar_lt (Nat.lt_succ_self _), liftVar_le (Nat.le_refl _)]
        simp only [instVar, if_neg (Nat.lt_irrefl _)]
        show VExpr.liftN j (VExpr.bvar m) 0 = _
        rw [VExpr.liftN, liftVar_base']
      · rw [liftVar_le (show j+1 ≤ i by omega), liftVar_le (show j ≤ i by omega)]
        simp only [instVar, if_neg (show ¬ (m+1+i < j) by omega),
          if_neg (show ¬ (m+1+i = j) by omega)]
        congr 1; omega
  | .sort _, _, _ | .const .., _, _ => rfl
  | .app f a, m, j => by simp only [liftN, inst, inst_bvar_liftN]
  | .lam A b, m, j => by
    simp only [liftN, inst, inst_bvar_liftN A m j, inst_bvar_liftN b m (j+1)]
  | .forallE A b, m, j => by
    simp only [liftN, inst, inst_bvar_liftN A m j, inst_bvar_liftN b m (j+1)]

theorem instTele_bvar_liftTele : ∀ {As : List VExpr} {m j : Nat},
    instTele (.bvar m) (liftTele (m+1) As (j+1)) j = liftTele m As j
  | [], _, _ => rfl
  | A :: As, m, j => by
    rw [liftTele_cons, instTele_cons, inst_bvar_liftN, liftTele_cons,
      instTele_bvar_liftTele (As := As) (m := m) (j := j+1)]

end VExpr

theorem Lookup.append : ∀ (Ξ : List VExpr) {A Γ},
    Lookup (Ξ ++ A :: Γ) Ξ.length (A.liftN (Ξ.length + 1))
  | [], _, _ => .zero
  | B :: Ξ, A, Γ => by
    have := (Lookup.append Ξ (A := A) (Γ := Γ)).succ (A := B)
    rw [show (A.liftN (Ξ.length + 1)).lift = A.liftN (Ξ.length + 1 + 1) from
      VExpr.liftN_liftN ..] at this
    simpa using this

namespace VEnv

/-- **The variable spine of a telescope.**  If `As` sits in the context `k` binders down,
its own variables instantiate it. -/
theorem HasArgs.bvars {env : VEnv} {U : Nat} {Δ : List VExpr} :
    ∀ {As Γ₀ : List VExpr},
      env.HasArgs U (Δ ++ As.reverse ++ Γ₀) (liftTele (Δ.length + As.length) As)
        (bvars Δ.length As.length)
  | [], _ => by simpa using HasArgs.nil
  | A :: As, Γ₀ => by
    rw [List.append_assoc, VExpr.tele_ctx_cons, ← List.append_assoc, List.length_cons,
      show Δ.length + (As.length + 1) = (Δ.length + As.length) + 1 from by omega,
      VExpr.liftTele_cons, VExpr.bvars_succ]
    refine HasArgs.cons (.bvar ?_) ?_
    · simpa using Lookup.append (Ξ := Δ ++ As.reverse) (A := A) (Γ := Γ₀)
    · rw [VExpr.instTele_bvar_liftTele]
      exact HasArgs.bvars (Δ := Δ) (As := As) (Γ₀ := A :: Γ₀)

/-! ### Monotonicity of the well-formedness data -/

theorem HasArgs.mono {env env' : VEnv} (hle : env ≤ env') :
    ∀ {As as}, env.HasArgs U Γ As as → env'.HasArgs U Γ As as
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (h1.mono hle) (h2.mono hle)

theorem IsDefEqCtx.mono {env env' : VEnv} (hle : env ≤ env') :
    ∀ {Γ₀ Γ₁ Γ₂}, VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂ → VEnv.IsDefEqCtx env' U Γ₀ Γ₁ Γ₂
  | _, _, _, .zero => .zero
  | _, _, _, .succ h1 h2 => .succ (h1.mono hle) (h2.mono hle)

end VEnv

theorem VIndField.WF.mono {env env' : VEnv} {D : VInductDecl'} {Γ : List VExpr} {i F}
    (hle : env ≤ env') (h : VIndField.WF env D Γ i F) : VIndField.WF env' D Γ i F where
  hasType := h.hasType.mono hle
  level := h.level
  pos := by
    have hp := h.pos
    revert hp; cases F.recArg with
    | none => exact fun ⟨A, h1, h2⟩ => ⟨A, h1, h2.mono hle⟩
    | some r =>
      exact fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
        ⟨h1, h2, h3, h4, OnCtx.mono (fun hh => hh.mono hle) h5, h6.mono hle,
          fun T' hT' => (h7 T' hT').mono hle, h8.mono hle⟩

theorem VIndCtor.WF.mono {env env' : VEnv} {D : VInductDecl'} {j T C}
    (hle : env ≤ env') (h : VIndCtor.WF env D j T C) : VIndCtor.WF env' D j T C where
  params_len := h.params_len
  params_eq := h.params_eq.mono hle
  fields i F hF := (h.fields i F hF).mono hle
  args_len := h.args_len
  args_fresh := h.args_fresh
  args_ty := h.args_ty.mono hle
  result := h.result.mono hle

/-! ## The recursor's working environment -/

theorem VIndType.WF.mono {env env' : VEnv} {D : VInductDecl'} {T : VIndType}
    (hle : env ≤ env') (h : VIndType.WF env D T) : VIndType.WF env' D T where
  indices := OnCtx.mono (fun hh => hh.mono hle) h.indices
  isType := h.isType.mono hle
  canon := h.canon.mono hle

/-- The situation in which the recursor is built: an ordered environment containing the
block's type constants at their stored types, in which every type of the block is
well-formed.  `addIndTypes` followed by `addIndCtors` produces exactly this. -/
structure VInductDecl'.RecCtx (env : VEnv) (D : VInductDecl') : Prop where
  ordered : env.Ordered
  params : OnCtx D.params.reverse (env.IsType D.uvars)
  types : ∀ T ∈ D.types, VIndType.WF env D T
  consts : ∀ T ∈ D.types, env.constants T.name = some ⟨D.uvars, T.type⟩
  ctors : ∀ j (T : VIndType), D.types[j]? = some T →
    ∀ (C : VIndCtor), C ∈ T.ctors → VIndCtor.WF env D j T C
  ctorConsts : ∀ j (C : VIndCtor), (j, C) ∈ D.ctorsAll →
    env.constants C.name = some ⟨D.uvars, C.type D j⟩

/-- `RecCtx` from the declaration's well-formedness and any environment above the one the
block's types were added to. -/
theorem VInductDecl'.WF.recCtx {env env₁ env₂ env₃ : VEnv} {D : VInductDecl'}
    (h : D.WF env) (he : env.addIndTypes D = some env₁)
    (he₂ : env₁.addIndCtors D = some env₂) (hle : env₂ ≤ env₃)
    (henv₃ : env₃.Ordered) : D.RecCtx env₃ where
  ordered := henv₃
  params := OnCtx.mono (fun hh => hh.mono (le₁₃ he he₂ hle)) h.params
  types T hT := (h.types T hT).mono (le₁₃ he he₂ hle)
  consts T hT := (le₂₃ he₂ hle).constants <|
    VEnv.addConstList_constants he (T.name, ⟨D.uvars, T.type⟩) (List.mem_map_of_mem hT)
  ctors j T hT C hC := (h.ctors env₁ he j T hT C hC).mono (le₂₃ he₂ hle)
  ctorConsts j C hC := hle.constants <|
    VEnv.addConstList_constants he₂ (C.name, ⟨D.uvars, C.type D j⟩)
      (List.mem_map_of_mem hC)
where
  /-- `env ≤ env₃` -/
  le₁₃ {env env₁ env₂ env₃ : VEnv} {D : VInductDecl'}
      (he : env.addIndTypes D = some env₁) (he₂ : env₁.addIndCtors D = some env₂)
      (hle : env₂ ≤ env₃) : env ≤ env₃ :=
    (VEnv.addIndTypes_le he).trans ((VEnv.addIndCtors_le he₂).trans hle)
  /-- `env₁ ≤ env₃` -/
  le₂₃ {env₁ env₂ env₃ : VEnv} {D : VInductDecl'}
      (he₂ : env₁.addIndCtors D = some env₂) (hle : env₂ ≤ env₃) : env₁ ≤ env₃ :=
    (VEnv.addIndCtors_le he₂).trans hle

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

theorem elimLvl_wf : D.elimLvl.WF D.recUvars := by
  simp only [elimLvl, recUvars]
  by_cases h : D.isLE <;> simp [h, VLevel.WF]

theorem RecCtx.onCtxParams (hR : D.RecCtx env) :
    OnCtx (D.atRecTele D.params).reverse (env.IsType D.recUvars) := by
  have := D.atRec_onCtx hR.params
  rwa [VInductDecl'.atRecCtx, List.map_reverse] at this

theorem RecCtx.onCtxIndices (hR : D.RecCtx env) {T : VIndType} (hT : T ∈ D.types) :
    OnCtx ((D.atRecTele T.indices).reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars) := (hR.types T hT).onCtxIndicesAtRec

theorem getD_types (hT : D.types[t]? = some T) : D.types.getD t default = T := by
  rw [List.getD_eq_getElem?_getD, hT]; rfl

/-! ### D1: an inductive type of the block, saturated -/

/-- **D1.**  `I_t.{selfLvls}` applied to the parameters -- which sit `T.indices.length + m`
binders away -- and to its own index variables is a type, at the recursor's universe
numbering.  `m` is the number of binders (motives, minors) inserted between the parameter
block and the index block. -/
theorem tyApp'_hasType (hR : D.RecCtx env) {t : Nat} {T : VIndType}
    (hT : D.types[t]? = some T) {m : Nat} {Γ₁ : List VExpr}
    (W : Ctx.LiftN m 0 (D.atRecTele D.params).reverse Γ₁)
    (hΓ₁ : OnCtx Γ₁ (env.IsType D.recUvars)) :
    env.HasType D.recUvars ((liftTele m (D.atRecTele T.indices)).reverse ++ Γ₁)
      (D.tyApp' t (T.indices.length + m) (bvars 0 T.indices.length))
      (.sort (D.lvl.inst D.selfLvls)) := by
  have hmem : T ∈ D.types := List.mem_of_getElem? hT
  have hf := (hR.types T hmem).tyConst_hasType hR.ordered (hR.consts T hmem) (Γ := [])
  have h := VEnv.HasType.appBVars₂ (As := D.atRecTele D.params) (Bs := D.atRecTele T.indices)
    (Γ₀ := []) (m := m) hR.ordered (f := .const T.name D.selfLvls) trivial
    (by simpa using hf) (by simpa using hR.onCtxParams)
    (by simpa using hR.onCtxIndices hmem) (by simpa using W) hΓ₁
  simpa [VInductDecl'.tyApp', VInductDecl'.np, hT, VExpr.liftN] using h

/-! ### D3: the motives -/

/-- **D3.**  Motive `t` is a type in the context `params ++ motives<t`. -/
theorem motiveType_isType (hR : D.RecCtx env) {t : Nat} {T : VIndType}
    (hT : D.types[t]? = some T) {M : List VExpr} (hMlen : M.length = t)
    (hM : OnCtx (M ++ (D.atRecTele D.params).reverse) (env.IsType D.recUvars)) :
    env.IsType D.recUvars (M ++ (D.atRecTele D.params).reverse) (D.motiveType t) := by
  have hmem : T ∈ D.types := List.mem_of_getElem? hT
  have W : Ctx.LiftN t 0 (D.atRecTele D.params).reverse (M ++ (D.atRecTele D.params).reverse) :=
    .zero M hMlen
  have hI : OnCtx ((liftTele t (D.atRecTele T.indices)).reverse ++
      (M ++ (D.atRecTele D.params).reverse)) (env.IsType D.recUvars) :=
    VEnv.OnCtx.weakTele hR.ordered W hM (hR.onCtxIndices hmem)
  rw [VInductDecl'.motiveType, getD_types hT]
  exact VEnv.IsType.mkPi hI (VEnv.IsType.forallE ⟨_, tyApp'_hasType hR hT W hM⟩
    ⟨_, VEnv.HasType.sort (Γ := _) elimLvl_wf⟩)

/-- The motive telescope is a well-formed context over the parameters. -/
theorem onCtxMotivesTake (hR : D.RecCtx env) : ∀ t, t ≤ D.nm →
    OnCtx (((List.range t).map D.motiveType).reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars)
  | 0, _ => by simpa using hR.onCtxParams
  | t+1, ht => by
    obtain ⟨T, hT⟩ : ∃ T, D.types[t]? = some T :=
      ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht)⟩
    rw [List.range_succ, List.map_append, List.reverse_append, List.append_assoc]
    exact ⟨onCtxMotivesTake hR t (by omega),
      motiveType_isType hR hT (by simp) (onCtxMotivesTake hR t (by omega))⟩

theorem onCtxMotives (hR : D.RecCtx env) :
    OnCtx (D.motives.reverse ++ (D.atRecTele D.params).reverse) (env.IsType D.recUvars) :=
  onCtxMotivesTake hR D.nm (Nat.le_refl _)

end VInductDecl'


/-! ## Closedness of a well-formed telescope

D4 has to identify two re-indexings of the same index telescope, which is only possible
because the telescope's entries are closed at the parameter count. -/

theorem OnCtx.ctxClosed {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Γ}, OnCtx Γ (env.IsType U) → CtxClosed Γ
  | [], _ => trivial
  | _ :: _, ⟨h1, _, h2⟩ => ⟨h1.ctxClosed henv, h2.closedN henv (h1.ctxClosed henv)⟩

theorem VExpr.ClosedTele.of_onCtx {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {As Γ : List VExpr}, OnCtx (As.reverse ++ Γ) (env.IsType U) →
      VExpr.ClosedTele As Γ.length
  | [], _, _ => trivial
  | A :: As, Γ, h => by
    rw [VExpr.tele_ctx_cons] at h
    have hΓ : OnCtx (A :: Γ) (env.IsType U) := OnCtx.append_right h
    refine ⟨hΓ.2.choose_spec.closedN henv (hΓ.1.ctxClosed henv), ?_⟩
    simpa using VExpr.ClosedTele.of_onCtx (As := As) (Γ := A :: Γ) henv h

/-- The index telescope of a block type is closed at the parameter count. -/
theorem VIndType.WF.indices_closed {env : VEnv} {D : VInductDecl'} {T : VIndType}
    (henv : env.Ordered) (h : VIndType.WF env D T) :
    VExpr.ClosedTele T.indices D.np := by
  have := VExpr.ClosedTele.of_onCtx henv h.indices
  simpa using this

/-! ## Weakening a `HasArgs` -/

namespace VExpr

theorem liftTele_instTele : ∀ {As : List VExpr} {a n k j},
    liftTele n (instTele a As j) (k + j)
      = instTele (a.liftN n k) (liftTele n As (k + j + 1)) j
  | [], _, _, _, _ => rfl
  | A :: As, a, n, k, j => by
    rw [instTele_cons, liftTele_cons, liftTele_cons, instTele_cons, liftN_instN_hi]
    refine congrArg _ ?_
    rw [show k + j + 1 = k + (j + 1) from by omega,
      liftTele_instTele (As := As) (a := a) (n := n) (k := k) (j := j + 1),
      show k + (j + 1) + 1 = k + j + 1 + 1 from by omega]

end VExpr

namespace VEnv

theorem HasArgs.instL {env : VEnv} {U U' : Nat} {Γ : List VExpr} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {As as}, env.HasArgs U Γ As as →
      env.HasArgs U' (Γ.map (VExpr.instL ls)) (As.map (VExpr.instL ls))
        (as.map (VExpr.instL ls))
  | _, _, .nil => .nil
  | _, _, .cons ha h => by
    refine .cons (ha.instL hls) ?_
    have ih := HasArgs.instL hls h
    rwa [VExpr.instL_instTele] at ih

theorem HasArgs.weakN {env : VEnv} {U n k} {Γ Γ' : List VExpr} (henv : Ordered env)
    (W : Ctx.LiftN n k Γ Γ') :
    ∀ {As as}, env.HasArgs U Γ As as →
      env.HasArgs U Γ' (liftTele n As k) (as.map (·.liftN n k))
  | _, _, .nil => .nil
  | _, _, .cons ha h => by
    refine .cons (ha.weakN henv W) ?_
    have ih := HasArgs.weakN henv W h
    rwa [show k = k + 0 from rfl, VExpr.liftTele_instTele, Nat.add_zero] at ih

end VEnv

/-- **The offset the two routes into D4 must agree on.**

`args_ty` places the block's parameters at `nxi + i` in the recursive field's own
`ξ`-context; the two weakenings that carry it into minor `q`'s `s`-th induction hypothesis
add `off = nm + q` (between the fields and the parameters) and `d = nf - i + s` (below the
fields).  Independently, `ihTypes` reads motive `r.idx` at
`nxi + s + nf + q + (nm - 1 - r.idx)`, which puts the `nm` motives immediately below the
parameters -- i.e. the parameters at `nxi + s + nf + q + nm`.  The two agree, which is what
lets D4 identify the telescope `args_ty` supplies with the one the motive's type demands. -/
theorem VInductDecl'.ih_param_offset {nxi i s nf q nm : Nat} (h : i ≤ nf) :
    nxi + i + (nm + q) + (nf - i + s) = nxi + s + nf + q + nm := by omega

/-! ## The telescope identification D4 needs

Two routes reach the same telescope inside an induction hypothesis:

* `args_ty` supplies `liftTele (nxi+i) X` in the recursive field's own `ξ`-context, which
  the two weakenings turn into `liftTele d (liftTele off (liftTele (nxi+i) X) (nxi+i)) nxi`;
* the motive's type supplies `liftTele L (liftTele u X)`, where `L` is the lift `Lookup`
  assigns to motive `u`.

They agree, and -- pleasantly -- with no closedness hypothesis at all: each side collapses
by `liftTele_liftTele`, and `ih_param_offset` supplies the arithmetic. -/

theorem VExpr.liftTele_collapse₃ {X : List VExpr} {a off d nxi : Nat} (h : nxi ≤ a + off) :
    liftTele d (liftTele off (liftTele a X 0) a) nxi = liftTele (a + off + d) X 0 := by
  rw [liftTele_liftTele (Nat.zero_le _) (by omega),
    liftTele_liftTele (Nat.zero_le _) (by omega)]

theorem VExpr.liftTele_collapse₂ {X : List VExpr} {u L : Nat} :
    liftTele L (liftTele u X 0) 0 = liftTele (u + L) X 0 :=
  liftTele_liftTele (Nat.le_refl _) (by omega)

/-- **The telescope identification.**  `harith` is `ih_param_offset` plus
`u + (nm - 1 - u) + 1 = nm` (valid for `u < nm`). -/
theorem VInductDecl'.ih_telescope_eq {X : List VExpr} {a off d nxi u L : Nat}
    (h : nxi ≤ a + off) (harith : a + off + d = u + L) :
    liftTele d (liftTele off (liftTele a X 0) a) nxi = liftTele L (liftTele u X 0) 0 := by
  rw [VExpr.liftTele_collapse₃ h, VExpr.liftTele_collapse₂, harith]

/-! ## `instAll` on a `bvars` spine

Applying a function to a spine `bvars L np ++ bvars 0 ni` and then instantiating the `ni`
index arguments by genuine terms `π` leaves the parameter block shifted down by `ni` and
replaces the index block by `π` itself. -/

namespace VExpr

theorem instAll_bvar_ge : ∀ {as : List VExpr} {j k}, k + as.length ≤ j →
    instAll (.bvar j) as k = .bvar (j - as.length)
  | [], _, _, _ => by simp
  | a :: as, j, k, h => by
    simp only [List.length_cons] at h
    rw [instAll_cons,
      show (VExpr.bvar j).inst a (k + as.length) = .bvar (j - 1) from by
        simp only [inst, instVar, if_neg (show ¬ (j < k + as.length) by omega),
          if_neg (show ¬ (j = k + as.length) by omega)],
      instAll_bvar_ge (show k + as.length ≤ j - 1 by omega)]
    simp only [List.length_cons]
    congr 1
    omega

theorem map_instAll_bvars_ge {as : List VExpr} {lo n : Nat} (h : as.length ≤ lo) :
    (bvars lo n).map (instAll · as 0) = bvars (lo - as.length) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bvars_succ, List.map_cons, ih, bvars_succ,
      instAll_bvar_ge (show 0 + as.length ≤ lo + n by omega)]
    congr 2
    omega

/-- The identity spine, instantiated by `as`, returns `as`. -/
theorem map_instAll_bvars : ∀ (as : List VExpr),
    (bvars 0 as.length).map (instAll · as 0) = as
  | [] => rfl
  | a :: as => by
    have h1 : instAll (VExpr.bvar (0 + as.length)) (a :: as) 0 = a := by
      rw [instAll_cons,
        show (VExpr.bvar (0 + as.length)).inst a (0 + as.length) = a.liftN as.length 0 from by
          simp [inst, instVar],
        instAll_liftN]
    have h2 : (bvars 0 as.length).map (instAll · (a :: as) 0) = as := by
      have hc : (bvars 0 as.length).map (instAll · (a :: as) 0)
          = (bvars 0 as.length).map (instAll · as 0) := by
        refine List.map_congr_left fun e he => ?_
        obtain ⟨v, hv, rfl⟩ := mem_bvars.1 he
        rw [instAll_cons,
          show (VExpr.bvar (0 + v)).inst a (0 + as.length) = .bvar (0 + v) from by
            simp only [inst, instVar, Nat.zero_add, if_pos hv]]
      rw [hc, map_instAll_bvars]
    rw [List.length_cons, bvars_succ, List.map_cons, h1, h2]

end VExpr

/-! ## The `addInduct'` assembly

`addInduct'` is four stages; three of them are now discharged.  Stating the composition
with the remaining two as hypotheses fixes exactly what D6 and E5 must deliver, and lets
everything else be reviewed independently of them. -/

namespace VEnv

theorem addInduct'_stages {env env' : VEnv} {D : VInductDecl'}
    (h : env.addInduct' D = some env') :
    ∃ env₁ env₂ env₃, env.addIndTypes D = some env₁ ∧ env₁.addIndCtors D = some env₂ ∧
      env₂.addIndRecs D = some env₃ ∧ env' = env₃.addIndRules D := by
  rw [show env.addInduct' D
      = (env.addIndTypes D).bind (fun e₁ => (e₁.addIndCtors D).bind
          (fun e₂ => (e₂.addIndRecs D).bind (fun e₃ => some (e₃.addIndRules D)))) from rfl,
    Option.bind_eq_some_iff] at h
  obtain ⟨env₁, h1, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨env₂, h2, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨env₃, h3, h4⟩ := h
  exact ⟨env₁, env₂, env₃, h1, h2, h3, (Option.some_inj.1 h4).symm⟩

end VEnv

/-- **`addInduct'` preserves `Ordered`**, modulo the two obligations that remain.

* `hrec` is D6 (`recType_isType`): each recursor's type is a well-formed constant in the
  environment that already has the block's types and constructors.
* `hrules` is E5 (`iotaRule_WF`): each ι-rule is a well-formed `VDefEq` there.

Everything else -- the three `addConstList` stages, the type constants (`VIndType.WF`), the
constructor constants (`VIndCtor.WF.isType`, which carries the F3 parameter transport), and
the `addDefEq` fold -- is proved. -/
theorem VInductDecl'.addInduct'_ordered {env env' : VEnv} {D : VInductDecl'}
    (henv : env.Ordered) (h : D.WF env)
    (hrec : ∀ {env₁ env₂ : VEnv}, env.addIndTypes D = some env₁ →
      env₁.addIndCtors D = some env₂ → ∀ c ∈ D.recConsts, VConstant.WF env₂ c.2)
    (hrules : ∀ {env₃ : VEnv}, env ≤ env₃ → env₃.Ordered → ∀ df ∈ D.iotaRules, df.WF env₃)
    (he : env.addInduct' D = some env') : env'.Ordered := by
  obtain ⟨env₁, env₂, env₃, h1, h2, h3, rfl⟩ := VEnv.addInduct'_stages he
  have o1 := VInductDecl'.addIndTypes_ordered henv h h1
  have o2 := VInductDecl'.addIndCtors_ordered o1 h h1 h2
  have o3 := VEnv.addConstList_ordered o2 (hrec h1 h2) h3
  refine VEnv.addIndRules_ordered o3 (hrules ?_ o3)
  exact (VEnv.addIndTypes_le h1).trans ((VEnv.addIndCtors_le h2).trans (VEnv.addIndRecs_le h3))

/-! ## Arities of a constructor's stored type

These are what a `ParamsExtra.ctor_ty`-style obligation needs: the pi-arity of the stored
constructor type, and the head-arity of its result. -/

theorem VExpr.piArity_mkApp {f : VExpr} (h : f.piArity = 0) :
    ∀ {as}, (VExpr.mkApp f as).piArity = 0
  | [] => h
  | _ :: _ => VExpr.piArity_mkApp (f := .app _ _) rfl

/-- The result of a constructor is an application, never a `∀`. -/
@[simp] theorem VIndCtor.canonResult_piArity (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    (C.canonResult D j).piArity = 0 := VExpr.piArity_mkApp rfl

/-- **The constructor's arity.**  The stored type binds exactly the parameters and the
fields; nothing further, because the result is an application. -/
theorem VIndCtor.type_piArity (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    (C.type D j).piArity = C.params.length + C.fields.length := by
  rw [VIndCtor.type, VExpr.piArity_mkPi, VIndCtor.canonResult_piArity, Nat.add_zero,
    List.length_append, List.length_map]

/-- **The head-arity of the constructor's result.**  `I_j` is applied to the parameters and
to `C.args`; by `VIndCtor.WF.args_len` that count is `D.np + T.indices.length`, the same for
every constructor of `T` -- which is what makes a per-name head-arity well defined. -/
theorem VIndCtor.canonResult_appArity (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    (C.canonResult D j).appArity = D.np + C.args.length := by
  rw [VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.appArity_mkApp]
  simp [VExpr.appArity]

theorem VIndCtor.WF.canonResult_appArity {env : VEnv} {D : VInductDecl'} {j T C}
    (h : VIndCtor.WF env D j T C) :
    (C.canonResult D j).appArity = D.np + T.indices.length := by
  rw [VIndCtor.canonResult_appArity, h.args_len]

/-- `VIndCtor.WF.result`, transported to the constructor's **own** copy of the parameter
telescope -- which is the context `C.type D j` actually binds (F3).  `WF.result` is stated
over `D.params`; a consumer that reads the binder list off `ci.type` gets `C.params`, and
the two are only definitionally equal.  This is the transport that joins them. -/
theorem VIndCtor.WF.result' {env₁ : VEnv} {D : VInductDecl'} {j T C}
    (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    env₁.HasType D.uvars ((C.fields.map (·.type)).reverse ++ C.params.reverse)
      (C.canonResult D j) (.sort D.lvl) :=
  VEnv.HasType.defeqDFC henv (h.defeqCtx henv (h.onCtxAllFields henv)) h.result

/-! ## D6's body: the recursor's codomain

`motive_j` applied to the index variables and to the major premise.  Everything applied here
is a variable, so it goes through `HasArgs.bvars` + `mkApp'`.  Two offset identities make it
work, and they are isolated as `omega` lemmas below so the assembly never has to reason
about arithmetic inline. -/

/-- `HasArgs` transported from the block's universe numbering to the recursor's. -/
theorem VInductDecl'.atRec_hasArgs {env : VEnv} (D : VInductDecl') {Γ As as : List VExpr}
    (h : env.HasArgs D.uvars Γ As as) :
    env.HasArgs D.recUvars (D.atRecCtx Γ) (D.atRecTele As) (as.map D.atRec) :=
  h.instL D.selfLvls_wf

/-- Offset 3: the minor premise's telescope collapse.  `nf` is the field count, `nr` the
number of induction hypotheses, `off = nm + q`. -/
theorem VInductDecl'.minor_tele_offset {nm q nf nr t : Nat} (ht : t < nm) :
    nf + (nm + q) + nr = t + (nr + nf + q + (nm - 1 - t) + 1) := by omega

/-- Offset 4: the minor premise's domain match — the constructor application's type is
exactly what the motive demands after eating the index terms. -/
theorem VInductDecl'.minor_dom_offset {nm q nf nr t ni : Nat} (ht : t < nm) :
    (nr + nf + q + (nm - 1 - t)) + 1 + (ni + t) - ni = nr + nf + (nm + q) := by omega

/-- Offset 1: the telescope `HasArgs.bvars` supplies and the one the motive's type demands
collapse to the same lift. -/
theorem VInductDecl'.rec_tele_offset {nm nmin ni j : Nat} (hj : j < nm) :
    nm + nmin + (1 + ni) = j + (1 + ni + nmin + (nm - 1 - j) + 1) := by omega

/-- Offset 2: after the motive has eaten the index arguments, the parameter block lands
exactly on the major premise's own type. -/
theorem VInductDecl'.rec_dom_offset {nm nmin ni j : Nat} (hj : j < nm) :
    1 + ni + nmin + (nm - 1 - j) + 1 + j = 1 + ni + nmin + nm := by omega

/-- `map_instAll_bvars` with the length supplied as an equation, so callers never need a
`conv` to line the index up. -/
theorem VExpr.map_instAll_bvars' {as : List VExpr} {n : Nat} (h : as.length = n) :
    (bvars 0 n).map (VExpr.instAll · as 0) = as := by
  subst h; exact VExpr.map_instAll_bvars as

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- **The motive's index-telescope computation.**  Applying `motive_j`'s stored `I_j p ι`
to index arguments `ιs` shifts the parameter block down by `ni` and returns `ιs`.

`ιs` is arbitrary: D6 instantiates it at `bvars 1 ni` (the index *variables*), D5 at the
constructor's index *terms*. -/
theorem tyApp'_instAll {j ni K M : Nat} {ιs : List VExpr} (hlen : ιs.length = ni)
    (h : K + 1 + (ni + j) - ni = M) :
    VExpr.instAll ((D.tyApp' j (ni + j) (bvars 0 ni)).liftN (K + 1) ni) ιs 0
      = D.tyApp' j M ιs := by
  have hL : (D.tyApp' j (ni + j) (bvars 0 ni)).liftN (K + 1) ni
      = (VExpr.const (D.types.getD j default).name D.selfLvls).mkApp
          (bvars (K + 1 + (ni + j)) D.np ++ bvars 0 ni) := by
    rw [VInductDecl'.tyApp', VExpr.liftN_mkApp, List.map_append,
      VExpr.map_liftN_bvars_lo (Nat.le_add_right ni j),
      VExpr.map_liftN_bvars_hi (Nat.le_of_eq (Nat.zero_add ni))]
    rfl
  rw [hL, VInductDecl'.tyApp', VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append,
    VExpr.map_instAll_bvars_ge (by rw [hlen]; omega), hlen, h,
    VExpr.map_instAll_bvars' hlen]

/-- Applying `motive_j`'s stored `I_j p ι` to `bvars 1 ni` lands on the major premise's own
type: the D6 instance of `tyApp'_instAll`. -/
theorem tyApp'_instAll_bvars {j ni K : Nat} (h : K + 1 + j = 1 + ni + D.nmin + D.nm) :
    VExpr.instAll ((D.tyApp' j (ni + j) (bvars 0 ni)).liftN (K + 1) ni) (bvars 1 ni) 0
      = (D.tyApp' j (ni + D.nmin + D.nm) (bvars 0 ni)).liftN 1 0 := by
  have hR : (D.tyApp' j (ni + D.nmin + D.nm) (bvars 0 ni)).liftN 1 0
      = D.tyApp' j (1 + (ni + D.nmin + D.nm)) (bvars 1 ni) := by
    rw [VInductDecl'.tyApp', VInductDecl'.tyApp', VExpr.liftN_mkApp, List.map_append,
      VExpr.map_liftN_bvars_lo (Nat.zero_le _), VExpr.map_liftN_bvars_lo (Nat.zero_le _)]
    rfl
  rw [hR, tyApp'_instAll (D := D) (M := 1 + (ni + D.nmin + D.nm)) VExpr.length_bvars
    (by omega)]

/-- **The motive application, generically.**  Motive `t`, sitting at offset `K`, applied to
index arguments `ιs` and a major premise `z`.

Stated with `ιs` and `z` arbitrary because it is used twice: `recType`'s body applies the
motive to the index *variables* and the major *variable* (D6), while a minor premise applies
it to the constructor's index *terms* and to a constructor *application* (D5).  Only the two
hypotheses differ. -/
theorem motiveApp_hasType' {T : VIndType} {t K : Nat} {Γ ιs : List VExpr} {z : VExpr}
    (hT : D.types[t]? = some T)
    (hmot : Lookup Γ K ((D.motiveType t).liftN (K + 1)))
    (hidx : env.HasArgs D.recUvars Γ
      (liftTele (K + 1) (liftTele t (D.atRecTele T.indices) 0) 0) ιs)
    (hz : env.HasType D.recUvars Γ z
      (VExpr.instAll ((D.tyApp' t (T.indices.length + t)
        (bvars 0 T.indices.length)).liftN (K + 1) T.indices.length) ιs 0)) :
    env.HasType D.recUvars Γ ((VExpr.bvar K).mkApp (ιs ++ [z])) (.sort D.elimLvl) := by
  have hm0 : env.HasType D.recUvars Γ (.bvar K) ((D.motiveType t).liftN (K + 1)) := .bvar hmot
  have hlenX : (D.atRecTele T.indices).length = T.indices.length :=
    VInductDecl'.length_atRecTele D
  have hmot' : (D.motiveType t).liftN (K + 1)
      = mkPi (liftTele (K + 1) (liftTele t (D.atRecTele T.indices) 0) 0)
          ((VExpr.forallE (D.tyApp' t (T.indices.length + t) (bvars 0 T.indices.length))
              (.sort D.elimLvl)).liftN (K + 1) T.indices.length) := by
    simp only [VInductDecl'.motiveType, getD_types hT]
    rw [VExpr.liftN_mkPi, VExpr.length_liftTele, hlenX, Nat.zero_add]
  rw [hmot'] at hm0
  have happ := VEnv.HasType.mkApp' hidx hm0
  simp only [VExpr.liftN, VExpr.instAll_forallE, VExpr.instAll_sort] at happ
  rw [VExpr.mkApp_concat]
  exact happ.app hz

/-- **D6's body**, the variables-only instance of `motiveApp_hasType'`.  `hidx` is
discharged by `HasArgs.bvars` at the call site. -/
theorem motiveApp_hasType {T : VIndType} {j : Nat} {Γ : List VExpr}
    (hT : D.types[j]? = some T) (hj : j < D.nm)
    (hmot : Lookup Γ (1 + T.indices.length + D.nmin + (D.nm - 1 - j))
      ((D.motiveType j).liftN (1 + T.indices.length + D.nmin + (D.nm - 1 - j) + 1)))
    (hmaj : Lookup Γ 0 ((D.tyApp' j (T.indices.length + D.nmin + D.nm)
      (bvars 0 T.indices.length)).liftN 1))
    (hidx : env.HasArgs D.recUvars Γ
      (liftTele (1 + T.indices.length)
        (liftTele (D.nm + D.nmin) (D.atRecTele T.indices) 0) 0)
      (bvars 1 T.indices.length)) :
    env.HasType D.recUvars Γ
      ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
        (bvars 1 T.indices.length ++ [.bvar 0]))
      (.sort D.elimLvl) := by
  have hcol : liftTele (1 + T.indices.length)
        (liftTele (D.nm + D.nmin) (D.atRecTele T.indices) 0) 0
      = liftTele (1 + T.indices.length + D.nmin + (D.nm - 1 - j) + 1)
          (liftTele j (D.atRecTele T.indices) 0) 0 := by
    rw [VExpr.liftTele_collapse₂, VExpr.liftTele_collapse₂]
    exact congrArg (liftTele · _ _) (VInductDecl'.rec_tele_offset hj)
  rw [hcol] at hidx
  refine motiveApp_hasType' hT hmot hidx ?_
  rw [tyApp'_instAll_bvars (D := D) (j := j) (ni := T.indices.length)
    (K := 1 + T.indices.length + D.nmin + (D.nm - 1 - j)) (VInductDecl'.rec_dom_offset hj)]
  exact .bvar hmaj

/-- **D5's body**, the terms-and-application instance of `motiveApp_hasType'`.

`hidx` comes from `VIndCtor.WF.args_ty` after `atRec` and the two weakenings; `hz` from the
constructor constant applied to the parameters and fields.  Everything offset-related is in
`minor_dom_offset`. -/
theorem minorBody_hasType {T : VIndType} {C : VIndCtor} {t q nr : Nat} {Γ : List VExpr}
    (hT : D.types[t]? = some T) (ht : t < D.nm)
    (hlen : C.args.length = T.indices.length)
    (hmot : Lookup Γ (nr + C.fields.length + q + (D.nm - 1 - t))
      ((D.motiveType t).liftN (nr + C.fields.length + q + (D.nm - 1 - t) + 1)))
    (hidx : env.HasArgs D.recUvars Γ
      (liftTele (nr + C.fields.length + q + (D.nm - 1 - t) + 1)
        (liftTele t (D.atRecTele T.indices) 0) 0)
      (C.args.map fun a => VExpr.shift (D.nm + q) nr C.fields.length (D.atRec a)))
    (hz : env.HasType D.recUvars Γ
      (D.ctorApp' C (nr + C.fields.length + (D.nm + q)) (bvars nr C.fields.length))
      (D.tyApp' t (nr + C.fields.length + (D.nm + q))
        (C.args.map fun a => VExpr.shift (D.nm + q) nr C.fields.length (D.atRec a)))) :
    env.HasType D.recUvars Γ
      ((VExpr.bvar (nr + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) nr C.fields.length (D.atRec a))
          ++ [D.ctorApp' C (nr + C.fields.length + (D.nm + q)) (bvars nr C.fields.length)]))
      (.sort D.elimLvl) := by
  refine motiveApp_hasType' hT hmot hidx ?_
  rw [tyApp'_instAll (D := D) (M := nr + C.fields.length + (D.nm + q))
    (by rw [List.length_map, hlen]) (VInductDecl'.minor_dom_offset ht)]
  exact hz

end VInductDecl'
