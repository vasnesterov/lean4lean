import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.InductiveLemmas

namespace Lean4Lean

theorem VEnv.addConsts_le {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' → env ≤ env'
  | [], h => by cases h; exact .rfl
  | _ :: _, h => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConst_le h1).trans (addConsts_le h2)

/-! ## Shared `defeqs`/`≤` plumbing for the environment-building operations

These four were duplicated verbatim in `Theory/Typing/DeltaUnique.lean` and in
`Verify/Environment/Lemmas.lean` / `Verify/TypeChecker/Reduce.lean`, which made the two
import cones impossible to combine (Lean rejects an import that re-declares a name).  They
live here — the lowest module both cones already import — and both sides use them from here.
All binders are implicit, matching the `Verify/` call style. -/

theorem VEnv.addConst_defeqs {env env' : VEnv} {n ci} (h : env.addConst n ci = some env') :
    env'.defeqs = env.defeqs := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

theorem VEnv.addConsts_defeqs : ∀ {cis : List VDefVal} {env env' : VEnv},
    env.addConsts cis = some env' → env'.defeqs = env.defeqs
  | [], _, _, h => by cases h; rfl
  | ci :: cis, env, env', h => by
    rw [VEnv.addConsts, List.foldlM_cons] at h
    cases hh : env.addConst ci.name ci.toVConstant with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e => rw [hh] at h; rw [VEnv.addConsts_defeqs h, VEnv.addConst_defeqs hh]

theorem VEnv.addConstList_defeqs : ∀ {cs : List (Name × VConstant)} {env env' : VEnv},
    env.addConstList cs = some env' → env'.defeqs = env.defeqs
  | [], _, _, h => by cases h; rfl
  | c :: cs, env, env', h => by
    rw [VEnv.addConstList, List.foldlM_cons] at h
    cases hh : env.addConst c.1 c.2 with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e => rw [hh] at h; rw [VEnv.addConstList_defeqs h, VEnv.addConst_defeqs hh]

theorem VEnv.addDefEqs_le : ∀ {cis : List VDefVal} {env : VEnv}, env ≤ env.addDefEqs cis
  | [], _ => VEnv.LE.rfl
  | ci :: cis, env => by
    show env ≤ VEnv.addDefEqs (env.addDefEq ci.toDefEq) cis
    exact VEnv.addDefEq_le.trans VEnv.addDefEqs_le

theorem VEnv.addDefEqs_defeqs : ∀ {cis : List VDefVal} {env : VEnv} {df},
    (env.addDefEqs cis).defeqs df → (∃ ci ∈ cis, df = ci.toDefEq) ∨ env.defeqs df
  | [], _, _, h => .inr h
  | ci :: cis, env, df, h => by
    rcases VEnv.addDefEqs_defeqs (cis := cis) (env := env.addDefEq ci.toDefEq) h with
      ⟨ci', hci', rfl⟩ | h
    · exact .inl ⟨ci', .tail _ hci', rfl⟩
    · rcases (h : df = ci.toDefEq ∨ env.defeqs df) with rfl | h
      · exact .inl ⟨ci, .head _, rfl⟩
      · exact .inr h

theorem VEnv.addConst_eq_none {env : VEnv} {name ci}
    (h : env.constants name = none) : ∃ env', env.addConst name ci = some env' := by
  unfold VEnv.addConst; rw [h]; exact ⟨_, rfl⟩

theorem VEnv.addConst_constants_eq {env env' : VEnv} {name ci}
    (h : env.addConst name ci = some env') :
    env'.constants = fun n => if name = n then some ci else env.constants n := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

/-- A block of constants can be added as long as each name is fresh and the block has no
duplicates; the latter is what `addMutual`'s `found` set checks. -/
theorem VEnv.exists_addConsts {env : VEnv} : ∀ {cis : List VDefVal},
    (∀ ci ∈ cis, env.constants ci.name = none) → (cis.map (·.name)).Nodup →
    ∃ env', env.addConsts cis = some env'
  | [], _, _ => ⟨_, rfl⟩
  | ci :: cis, hfresh, hnd => by
    obtain ⟨env₁, h₁⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) (hfresh _ (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨env₂, h₂⟩ := VEnv.exists_addConsts (env := env₁) (cis := cis) (fun c hc => ?_) hnd.2
    · exact ⟨env₂, by simp [VEnv.addConsts, h₁]; exact h₂⟩
    · rw [VEnv.addConst_constants_eq h₁]
      have : ci.name ≠ c.name := fun h => hnd.1 (List.mem_map.2 ⟨c, hc, h.symm⟩)
      simp [this, hfresh c (.tail _ hc)]

theorem VEnv.addConsts_congr {env : VEnv} : ∀ {cis cis' : List VDefVal},
    List.Forall₂ (fun a b => a.toVConstVal = b.toVConstVal) cis cis' →
    env.addConsts cis = env.addConsts cis'
  | [], [], _ => rfl
  | a :: _, b :: _, .cons h t => by
    have h1 : a.name = b.name := congrArg VConstVal.name h
    have h2 : a.toVConstant = b.toVConstant := congrArg VConstVal.toVConstant h
    show (env.addConst a.name a.toVConstant).bind _ = (env.addConst b.name b.toVConstant).bind _
    rw [h1, h2]
    cases env.addConst b.name b.toVConstant
    · rfl
    · exact VEnv.addConsts_congr t

theorem VEnv.addConsts_ordered {env env' : VEnv} : ∀ {cis}, Ordered env →
    (∀ ci ∈ cis, ci.toVConstant.WF env) → env.addConsts cis = some env' → Ordered env'
  | [], h, _, e => by cases e; exact h
  | _ :: _, h, hw, e => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    refine VEnv.addConsts_ordered (.const h (hw _ (.head _)) h1) (fun c hc => ?_) h2
    exact (hw c (.tail _ hc)).mono (VEnv.addConst_le h1)

theorem VEnv.addConsts_constants {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' →
    ∀ ci ∈ cis, env'.constants ci.name = some ci.toVConstant
  | [], _, _, hc => nomatch hc
  | _ :: _, e, c, hc => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    cases hc with
    | head => exact (VEnv.addConsts_le h2).constants (VEnv.addConst_self h1)
    | tail _ hc => exact VEnv.addConsts_constants h2 c hc

theorem VEnv.addDefEqs_ordered : ∀ {env : VEnv} {cis}, Ordered env →
    (∀ ci ∈ cis, env.constants ci.name = some ci.toVConstant) →
    (∀ ci ∈ cis, ci.WF env) → Ordered (env.addDefEqs cis)
  | _, [], h, _, _ => h
  | env, ci :: cis, h, hmem, hw => by
    have hci : ci.WF env := hw _ (.head _)
    have hord : Ordered (env.addDefEq ci.toDefEq) := by
      refine .defeq h ⟨?_, hci⟩
      simp [VDefVal.toDefEq]
      rw [← (hci.levelWF ⟨⟩).2.2.instL_id]
      exact .const (hmem _ (.head _)) VLevel.id_WF (by simp)
    show Ordered ((env.addDefEq ci.toDefEq).addDefEqs cis)
    refine VEnv.addDefEqs_ordered hord (fun c hc => ?_) (fun c hc => ?_)
    · exact (VEnv.addDefEq_le (df := ci.toDefEq)).constants (hmem c (.tail _ hc))
    · exact (hw c (.tail _ hc)).mono VEnv.addDefEq_le

theorem VEnv.WF.ordered : WF env → Ordered env
  | ⟨ds, H⟩ => by
    induction H with | empty => exact .empty | decl h _ ih
    cases h with
    | «axiom» h1 h2 => exact .const ih h1 h2
    | @«def» env env' ci h1 h2 =>
      refine .defeq (.const ih (h1.isType ih ⟨⟩) h2) ⟨?_, ?_⟩
      · simp [VDefVal.toDefEq]
        rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
        exact .const (addConst_self h2) VLevel.id_WF (by simp)
      · exact h1.mono (addConst_le h2)
    | unsafeDef h0 h1 h2 =>
      exact VEnv.addDefEqs_ordered (VEnv.addConsts_ordered ih h0 h1)
        (VEnv.addConsts_constants h1) h2
    | «opaque» h1 h2 => exact .const ih (h1.isType ih ⟨⟩) h2
    | «example» _ => exact ih
    | quot h1 h2 => exact addQuot_WF ih h1 h2
    | induct h1 h2 => exact addInduct_WF ih h1 h2

instance : CoeOut (VEnv.WF env) env.Ordered := ⟨(·.ordered)⟩
