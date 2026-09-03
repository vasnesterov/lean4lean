import Lean4Lean.Theory.Typing.ShapeIndepStep

/-!
# `ShapeIndepFresh`: `VEnv.FreshNames` is a theorem

`ShapeIndepStep.lean` carried freshness as a hypothesis, on the grounds that no "names added"
bound existed for `VDecl.WF`'s arms.  That was half right: `addInduct'` — the arm that looked
worst — already has one (`VEnv.addInduct'_constants_of_not_mem`, `Theory/Inductive/Lemmas.lean`),
and the other six arms are `addConst`, `addConsts`, `addQuot` and the identity.  So the bound is
available, and with it `ShapeIndep.lean`'s verdict loses its only side condition.

Two halves:

* **§1** `Name` is infinite — a depth measure, so no pigeonhole is needed.
* **§2** a `VEnv.WF` environment's constant table is bounded by a finite list of names, by
  induction on `VEnv.WF'` with one clause per `VDecl.WF` arm.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## §1 `Name` is infinite -/

/-- Number of components of a name.  **Not** `Verify/Inductive/NestedOccData.nameDepth`, which is
a different function of the same shape — the duplicate-name check caught the collision. -/
def nameParts : Name → Nat
  | .anonymous => 0
  | .str p _ => nameParts p + 1
  | .num p _ => nameParts p + 1

/-- A name of any prescribed depth. -/
def strName : Nat → Name
  | 0 => .anonymous
  | k+1 => .str (strName k) "x"

@[simp] theorem nameParts_strName : ∀ k, nameParts (strName k) = k
  | 0 => rfl
  | k+1 => by rw [strName, nameParts, nameParts_strName k]

/-- Every name in a list has depth at most the list's total depth. -/
theorem nameParts_le_total : ∀ {l : List Name} {n : Name}, n ∈ l →
    nameParts n ≤ l.foldr (fun a m => nameParts a + m) 0
  | _ :: _, _, .head _ => Nat.le_add_right ..
  | _ :: _, _, .tail _ h => Nat.le_trans (nameParts_le_total h) (Nat.le_add_left ..)

/-- **`Name` is infinite**: no finite list exhausts it. -/
theorem Name.exists_not_mem (l : List Name) : ∃ c : Name, c ∉ l := by
  refine ⟨strName (l.foldr (fun a m => nameParts a + m) 0 + 1), fun h => ?_⟩
  have := nameParts_le_total h
  rw [nameParts_strName] at this
  exact absurd this (Nat.not_succ_le_self _)

/-! ## §2 A well-formed environment's constant table is finite -/

namespace VEnv

/-- The constants of `env` are confined to a finite list of names. -/
def ConstantsBounded (env : VEnv) : Prop :=
  ∃ l : List Name, ∀ n : Name, n ∉ l → env.constants n = none

theorem ConstantsBounded.addConst {env env' : VEnv} {c : Name} {ci : VConstant}
    (h : env.addConst c ci = some env') (H : ConstantsBounded env) : ConstantsBounded env' :=
  let ⟨l, hl⟩ := H
  ⟨c :: l, fun n hn => by
    rw [VEnv.addConst_constants_eq h]
    show (if c = n then _ else _) = none
    rw [if_neg (show ¬ c = n from fun he => hn (by cases he; exact List.Mem.head _))]
    exact hl n fun hm => hn (List.Mem.tail _ hm)⟩

@[simp] theorem addDefEq_constants' (env : VEnv) (df : VDefEq) :
    (env.addDefEq df).constants = env.constants := rfl

theorem ConstantsBounded.addDefEq {env : VEnv} {df : VDefEq}
    (H : ConstantsBounded env) : ConstantsBounded (env.addDefEq df) := H

theorem ConstantsBounded.addDefEqs : ∀ {cis : List VDefVal} {env : VEnv},
    ConstantsBounded env → ConstantsBounded (env.addDefEqs cis)
  | [], _, H => H
  | ci :: cis, _, H =>
    ConstantsBounded.addDefEqs (cis := cis) (ConstantsBounded.addDefEq (df := ci.toDefEq) H)

theorem ConstantsBounded.addConsts : ∀ {cis : List VDefVal} {env env' : VEnv},
    env.addConsts cis = some env' → ConstantsBounded env → ConstantsBounded env'
  | [], _, _, h, H => by cases h; exact H
  | _ :: _, _, _, h, H => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact ConstantsBounded.addConsts h2 (H.addConst h1)

theorem ConstantsBounded.addQuot {env env' : VEnv} (h : env.addQuot = some env')
    (H : ConstantsBounded env) : ConstantsBounded env' := by
  simp [VEnv.addQuot, Option.bind_eq_some_iff] at h
  obtain ⟨_, h1, _, h2, _, h3, _, h4, rfl⟩ := h
  exact (((H.addConst h1).addConst h2).addConst h3).addConst h4 |>.addDefEq

theorem ConstantsBounded.addInduct' {env env' : VEnv} {D : VInductDecl'}
    (h : env.addInduct' D = some env') (H : ConstantsBounded env) : ConstantsBounded env' :=
  let ⟨l, hl⟩ := H
  ⟨D.allNames ++ l, fun n hn => by
    rw [VEnv.addInduct'_constants_of_not_mem h fun hm => hn (List.mem_append.2 (.inl hm))]
    exact hl n fun hm => hn (List.mem_append.2 (.inr hm))⟩

/-- **Every well-formed environment has finitely many constants.**  One clause per `VDecl.WF`
arm; the `induct` arm is `Theory/Inductive/Lemmas.addInduct'_constants_of_not_mem`. -/
theorem WF.constantsBounded {env : VEnv} : env.WF → ConstantsBounded env
  | ⟨ds, H⟩ => by
    induction H with
    | empty => exact ⟨[], fun _ _ => rfl⟩
    | decl h _ ih =>
      cases h with
      | «axiom» _ h2 => exact ih.addConst h2
      | «def» _ h2 => exact (ih.addConst h2).addDefEq
      | «opaque» _ h2 => exact ih.addConst h2
      | «example» _ => exact ih
      | unsafeDef _ h2 _ => exact (ConstantsBounded.addConsts h2 ih).addDefEqs
      | quot _ h2 => exact ih.addQuot h2
      | induct _ h2 => exact ih.addInduct' h2

/-- **`FreshNames` is a theorem.**  `ShapeIndep.lean`'s verdict therefore has no side condition. -/
theorem freshNames : FreshNames := fun env henv =>
  let ⟨l, hl⟩ := henv.constantsBounded
  let ⟨c, hc⟩ := Name.exists_not_mem l
  ⟨c, hl c hc⟩

end VEnv

section Audit
#print axioms Lean4Lean.Name.exists_not_mem
#print axioms Lean4Lean.VEnv.WF.constantsBounded
#print axioms Lean4Lean.VEnv.freshNames
end Audit

end Lean4Lean
