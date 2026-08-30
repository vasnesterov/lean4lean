import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Theory.Inductive.StructureEta

/-!
# The `IsStructure` bridge, and what `AddInduct`'s strengthened shape predicates now supply

`docs/handoff-eta.md` §5 isolated the single step that blocks `tryEtaStructCore.WF`:

> supply `c.venv.IsStructure I D T C` from `c.env.isNonRecStructure I = true`.

## The finding this file used to record, and its repair

`AddInductStages` related the constant map to the abstract block through `AddIndConsts` at the
*bare* shape predicates `fun ci => ∃ v, ci = .inductInfo v` (and `.ctorInfo`, `.recInfo`) and
through `TrConstant`, which pins only the safety tag, the universe count and the type.
**Nothing there mentioned `InductiveVal.isRec`, `.ctors`, `.numIndices` or `.numParams`, nor
`ConstructorVal.numFields`, `.numParams` or `.induct`** — exactly the fields
`Environment.isNonRecStructure` and the two eta checks read.  `addInductStages_with` re-proved
the tree's own `AddInductStages` witness with that bookkeeping as a **free parameter**, and
`isNonRecStructure_not_determined` exhibited two runs of the same block, from the same map,
landing on the same `VEnv`, whose maps answered `isNonRecStructure` oppositely.

**That is repaired.**  `IndShape`/`CtorShape` and their stage wrappers `IndShapeOf`/
`CtorShapeOf` (`Verify/Environment/Basic.lean`) are now the shape predicates of
`AddInductStages` and of the nested-aware `AddInductStagesR`
(`Verify/Environment/InductR.lean`).  §2 below transports them, and §3 **re-runs both
demonstrations**:

* `addInductStages_pinned` — `addInductStages_with`'s three free parameters are down to one:
  `numIndices` and `ctors` are now *forced*, as an `↔`, not merely constrained;
* `isNonRecStructure_not_determined` — kept under its old name because
  `Verify/TypeChecker/IsDefEq.lean` cites it, but **restated**: what survives is `isRec` alone,
  and `isNonRecStructure_one_sided` shows that residue can only ever make the checker *refuse*
  eta, never accept it wrongly.

## What is still owed, and why it is not a shape-predicate problem

`VEnv.IsStructure` (`Theory/Inductive/Structure.lean`) demands `D.types = [T]`.  **No
strengthening of the shape predicates can supply that**, and the obstruction is not a gap in
the predicate but a fact about Lean: `Lean4Lean/Inductive/Add.lean` computes `isRec` *block
wide* (`indTypes.any fun indType => indType.ctors.any …`), so

```
mutual inductive A | mk : A
       inductive B | mk : B end
```

has `isRec = false`, `ctors = [A.mk]` and `numIndices = 0` on **both** members.
`isNonRecStructure A` answers `true`, and the block that declared `A` has two types.  Structure
eta on `A` is perfectly sound — nothing about eta needs the block to be a singleton — but
`IsStructure` as stated is not a true description of that situation.
`indShapeOf_not_singleton` (§4) machine-checks the shape-level half of this: the strengthened
predicate holds, `isNonRecStructure`'s three conditions hold, and `D.types` is not a singleton.

The recommended repair is on `IsStructure`'s side — `types : D.types = [T]` weakened to
`T ∈ D.types`, with `nm_eq`/`nmin_eq` going with it — and it is a redesign of
`Theory/Inductive/Structure.lean` and its two dependents, not of this file.  It is *stated*
here and not made.

`InductiveVal.all` is likewise **deliberately absent** from `IndShape`: `Add.lean` patches it
during nested restoration (`modify (·.add <| .inductInfo { ind with all := allIndNames })`), so
a clause `v.all = D.types.map (·.name)` would be an over-constraint refuting real nested blocks.

## Scope

`StructureBridge` is stated but **not proved**, and it is not proved *vacuously* either.  What
*is* proved is everything the strengthened predicates buy: §2's transport lemmas give every
field of `IsStructure` except `types` and `decl`, at a `T` the consumer names.  Nothing in this
file is a `sorry`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-! ## 1. `isNonRecStructure`, inverted -/

/-- What `Environment.isNonRecStructure I = true` actually says. -/
theorem isNonRecStructure_eq_true {env : Environment} {I : Name}
    (h : env.isNonRecStructure I = true) :
    ∃ (v : InductiveVal) (c : Name), env.find? I = some (.inductInfo v) ∧
      v.isRec = false ∧ v.ctors = [c] ∧ v.numIndices = 0 := by
  unfold Environment.isNonRecStructure at h
  split at h
  · rename_i v _ _ heq
    exact ⟨_, _, heq, rfl, rfl, rfl⟩
  · exact absurd h (by simp)

/-- …and the converse direction this file needs: a `true` verdict is impossible at a constant
the map records as recursive. -/
theorem isNonRecStructure_eq_false_of_isRec {env : Environment} {I : Name} {v : InductiveVal}
    (h : env.find? I = some (.inductInfo v)) (hr : v.isRec = true) :
    env.isNonRecStructure I = false := by
  unfold Environment.isNonRecStructure
  split
  · rename_i heq
    rw [h] at heq
    cases heq
    exact absurd hr (by simp)
  · rfl

/-! ## 2. Transport: from the strengthened shape predicates to `IsStructure`'s fields -/

/-- **The type side.**  `isNonRecStructure`'s three conditions, read across `IndShape` at a
member the consumer names.  Every field of `VEnv.IsStructure` except `types` and `decl` is
here: `name` is `hn`, `ctors` is the `T.ctors = [C]`, `noRec` is `C.recFields = []`; and
`T.indices = []` is the extra conjunct the eta rule needs on top of `IsStructure`. -/
theorem IndShapeOf.structure_fields {D : VInductDecl'} {rn : Name → Name} {T : VIndType}
    {v : InductiveVal} {c : Name}
    (h : IndShapeOf D rn (.inductInfo v)) (hT : T ∈ D.types) (hn : T.name = v.name)
    (hrec : v.isRec = false) (hidx : v.numIndices = 0) (hc : v.ctors = [c]) :
    v.numParams = D.np ∧ T.indices = [] ∧
      ∃ C, T.ctors = [C] ∧ rn C.name = c ∧ C.recFields = [] := by
  obtain ⟨v', hv, -, hnp, hni, hct, hir⟩ := h.at hT hn
  injection hv with hv
  subst hv
  refine ⟨hnp, List.eq_nil_of_length_eq_zero (by rw [← hni, hidx]), ?_⟩
  have hct' : (T.ctors.map fun C => rn C.name) = [c] := by rw [← hct, hc]
  cases hcs : T.ctors with
  | nil => rw [hcs] at hct'; simp at hct'
  | cons C Cs =>
    rw [hcs] at hct'
    simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at hct'
    obtain ⟨hrn, rfl⟩ := hct'
    exact ⟨C, rfl, hrn, hir hrec T hT C (by rw [hcs]; exact List.mem_cons_self)⟩

/-- **The constructor side.**  `CtorShape` at the constructor the consumer names. -/
theorem CtorShapeOf.ctor_fields {D : VInductDecl'} {rn : Name → Name} {tn : Nat → Name}
    {j : Nat} {C : VIndCtor} {w : ConstructorVal}
    (h : CtorShapeOf D rn tn (.ctorInfo w)) (hjC : (j, C) ∈ D.ctorsAll)
    (hn : w.name = rn C.name) :
    w.induct = tn j ∧ w.numParams = D.np ∧ w.numFields = C.fields.length := by
  obtain ⟨w', hv, -, hind, hnp, hnf⟩ := h.at hjC hn
  injection hv with hv
  subst hv
  exact ⟨hind, hnp, hnf⟩

/-- **The bridge's type half, at a whole `AddInductStages` step.**  A fresh name that the
block introduces and whose `InductiveVal` passes `isNonRecStructure`'s three tests names a
member of the abstract block with no indices, one constructor, and no recursive fields. -/
theorem AddInductStages.structure_fields {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {I : Name} {v : InductiveVal} {c : Name}
    (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF)
    (hfresh : m₁.find? I = none) (hfind : m₂.find? I = some (.inductInfo v))
    (hrec : v.isRec = false) (hidx : v.numIndices = 0) (hc : v.ctors = [c]) :
    ∃ T ∈ D.types, T.name = I ∧ v.numParams = D.np ∧ T.indices = [] ∧
      ∃ C, T.ctors = [C] ∧ C.name = c ∧ C.recFields = [] := by
  rcases H.find?_shape' hwf hfind with h | ⟨hS, hname, -⟩
  · rw [hfresh] at h; exact absurd h nofun
  rcases hS with hS | hS | ⟨w, hw⟩
  · obtain ⟨T, hT, hn, -⟩ := hS.exists
    obtain ⟨hnp, hidx', C, hcs, hrn, hrf⟩ := hS.structure_fields hT hn hrec hidx hc
    exact ⟨T, hT, hn.trans hname, hnp, hidx', C, hcs, hrn, hrf⟩
  · obtain ⟨w, hw⟩ := hS.ctorInfo; exact absurd hw nofun
  · exact absurd hw nofun

/-- **The bridge's constructor half, at a whole `AddInductStages` step.** -/
theorem AddInductStages.ctor_fields {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {D : VInductDecl'} {j : Nat} {C : VIndCtor} {w : ConstructorVal}
    (H : AddInductStages m₁ env₁ D m₂ env₂) (hwf : m₁.WF) (hjC : (j, C) ∈ D.ctorsAll)
    (hfresh : m₁.find? C.name = none) (hfind : m₂.find? C.name = some (.ctorInfo w)) :
    w.induct = (D.types.getD j default).name ∧ w.numParams = D.np ∧
      w.numFields = C.fields.length := by
  rcases H.find?_shape' hwf hfind with h | ⟨hS, hname, -⟩
  · rw [hfresh] at h; exact absurd h nofun
  rcases hS with hS | hS | ⟨r, hr⟩
  · obtain ⟨v, hv⟩ := hS.inductInfo; exact absurd hv nofun
  · exact hS.ctor_fields hjC hname
  · exact absurd hr nofun

/-! ## 3. The two demonstrations, re-run -/

/-- **The bridge**, exactly as `docs/handoff-eta.md` §5 names it: the kernel environment's
verdict that `I` is a non-recursive structure, transported to the abstract environment.

The extra conjuncts beyond `IsStructure` are the two the eta rule needs and `IsStructure`
does not carry: no indices (`isNonRecStructure` tests `numIndices = 0`) and a field count
agreeing with the `ConstructorVal` the checker reads its loop bound from.

Still a hypothesis; §2 supplies every conjunct except `IsStructure.types` and
`IsStructure.decl`, and the header records why `types` is not obtainable at all. -/
def StructureBridge (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv safety env venv →
  ∀ I : Name, env.isNonRecStructure I = true →
    ∃ D T C, venv.IsStructure I D T C ∧ T.indices = [] ∧
      ∀ ci : ConstructorVal, env.find? C.name = some (.ctorInfo ci) →
        ci.numFields = C.fields.length ∧ ci.numParams = D.np

namespace R10.Wit

/-- `R10.Wit.uInd` with the three fields `isNonRecStructure` reads left free.  Kept from the
refuted round so that `addInductStages_pinned` can quantify over them and say which are still
free: `numIndices` and `ctors` no longer are. -/
def uIndWith (numIndices : Nat) (ctors : List Name) (isRec : Bool) : InductiveVal where
  name := `R10.Wit.U; levelParams := []; type := .sort (.succ .zero)
  numParams := 0; numIndices := numIndices; all := [`R10.Wit.U]; ctors := ctors
  numNested := 0; isRec := isRec; isUnsafe := false; isReflexive := false

/-- `uInd` is the instance with the structure bookkeeping. -/
theorem uIndWith_eq : uIndWith 0 [`R10.Wit.U.unit] false = uInd := rfl

/-- The type-stage shape at `uIndWith 0 [U.unit] ir`, for **either** `ir`.  At `ir = true` the
`isRec` clause is vacuous; at `ir = false` it fires and is discharged by the block's one
constructor having no fields.  This is the *whole* residual freedom. -/
theorem indShapeOf_uIndWith (ir : Bool) :
    IndShapeOf decl id (.inductInfo (uIndWith 0 [`R10.Wit.U.unit] ir)) := by
  refine ⟨_, rfl, ⟨_, List.mem_singleton_self _, rfl⟩, fun T hT hn => ?_⟩
  simp only [decl, List.mem_singleton] at hT
  subst hT
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, fun _ T hT C hC => ?_⟩
  simp only [decl, List.mem_singleton] at hT
  subst hT
  simp only [List.mem_singleton] at hC
  subst hC
  simp [VIndCtor.recFields]

/-- **`AddInductStages` at `decl`, with `isRec` — and only `isRec` — a free parameter.**

This is `addInductStages_wit`'s proof with `uInd` replaced by `uIndWith 0 [U.unit] ir`.  Under
the *old* shape predicates the same proof went through with `numIndices` and `ctors` free as
well; `addInductStages_pinned` below shows that is no longer possible. -/
theorem addInductStages_isRec_free {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none)
    (ir : Bool) :
    ∃ m' env', AddInductStages m VEnv.empty decl m' env' ∧
      m'.find? `R10.Wit.U = some (.inductInfo (uIndWith 0 [`R10.Wit.U.unit] ir)) ∧
      VEnv.empty.addInduct' decl = some env' := by
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := VEnv.empty) (name := `R10.Wit.U)
    (ci := ⟨0, .sort (.succ .zero)⟩) rfl
  have c1 := VEnv.addConst_constants_eq he1
  have hU1 : e1.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩ := by rw [c1]; simp
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := `R10.Wit.U.unit)
    (ci := ⟨0, .const `R10.Wit.U []⟩) (by rw [c1]; simp [VEnv.empty])
  have c2 := VEnv.addConst_constants_eq he2
  have hU2 : e2.constants `R10.Wit.U = some ⟨0, .sort (.succ .zero)⟩ := by
    rw [c2]; simp [hU1]
  have hu2 : e2.constants `R10.Wit.U.unit = some ⟨0, .const `R10.Wit.U []⟩ := by rw [c2]; simp
  obtain ⟨e3, he3⟩ := VEnv.addConst_eq_none (env := e2) (name := `R10.Wit.U.rec)
    (ci := ⟨0, decl.recType 0⟩) (by rw [c2, c1]; simp [VEnv.empty])
  have w1 := hwf.insert `R10.Wit.U (.inductInfo (uIndWith 0 [`R10.Wit.U.unit] ir)) (hfr _)
  have f2 : (m.insert `R10.Wit.U
      (.inductInfo (uIndWith 0 [`R10.Wit.U.unit] ir))).find? `R10.Wit.U.unit = none := by
    rw [hwf.find?_insert]; simp [hfr]
  have w2 := w1.insert `R10.Wit.U.unit (.ctorInfo uCtor) f2
  have s1 : AddIndConsts (IndShapeOf decl id) decl.typeConsts
      m VEnv.empty (m.insert `R10.Wit.U (.inductInfo (uIndWith 0 [`R10.Wit.U.unit] ir))) e1 :=
    .cons (ci := .inductInfo (uIndWith 0 [`R10.Wit.U.unit] ir)) rfl (indShapeOf_uIndWith ir)
      ⟨DefinitionSafety.le_safe, rfl, .sort rfl⟩ (hfr _) he1 .nil
  have s2 : AddIndConsts (CtorShapeOf decl id fun j => (decl.types.getD j default).name)
      decl.ctorConsts
      (m.insert `R10.Wit.U (.inductInfo (uIndWith 0 [`R10.Wit.U.unit] ir))) e1
      ((m.insert `R10.Wit.U (.inductInfo (uIndWith 0 [`R10.Wit.U.unit] ir))).insert
        `R10.Wit.U.unit (.ctorInfo uCtor)) e2 :=
    .cons (ci := .ctorInfo uCtor) rfl ctorShapeOf_uCtor
      ⟨by decide, rfl, .const hU1 rfl rfl⟩ f2 he2 .nil
  have s3 : AddIndConsts (fun ci => ∃ v, ci = .recInfo v) decl.recConsts
      ((m.insert `R10.Wit.U (.inductInfo (uIndWith 0 [`R10.Wit.U.unit] ir))).insert
        `R10.Wit.U.unit (.ctorInfo uCtor)) e2
      (((m.insert `R10.Wit.U (.inductInfo (uIndWith 0 [`R10.Wit.U.unit] ir))).insert
        `R10.Wit.U.unit (.ctorInfo uCtor)).insert `R10.Wit.U.rec (.recInfo uRec)) e3 :=
    .cons (ci := .recInfo uRec) rfl ⟨_, rfl⟩ ⟨by decide, rfl, tr_recType hU2 hu2⟩
      (by rw [w1.find?_insert, hwf.find?_insert]; simp [hfr, Lean.mkRecName]) he3 .nil
  have H : AddInductStages m VEnv.empty decl _ (e3.addIndRules decl) :=
    ⟨_, _, _, _, e3, s1, s2, s3, rfl⟩
  refine ⟨_, _, H, ?_, H.to_addInduct⟩
  rw [w2.find?_insert, w1.find?_insert]; simp [hwf.find?_insert]

/-- **Demonstration 1, re-run: the bookkeeping is no longer free.**

An `↔`, so it is a *pinning* and not merely a constraint: `AddInductStages` at `decl` can put
`uIndWith ni cs ir` in the map for **exactly** `ni = 0` and `cs = [U.unit]`, whatever `ir`.
Under the old shape predicates the left-hand side held for every `ni`, `cs`, `ir`. -/
theorem addInductStages_pinned {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none)
    (ni : Nat) (cs : List Name) (ir : Bool) :
    (∃ m' env', AddInductStages m VEnv.empty decl m' env' ∧
        m'.find? `R10.Wit.U = some (.inductInfo (uIndWith ni cs ir))) ↔
      (ni = 0 ∧ cs = [`R10.Wit.U.unit]) := by
  constructor
  · rintro ⟨m', env', H, hfind⟩
    rcases H.find?_shape' hwf hfind with h | ⟨hS, -, -⟩
    · rw [hfr] at h; exact absurd h nofun
    rcases hS with hS | hS | ⟨r, hr⟩
    · obtain ⟨v', hv, -, hall⟩ := hS
      injection hv with hv
      subst hv
      obtain ⟨v'', hv2, -, -, hni, hct, -⟩ := hall _ (List.mem_singleton_self _) rfl
      injection hv2 with hv2
      subst hv2
      exact ⟨hni, hct⟩
    · obtain ⟨w, hw⟩ := hS.ctorInfo; exact absurd hw nofun
    · exact absurd hr nofun
  · rintro ⟨rfl, rfl⟩
    obtain ⟨m', env', H, hfind, -⟩ := addInductStages_isRec_free hwf hfr ir
    exact ⟨m', env', H, hfind⟩

/-- **Demonstration 2, re-run — under its old name, because
`Verify/TypeChecker/IsDefEq.lean` cites it, and with its old claim retracted.**

What the refuted round proved: two runs of the same block, from the same map, landing on the
*same* `VEnv`, whose type constants differed in **every** field `isNonRecStructure` inspects.
What is true now: they differ in `isRec` and **agree on `numIndices` and `ctors`**, which is
recorded here as an equation between the two `InductiveVal`s' bookkeeping rather than as a
difference.  The surviving `isRec` freedom is disposed of by `isNonRecStructure_one_sided`. -/
theorem isNonRecStructure_not_determined {m : ConstMap} (hwf : m.WF)
    (hfr : ∀ n, m.find? n = none) :
    ∃ m₁ m₂ env' v₁ v₂,
      AddInductStages m VEnv.empty decl m₁ env' ∧
      AddInductStages m VEnv.empty decl m₂ env' ∧
      m₁.find? `R10.Wit.U = some (.inductInfo v₁) ∧
      m₂.find? `R10.Wit.U = some (.inductInfo v₂) ∧
      v₁.isRec = false ∧ v₂.isRec = true ∧
      -- …and this is what the strengthening added: the rest of the bookkeeping agrees.
      v₁.numIndices = v₂.numIndices ∧ v₁.ctors = v₂.ctors ∧ v₁.numParams = v₂.numParams := by
  obtain ⟨m₁, env₁, H₁, hf₁, ha₁⟩ := addInductStages_isRec_free hwf hfr false
  obtain ⟨m₂, env₂, H₂, hf₂, ha₂⟩ := addInductStages_isRec_free hwf hfr true
  cases ha₁.symm.trans ha₂
  exact ⟨m₁, m₂, env₁, _, _, H₁, H₂, hf₁, hf₂, rfl, rfl, rfl, rfl, rfl⟩

/-- **The residue is one-sided.**  Any two runs of `decl` agree on the two fields that
`isNonRecStructure`'s `true` verdict actually transports, and the third — `isRec` — can only
turn a `true` verdict into `false`.  So the surviving freedom makes the checker *refuse* eta;
it can never make it accept eta at a type the abstract environment does not support. -/
theorem isNonRecStructure_one_sided {m m₁ m₂ : ConstMap} {env₁ env₂ : VEnv}
    {v₁ v₂ : InductiveVal} (hwf : m.WF) (hfr : ∀ n, m.find? n = none)
    (H₁ : AddInductStages m VEnv.empty decl m₁ env₁)
    (H₂ : AddInductStages m VEnv.empty decl m₂ env₂)
    (hf₁ : m₁.find? `R10.Wit.U = some (.inductInfo v₁))
    (hf₂ : m₂.find? `R10.Wit.U = some (.inductInfo v₂)) :
    (v₁.numIndices = v₂.numIndices ∧ v₁.ctors = v₂.ctors ∧ v₁.numParams = v₂.numParams) ∧
    ∀ (env : Environment), env.find? `R10.Wit.U = some (.inductInfo v₁) →
      v₁.isRec ≠ v₂.isRec → v₁.isRec = true → env.isNonRecStructure `R10.Wit.U = false := by
  have key : ∀ {m' : ConstMap} {e : VEnv} {v : InductiveVal},
      AddInductStages m VEnv.empty decl m' e →
      m'.find? `R10.Wit.U = some (.inductInfo v) →
      v.numIndices = 0 ∧ v.ctors = [`R10.Wit.U.unit] ∧ v.numParams = 0 := by
    intro m' e v H hfind
    rcases H.find?_shape' hwf hfind with h | ⟨hS, hname, -⟩
    · rw [hfr] at h; exact absurd h nofun
    rcases hS with hS | hS | ⟨r, hr⟩
    · obtain ⟨v', hv, -, hall⟩ := hS
      injection hv with hv
      subst hv
      obtain ⟨v'', hv2, -, hnp, hni, hct, -⟩ :=
        hall _ (List.mem_singleton_self _) hname.symm
      injection hv2 with hv2
      subst hv2
      exact ⟨hni, hct, hnp⟩
    · obtain ⟨w, hw⟩ := hS.ctorInfo; exact absurd hw nofun
    · exact absurd hr nofun
  obtain ⟨a₁, b₁, c₁⟩ := key H₁ hf₁
  obtain ⟨a₂, b₂, c₂⟩ := key H₂ hf₂
  exact ⟨⟨a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm⟩,
    fun env h _ hr => isNonRecStructure_eq_false_of_isRec h hr⟩

/-! ### Negative controls

The point of an `↔` is that its right-hand side *fails* somewhere.  These are the three runs
the refuted round could produce and this one cannot. -/

/-- A wrong `numIndices` is refuted. -/
theorem addInductStages_refutes_numIndices {m : ConstMap} (hwf : m.WF)
    (hfr : ∀ n, m.find? n = none) (ir : Bool) :
    ¬ ∃ m' env', AddInductStages m VEnv.empty decl m' env' ∧
      m'.find? `R10.Wit.U = some (.inductInfo (uIndWith 1 [`R10.Wit.U.unit] ir)) := by
  rw [addInductStages_pinned hwf hfr]
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-- A wrong constructor list is refuted — including the "under-reports its constructors"
shape that `Theory/Inductive/Companion.lean`'s `fooComp_inconsistent` warns about, here on the
*map* side rather than the abstract one. -/
theorem addInductStages_refutes_ctors {m : ConstMap} (hwf : m.WF)
    (hfr : ∀ n, m.find? n = none) (ir : Bool) :
    ¬ ∃ m' env', AddInductStages m VEnv.empty decl m' env' ∧
      m'.find? `R10.Wit.U = some (.inductInfo (uIndWith 0 [] ir)) := by
  rw [addInductStages_pinned hwf hfr]
  rintro ⟨-, h⟩
  exact absurd h (by decide)

/-- `R10.Wit.uCtor` with a lying field count. -/
def uCtorWith (numFields : Nat) : ConstructorVal where
  name := `R10.Wit.U.unit; levelParams := []; type := .const `R10.Wit.U []
  induct := `R10.Wit.U; cidx := 0; numParams := 0; numFields := numFields; isUnsafe := false

/-- A wrong `numFields` is refuted: this is the `CtorShape` half of the strengthening biting.
`numFields` is the loop bound `tryEtaStructCore` reads, so this is the clause structure eta
depends on most directly. -/
theorem addInductStages_refutes_numFields {m : ConstMap} (hwf : m.WF)
    (hfr : ∀ n, m.find? n = none) :
    ¬ ∃ m' env', AddInductStages m VEnv.empty decl m' env' ∧
      m'.find? `R10.Wit.U.unit = some (.ctorInfo (uCtorWith 1)) := by
  rintro ⟨m', env', H, hfind⟩
  have hjC : (0, ({ name := `R10.Wit.U.unit, params := [], fields := [], args := [] } :
      VIndCtor)) ∈ decl.ctorsAll := List.mem_singleton_self _
  obtain ⟨-, -, hnf⟩ := H.ctor_fields hwf hjC (hfr _) hfind
  exact absurd hnf (by decide)

/-- **The bridge's fields, at the witness.**  Not vacuous, and not a restatement of the
hypothesis: the abstract facts come out of `AddInductStages`, and they are the three
`IsStructure` fields other than `types` plus the eta rule's `indices = []`. -/
theorem structure_fields_wit {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env', AddInductStages m VEnv.empty decl m' env' ∧
      ∃ T ∈ decl.types, T.name = `R10.Wit.U ∧ T.indices = [] ∧
        ∃ C, T.ctors = [C] ∧ C.name = `R10.Wit.U.unit ∧ C.recFields = [] := by
  obtain ⟨m', env', H, hfind, -⟩ := addInductStages_isRec_free hwf hfr false
  obtain ⟨T, hT, hn, -, hidx, C, hcs, hcn, hrf⟩ :=
    H.structure_fields hwf (hfr _) hfind rfl rfl rfl
  exact ⟨m', env', H, T, hT, hn, hidx, C, hcs, hcn, hrf⟩

end R10.Wit

/-! ## 4. What the strengthening still cannot give: `IsStructure.types` -/

namespace MutNonRec

mutual
/-- Half of a mutual block that is not recursive at all.  Declared for real so that the claim
about `isRec` is checked against Lean's own elaborator rather than read off `Add.lean`. -/
inductive A where | mk : A
/-- The other half. -/
inductive B where | mk : B
end

/-! **[EV] The situation `IsStructure` cannot describe, at a real declaration.**  `A` is a
member of a two-type block; it is non-recursive, has one constructor and no indices; so
`isNonRecStructure` answers `true` on it while its block has two types.  The `#eval` below fails
the build if any of that stops holding. -/

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let some (.inductInfo v) := env.find? ``A | throwError "MutNonRec.A is not an inductive"
  unless v.isRec = false do throwError "MutNonRec.A.isRec is no longer false"
  unless v.numIndices = 0 do throwError "MutNonRec.A.numIndices is no longer 0"
  unless v.ctors = [``A.mk] do throwError "MutNonRec.A.ctors moved"
  unless v.all = [``A, ``B] do throwError "MutNonRec.A.all moved"
  unless Lean.isNonRecStructure env ``A do
    throwError "isNonRecStructure no longer accepts a member of a mutual non-recursive block"

/-- The abstract form of that block: two members, neither recursive, one nullary constructor
each.  Only the shape data matters here; no `WF` claim is made and none is needed, because the
point is about the *shape predicate*. -/
def decl2 : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := false
  types :=
    [{ name := `MutNonRec.A, type := .sort (.succ .zero), indices := [],
       ctors := [{ name := `MutNonRec.A.mk, params := [], fields := [], args := [] }] },
     { name := `MutNonRec.B, type := .sort (.succ .zero), indices := [],
       ctors := [{ name := `MutNonRec.B.mk, params := [], fields := [], args := [] }] }]

def aInd : InductiveVal where
  name := `MutNonRec.A; levelParams := []; type := .sort (.succ .zero)
  numParams := 0; numIndices := 0; all := [`MutNonRec.A, `MutNonRec.B]
  ctors := [`MutNonRec.A.mk]
  numNested := 0; isRec := false; isUnsafe := false; isReflexive := false

/-- **`IsStructure.types` is not obtainable from the shape predicates, however strengthened.**

`IndShapeOf` holds — every clause, including the block-wide `isRec` one — and `aInd` passes all
three of `isNonRecStructure`'s tests, yet the block has two types.  This is not an artefact of
the predicate: `Lean4Lean/Inductive/Add.lean` computes `isRec` with `indTypes.any`, so a mutual
block none of whose members is recursive really does get `isRec = false` on every member, and
`isNonRecStructure` really does answer `true` for `A`.

Consequence for the flip: `VEnv.IsStructure` must weaken `types : D.types = [T]` to
`T ∈ D.types` before `StructureBridge` can be proved.  That edit is in
`Theory/Inductive/Structure.lean` and is **not** made here. -/
theorem indShapeOf_not_singleton :
    IndShapeOf decl2 id (.inductInfo aInd) ∧
    aInd.isRec = false ∧ aInd.numIndices = 0 ∧ aInd.ctors = [`MutNonRec.A.mk] ∧
    ∀ T, decl2.types ≠ [T] := by
  refine ⟨⟨aInd, rfl, ⟨_, List.mem_cons_self, rfl⟩, fun T hT hn => ?_⟩, rfl, rfl, rfl, ?_⟩
  · have hts : decl2.types
        = [{ name := `MutNonRec.A, type := .sort (.succ .zero), indices := [],
             ctors := [{ name := `MutNonRec.A.mk, params := [], fields := [], args := [] }] },
           { name := `MutNonRec.B, type := .sort (.succ .zero), indices := [],
             ctors := [{ name := `MutNonRec.B.mk, params := [], fields := [], args := [] }] }] :=
      rfl
    rw [hts] at hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · refine ⟨aInd, rfl, rfl, rfl, rfl, rfl, fun _ T' hT' C hC => ?_⟩
      rw [hts] at hT'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT'
      rcases hT' with rfl | rfl <;>
        (simp only [List.mem_singleton] at hC; subst hC; rfl)
    · exact absurd hn (by decide)
  · intro T h
    have h2 : (2 : Nat) = 1 := congrArg List.length h
    exact absurd h2 (by decide)

end MutNonRec

end Lean4Lean
