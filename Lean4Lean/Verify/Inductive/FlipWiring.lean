import Lean4Lean.Verify.Inductive.TrExprSGeneral

/-!
# Meeting `ConstLookup` from the step's own staging data

`Verify/Inductive/TrExprSGeneral.lean`'s inferencer `ctorTr?` carries exactly one environment
hypothesis, `ConstLookup Γc env := ∀ c ci, Γc c = some ci → env.constants c = some ci`, and
`TrIndDeclN.trCtors` is quantified over the *staged* environment
`env.addIndTypesC D K = some env₁`.  This file discharges that hypothesis from the staging step
alone.

**The finding, and it corrects the shape the obligation was stated in.**  The obligation was
named as "*every `.const` leaf of a constructor type is either a pre-block constant or one of
`D.typeConstsC K`*" — a claim about the leaves of a surface `Lean.Expr`, needing an induction
over it.  No such induction is needed, and none is done here: `ConstLookup Γc env₁` mentions
neither constructor types nor `Expr` at all.  It is a claim about the **table** `Γc`, and the
correct form of the named lemma is §1.2:

    (∀ c ci, Γc c = some ci → (c, ci) ∈ D.typeConstsC K ∨ env.constants c = some ci)
      → env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁

§1.3 proves the **converse** too, unconditionally, so this is not a sufficient condition that
might be weakenable: at a staged environment `ConstLookup` *is* the split, an `↔`
(`constLookup_iff_split`).  Nothing stronger than the split is available and nothing weaker
suffices.

**Where the surface side really lives, so this file does not overclaim.**  Two obligations were
being conflated under one name.  The one about the environment is settled here, completely.  The
one about the *expression* survives as `CtorsInFragment Γc Us types`
(`TrExprSGeneral.lean` §4a) — every constructor type must be built from
`.sort/.bvar/.const/.app/.forallE/.mdata`, with each `.const` leaf **present in `Γc`**.  That is
where knowing the leaves is unavoidable: you cannot write down `Γc` without them.  But it is a
*computation* at a block, not a theorem: `decide`/`rfl` settles it, and both nested blocks in the
repo are checked in `TrExprSGeneral.lean` §4b.  So the split above is the whole of what a
*general* theorem owes, and the leaf enumeration is per-block data.

This file is deliberately upstream of `TrIndDeclNProducer.lean` (which imports it) and imports
only `TrExprSGeneral.lean`, so `Verify/Inductive/FlipConstruct.lean` — the module holding the
hand-built `trS_tac` bridges `tr_ntreeType` / `tr_ntreeNodeType` — is not in its closure.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 The split

`D.typeConstsC K` is `D.typeConsts.filterMap (if ·.1 ∈ K then none else some ·)`
(`Theory/Inductive/Restore.lean`), and `VEnv.addIndTypesC env D K = env.addConstList
(D.typeConstsC K)` (`Theory/Inductive/Companion.lean`).  So the staged environment is the
pre-block one plus exactly the non-companion members' type constants, and §1.2/§1.3 are the two
`addConstList` lookup lemmas read in the two directions. -/

/-- **"…or one of `D.typeConstsC K`", in the form a table entry can be checked against.**
A non-companion member of the block contributes its own type constant.  `RestrictCompanion.lean`
proves this inline at one site; §1.2 needs it at an arbitrary member. -/
theorem VInductDecl'.mem_typeConstsC_of_mem_types {D : VInductDecl'} {K : List Name}
    {T : VIndType} (hT : T ∈ D.types) (hK : T.name ∉ K) :
    (T.name, (⟨D.uvars, T.type⟩ : VConstant)) ∈ D.typeConstsC K := by
  rw [VInductDecl'.typeConstsC, List.mem_filterMap]
  exact ⟨(T.name, ⟨D.uvars, T.type⟩),
    List.mem_map.2 ⟨T, hT, rfl⟩, by simp only [if_neg hK]⟩

/-- **THE NAMED LEMMA, in its correct form.**  Every entry of the table is either one of the
block's own declared type constants or a constant of the pre-block environment; then the table
agrees with the *staged* environment.

No induction over `Expr`, no constructor type, no `TrExprS`: the whole content is the two
`addConstList` lookup lemmas. -/
theorem constLookup_of_split {env env₁ : VEnv} {D : VInductDecl'} {K : List Name}
    {Γc : Name → Option VConstant}
    (hsplit : ∀ c ci, Γc c = some ci → (c, ci) ∈ D.typeConstsC K ∨ env.constants c = some ci)
    (hst : env.addIndTypesC D K = some env₁) : ConstLookup Γc env₁ := by
  rw [VEnv.addIndTypesC] at hst
  intro c ci hc
  match hsplit c ci hc with
  | .inl hm => exact VEnv.addConstList_constants hst (c, ci) hm
  | .inr he => exact (VEnv.addConstList_le hst).constants he

/-- …and the **converse**, unconditionally.  So §1.2's hypothesis is not a convenient
sufficient condition: at a staged environment it is equivalent to `ConstLookup`, and there is
nothing weaker to look for. -/
theorem split_of_constLookup {env env₁ : VEnv} {D : VInductDecl'} {K : List Name}
    {Γc : Name → Option VConstant}
    (hst : env.addIndTypesC D K = some env₁) (hCL : ConstLookup Γc env₁) :
    ∀ c ci, Γc c = some ci → (c, ci) ∈ D.typeConstsC K ∨ env.constants c = some ci := by
  rw [VEnv.addIndTypesC] at hst
  intro c ci hc
  by_cases hm : c ∈ (D.typeConstsC K).map (·.1)
  · obtain ⟨d, hd, hd1⟩ := List.mem_map.1 hm
    refine .inl ?_
    have h2 : env₁.constants c = some d.2 := hd1 ▸ VEnv.addConstList_constants hst d hd
    have he : ci = d.2 := Option.some.inj ((hCL c ci hc).symm.trans h2)
    rw [he, ← hd1]
    exact hd
  · exact .inr ((VEnv.addConstList_constants_of_not_mem hst hm).symm.trans (hCL c ci hc))

/-- **`ConstLookup` at a staged environment IS the split.** -/
theorem constLookup_iff_split {env env₁ : VEnv} {D : VInductDecl'} {K : List Name}
    {Γc : Name → Option VConstant} (hst : env.addIndTypesC D K = some env₁) :
    ConstLookup Γc env₁ ↔
      ∀ c ci, Γc c = some ci → (c, ci) ∈ D.typeConstsC K ∨ env.constants c = some ci :=
  ⟨split_of_constLookup hst, (constLookup_of_split · hst)⟩

/-- **The form `TrIndDeclN.trCtors`'s producer wants**: quantified over the staged environment,
so it plugs straight into `trCtors_of_ctorTr`'s `hΓc` and into §1 of
`Verify/Inductive/TrIndDeclNProducer.lean`.  Note it says nothing about staging *succeeding* —
the field is staged, so the producer needs no `∃ env₁, …` premise. -/
theorem constLookup_staged_of_split {env : VEnv} {D : VInductDecl'} {K : List Name}
    {Γc : Name → Option VConstant}
    (hsplit : ∀ c ci, Γc c = some ci → (c, ci) ∈ D.typeConstsC K ∨ env.constants c = some ci) :
    ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁ :=
  fun _ hst => constLookup_of_split hsplit hst

/-- The same with the block half presented by *member*, which is how a block's table is
actually written: each entry is either a member the user declared (`T ∈ D.types`, `T.name ∉ K`,
at the member's own `uvars`/`type`) or something already in the environment.  This is the named
lemma's prose read literally, with "one of `D.typeConstsC K`" unfolded. -/
theorem constLookup_staged_of_member_or_pre {env : VEnv} {D : VInductDecl'} {K : List Name}
    {Γc : Name → Option VConstant}
    (h : ∀ c ci, Γc c = some ci →
      (∃ T ∈ D.types, T.name = c ∧ T.name ∉ K ∧ ci = ⟨D.uvars, T.type⟩) ∨
        env.constants c = some ci) :
    ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁ := by
  refine constLookup_staged_of_split fun c ci hc => ?_
  rcases h c ci hc with ⟨T, hT, hname, hK, hci⟩ | he
  · subst hname; subst hci
    exact .inl (VInductDecl'.mem_typeConstsC_of_mem_types hT hK)
  · exact .inr he

/-! ## §2 `trType` through the same inferencer

A member's *own* stored type needs no table entry when it is a sort telescope: `ctorTr?` reads
it off with the empty table, so `TrIndDeclN.trType` at such a member costs **nothing** about the
environment.  This is what lets §3 of `TrIndDeclNProducer.lean` discharge `trType` without
`Verify/Inductive/FlipConstruct.lean`'s `tr_ntreeType` and without `sortPiTr?`'s producer
(cone 3692). -/

/-- The empty table meets `ConstLookup` at every environment. -/
theorem constLookup_none {env : VEnv} : ConstLookup (fun _ => none) env :=
  fun _ _ hc => absurd hc nofun

/-- `TrIndType` for one member, through the inferencer. -/
theorem trIndType_of_ctorTr {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    {t : InductiveType} {T : VIndType} (hΓc : ConstLookup Γc env) (hname : t.name = T.name)
    {t' : VExpr} (h : ctorTr? Γc Us t.type [] = some (T.type, t')) : TrIndType env Us t T :=
  ⟨hname, trExprS_of_ctorTr hΓc h⟩

/-- **`TrIndDeclN.trType`, discharged through `ctorTr?`** — a second general producer for the
field, alongside `trType_of_sortPiTr` (`Verify/Inductive/TrTypeProducer.lean`, arity 10, cone
3692), and a *strictly wider* one.

`sortPiTr?` accepts only a **sort telescope**, i.e. a non-indexed member: `∀ …, Sort u`.
`ctorTr?` accepts `.const` and `.app` too, so it covers an **indexed** member as well — a
member whose type is `∀ (α : Type u) (n : Nat), Type u` has `Nat` as a `.const` leaf and is out
of `sortPiTr?`'s fragment but inside this one, needing only `Nat` in the table.

Note the environment: `trType` is **unstaged**, so the table must agree with the *pre-block*
environment.  That is not a restriction in practice — a member's own stored type is
`params → indices → Sort`, which cannot mention the block's own members — and it is why the
sort-telescope case costs nothing at all (`constLookup_none`). -/
theorem trType_of_ctorTr {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    {types : List InductiveType} {D : VInductDecl'} (hΓc : ConstLookup Γc env)
    (h : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      t.name = T.name ∧ ∃ t', ctorTr? Γc Us t.type [] = some (T.type, t')) :
    ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T := by
  intro j t T ht hT
  obtain ⟨hn, t', htr⟩ := h j t T ht hT
  exact trIndType_of_ctorTr hΓc hn htr

end Lean4Lean
