import Lean4Lean.Theory.Inductive.Nested
import Lean4Lean.Theory.Consistency

/-!
# The companion member: what `addInduct'` refuses, what admitting it costs

`Theory/Inductive/Nested.lean` closes with three open items, of which the first is

> **`addInduct'` still refuses a companion member, and that is a theorem of this file.**

This file answers that item in three parts.

1. **Where the refusal is.**  `VEnv.addInduct'` (`Theory/Inductive/Decl.lean`) is
   `addIndTypes >=> addIndCtors >=> addIndRecs`, and `addIndTypes` is
   `addConstList D.typeConsts` where `typeConsts` covers **every** member of `D.types`.
   `VEnv.addConst` returns `none` on an already-taken name.  So the refusal is one
   `addConst` call on the companion's own name.

   It is an **artefact, not a gate** — but an artefact that is load-bearing by accident.
   `addConst`'s duplicate test is a *freshness* test; it knows nothing about companions.
   The proof that it is not a gate is `fooComp_WF` below: the companion block
   `fooCompDecl` — which lies about `Foo`, claiming it has no constructors — satisfies
   `VInductDecl'.WF` over the very environment that declared `Foo`.  Worse, it satisfies
   it *because* the refusal happens: `VInductDecl'.WF.ctors` is stated over
   `env.addIndTypes D = some env₁`, and that hypothesis is exactly what a companion makes
   unsatisfiable, so the whole constructor half of `WF` goes **vacuous** at precisely the
   blocks a companion clause wants to admit.

2. **The generalisation, and the theorem that it is one.**  `VEnv.addInductC` below takes
   a set `K` of companion names and a recursor renaming, declares the type and constructor
   constants only of the *non-companion* members, and declares a recursor (under the
   renamed name) for every member.  `addInductC_eq_addInduct'` is the conservativity
   theorem: at `K = []` and `rn = id` it *is* `addInduct'`, so nothing already proved about
   `addInduct'` is disturbed.  The structural facts `Nested.lean` needs —
   `addInductC_le`, `addInductC_constants`, `addInductC_new_name`,
   `addInductC_type_fresh`, `addInductC_types_disjoint` — all survive, the last two
   restricted to non-companion members, which is the strongest form available and the one
   exit 4 actually uses.

   Why `K : List Name` and not a field on `VIndType`: a field would change
   `VInductDecl'`, which is read by ~400KB of files this stream does not own
   (`Inductive/Lemmas.lean`, `StructureClosed.lean`, `Verify/*`, `SetModel/*`).  `K` is an
   isomorphic external encoding — a block's type names are `Nodup` whenever it is added at
   all (`VEnv.WF'.induct_allNames_nodup`) — that costs nothing and breaks nothing.  The
   eventual `Decl.lean` edit can carry the flag internally.

3. **The guard, and the unsoundness it stops.**  Two checks are owed, and they are
   independent:

   * **G1, re-staging.**  `VInductDecl'.WF.ctors` must be re-stated over the
     companion-aware `addIndTypesC`, or it is vacuous for every companion block
     (`fooComp_WF`).
   * **G2, completeness.**  A companion's `ctors` must be *all* of `J`'s constructors.
     Nothing in `WF` says so, and G1 does not imply it: `ctors = []` satisfies every
     `∀ C ∈ T.ctors, …` clause vacuously.

   `fooComp_inconsistent` is the machine-checked negative for G2.  `fooCompDecl` claims
   `Foo` has no constructors; its recursor is therefore `∀ (C : Foo → Prop) (m : Foo), C m`,
   an eliminator with no minor premises over a type that is inhabited.  Applying it to the
   motive `fun _ => ∀ p : Prop, p` and to `Foo.mk (∀ p : Prop, p)` inhabits `falseProp`.
   This is `Theory/MutualDefUnsound.lean`'s shape, at the companion instead of at
   `unsafeDef`.

Read together: admitting the companion member is a two-line change to `addInduct'`, and it
is unsound unless G1 and G2 land in the same commit.
-/

namespace Lean4Lean

open VExpr (mkPi mkLams bvars)

/-! ## Part 1: locating the refusal -/

namespace VEnv
variable {env env' : VEnv} {D : VInductDecl'}

/-- **The refusal, in the form that names the failing call.**  `addIndTypes` — the *first*
stage of `addInduct'` — already returns `none` when a member's name is taken.  So the
refusal is not spread over the definition; it is one `addConst`. -/
theorem addIndTypes_eq_none_of_declared {T : VIndType} {ci : VConstant}
    (hT : T ∈ D.types) (hJ : env.constants T.name = some ci) : env.addIndTypes D = none := by
  rcases h : env.addIndTypes D with _ | env₁
  · rfl
  · have hmem : T.name ∈ (D.typeConsts.map (·.1)) :=
      List.mem_map_of_mem (f := (·.1))
        (List.mem_map_of_mem (f := fun T => (T.name, (⟨D.uvars, T.type⟩ : VConstant))) hT)
    exact absurd ((addConstList_fresh h).1 _ hmem) (by simp only [hJ]; exact nofun)

/-- …and therefore `addInduct'` does, which is `addInduct'_no_companion`
(`Theory/Inductive/Nested.lean`) in positive form. -/
theorem addInduct'_eq_none_of_declared {T : VIndType} {ci : VConstant}
    (hT : T ∈ D.types) (hJ : env.constants T.name = some ci) : env.addInduct' D = none := by
  rcases h : env.addInduct' D with _ | env₁
  · rfl
  · exact absurd (addInduct'_type_fresh h hT) (by simp only [hJ]; exact nofun)

end VEnv

/-! ## Part 2: the companion-aware extension

`K` lists the block's **companion** members by name: a member whose name is in `K` is not
declared, because it is already in the environment.  Its constructors are not declared
either.  Its *recursor* is, under `rn (mkRecName T.name)` — the nested path's
`mkAuxRecNameMap` renaming (`Inductive/Add.lean`), which is why the renaming is a parameter
rather than fixed. -/

namespace VInductDecl'
variable (D : VInductDecl') (K : List Name) (rn : Name → Name)

-- `typeConstsC` moved to `Theory/Inductive/Restore.lean` (it is a definitional prerequisite
-- of `VEnv.addInductR`, which has to be upstream of `Theory/Typing/Env.lean`).

/-- The constructor constants actually declared: those of non-companion members only. -/
def ctorConstsC : List (Name × VConstant) :=
  D.ctorsAll.filterMap fun (j, C) =>
    if (D.types.getD j default).name ∈ K then none else some (C.name, ⟨D.uvars, C.type D j⟩)

/-- Every member gets a recursor, companion or not — that is the whole point of a
companion — but under a renameable name. -/
def recConstsC : List (Name × VConstant) :=
  D.types.zipIdx.map fun (T, j) => (rn (Lean.mkRecName T.name), ⟨D.recUvars, D.recType j⟩)

def allConstsC : List (Name × VConstant) :=
  D.typeConstsC K ++ D.ctorConstsC K ++ D.recConstsC rn

def allNamesC : List Name := (D.allConstsC K rn).map (·.1)

end VInductDecl'

/-- Add only the non-companion type constants.  This is the staging environment a
companion-aware `VInductDecl'.WF.ctors` must be stated over (guard **G1**). -/
def VEnv.addIndTypesC (env : VEnv) (D : VInductDecl') (K : List Name) : Option VEnv :=
  env.addConstList (D.typeConstsC K)

/-- **The companion-aware environment extension.**  Stated in the `addInduct'_eq` shape so
that conservativity is a rewrite rather than a re-proof. -/
def VEnv.addInductC (env : VEnv) (D : VInductDecl') (K : List Name) (rn : Name → Name) :
    Option VEnv :=
  (env.addConstList (D.allConstsC K rn)).map (·.addIndRules D)

namespace VInductDecl'

@[simp] theorem typeConstsC_nil (D : VInductDecl') : D.typeConstsC [] = D.typeConsts := by
  simp [typeConstsC]

@[simp] theorem ctorConstsC_nil (D : VInductDecl') : D.ctorConstsC [] = D.ctorConsts := by
  simp [ctorConstsC, VInductDecl'.ctorConsts]

@[simp] theorem recConstsC_id (D : VInductDecl') : D.recConstsC id = D.recConsts := rfl

@[simp] theorem allConstsC_nil (D : VInductDecl') : D.allConstsC [] id = D.allConsts := by
  simp [allConstsC, VInductDecl'.allConsts]

end VInductDecl'

namespace VEnv
variable {env env' env₁ env₂ env₃ : VEnv} {D D' : VInductDecl'} {K K' : List Name}
  {rn rn' : Name → Name}

/-- **Conservativity.**  With no companions and no renaming, `addInductC` *is* `addInduct'`.
So the generalisation disturbs nothing already proved. -/
theorem addInductC_eq_addInduct' (env : VEnv) (D : VInductDecl') :
    env.addInductC D [] id = env.addInduct' D := by
  rw [VEnv.addInductC, VInductDecl'.allConstsC_nil, ← VEnv.addInduct'_eq]

theorem addInductC_le (h : env.addInductC D K rn = some env') : env ≤ env' := by
  rw [VEnv.addInductC, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  exact (addConstList_le h1).trans addIndRules_le

theorem addInductC_constants (h : env.addInductC D K rn = some env') :
    ∀ c ∈ D.allConstsC K rn, env'.constants c.1 = some c.2 := by
  rw [VEnv.addInductC, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  intro c hc
  rw [addIndRules_constants]
  exact addConstList_constants h1 c hc

theorem addInductC_constants_of_not_mem {n : Name} (h : env.addInductC D K rn = some env')
    (hn : n ∉ D.allNamesC K rn) : env'.constants n = env.constants n := by
  rw [VEnv.addInductC, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  rw [addIndRules_constants]
  exact addConstList_constants_of_not_mem h1 hn

/-- **`addInduct'_new_name`, generalised.**  A companion block still introduces no name
outside its own list. -/
theorem addInductC_new_name {n : Name} (h : env.addInductC D K rn = some env')
    (hnew : env'.constants n ≠ env.constants n) : n ∈ D.allNamesC K rn :=
  Classical.byContradiction fun hc => hnew (addInductC_constants_of_not_mem h hc)

theorem addInductC_eq_some_iff :
    (∃ env', env.addInductC D K rn = some env') ↔
      (∀ n ∈ D.allNamesC K rn, env.constants n = none) ∧ (D.allNamesC K rn).Nodup := by
  simp only [VInductDecl'.allNamesC]
  rw [← addConstList_eq_some_iff (cs := D.allConstsC K rn)]
  constructor
  · rintro ⟨env', h⟩
    rw [VEnv.addInductC, Option.map_eq_some_iff] at h
    exact ⟨_, h.choose_spec.1⟩
  · rintro ⟨env₁, h⟩
    exact ⟨_, by rw [VEnv.addInductC, h]; rfl⟩

/-- **`addInduct'_type_fresh`, generalised — and this is the strongest form available.**
A *non-companion* member is still a newly declared constant.  A companion member is not,
and that is the entire content of the change. -/
theorem addInductC_type_fresh (h : env.addInductC D K rn = some env') {T : VIndType}
    (hT : T ∈ D.types) (hK : T.name ∉ K) : env.constants T.name = none :=
  (addInductC_eq_some_iff.1 ⟨_, h⟩).1 _ <| by
    refine List.mem_map_of_mem (f := (·.1)) (a := (T.name, ⟨D.uvars, T.type⟩)) ?_
    simp only [VInductDecl'.allConstsC, List.mem_append]
    refine .inl (.inl ?_)
    simp only [VInductDecl'.typeConstsC, List.mem_filterMap]
    exact ⟨_, List.mem_map_of_mem (f := fun T => (T.name, (⟨D.uvars, T.type⟩ : VConstant))) hT,
      by simp [hK]⟩

/-- The non-companion type constants are present, at their stored types. -/
theorem addInductC_types (h : env.addInductC D K rn = some env') {T : VIndType}
    (hT : T ∈ D.types) (hK : T.name ∉ K) :
    env'.constants T.name = some ⟨D.uvars, T.type⟩ :=
  addInductC_constants h (T.name, ⟨D.uvars, T.type⟩) <| by
    simp only [VInductDecl'.allConstsC, List.mem_append]
    refine .inl (.inl ?_)
    simp only [VInductDecl'.typeConstsC, List.mem_filterMap]
    exact ⟨_, List.mem_map_of_mem (f := fun T => (T.name, (⟨D.uvars, T.type⟩ : VConstant))) hT,
      by simp [hK]⟩

/-- Every member's recursor is present, at `recType`, under the renamed name. -/
theorem addInductC_recs (h : env.addInductC D K rn = some env') {T : VIndType} {j : Nat}
    (hT : (T, j) ∈ D.types.zipIdx) :
    env'.constants (rn (Lean.mkRecName T.name)) = some ⟨D.recUvars, D.recType j⟩ :=
  addInductC_constants h _ <| by
    simp only [VInductDecl'.allConstsC, List.mem_append]
    exact .inr (List.mem_map_of_mem hT)

/-- **`addInduct'_types_disjoint`, generalised.**  Exit 4's uniqueness handle survives, for
the members that are genuinely declared.  It *cannot* extend to companions, and that is not
a defect of the proof: a companion's whole purpose is to name a type another block already
declared, so "at most one block declares `J`" stays true only if a companion is not
counted as declaring it. -/
theorem addInductC_types_disjoint
    (h : env.addInductC D K rn = some env₁) (hle : env₁ ≤ env₂)
    (h' : env₂.addInductC D' K' rn' = some env₃)
    {T T' : VIndType} (hT : T ∈ D.types) (hK : T.name ∉ K)
    (hT' : T' ∈ D'.types) (hK' : T'.name ∉ K') : T.name ≠ T'.name := by
  intro hname
  have h1 : env₂.constants T.name = some ⟨D.uvars, T.type⟩ :=
    hle.constants (addInductC_types h hT hK)
  rw [hname, addInductC_type_fresh h' hT' hK'] at h1
  exact absurd h1 nofun

end VEnv

/-! ## Part 3: the two guards

**G1 — re-staging.**  `VInductDecl'.WF.ctors` is stated over `env.addIndTypes D = some env₁`.
A companion block makes that hypothesis unsatisfiable (`fooComp_addIndTypes_none`), so the
whole constructor half of `WF` becomes vacuous.  The companion-aware staging environment is
`VEnv.addIndTypesC`, defined above; the clause must be moved onto it.  `fooComp_WF` is the
proof that the move is mandatory rather than cosmetic.

**G2 — completeness.**  Nothing in `VInductDecl'.WF` — re-staged or not — says a companion
member lists *all* of `J`'s constructors.  `CompanionSound` below is everything the
environment alone can check, and it is satisfied by a companion that lists none of them
(`fooComp_sound`); `CompanionComplete` is the missing clause.  The separation matters
because G1 does not imply G2: every `∀ C ∈ T.ctors, …` clause is vacuous at `ctors = []`.

Note the shape of `CompanionComplete`: it quotes the *history*, not the constants map.  Two
blocks sharing a type name agree on `⟨uvars, type⟩` and on nothing else — in particular not
on `ctors` — so `env.constants` cannot express completeness.  This is exactly why exit 4
routes through the ι-rules (`VEnv.WF.iota_type_uniq`, `Theory/Inductive/Nested.lean`), and
why the zero-constructor case (`VInductDecl'.iotaRules_eq_nil`) has no certificate there. -/

/-- **The soundness half of the companion guard.**  Everything the environment on its own
can check about a companion member: the type it claims for `J` is the one `J` has, and each
constructor it claims for `J` is present at the type the block derives for it. -/
structure VInductDecl'.CompanionSound (env : VEnv) (D : VInductDecl') (K : List Name) :
    Prop where
  type_agree : ∀ T ∈ D.types, T.name ∈ K → env.constants T.name = some ⟨D.uvars, T.type⟩
  ctor_agree : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ C ∈ T.ctors, env.constants C.name = some ⟨D.uvars, C.type D j⟩

/-- **The completeness half — guard G2, the one that is missing.**  A companion member's
constructor list must be *all* of `J`'s, as recorded by the block of the history that
declared `J`.  Names are the right granularity: a companion's constructor types are `J`'s
with the parameter instantiation substituted, so the types move and the names do not. -/
structure VInductDecl'.CompanionComplete (ds : List VDecl) (D : VInductDecl')
    (K : List Name) : Prop where
  ctors_complete : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∃ (D₀ : VInductDecl') (j₀ : Nat) (T₀ : VIndType),
      VDecl.induct D₀ ∈ ds ∧ D₀.types[j₀]? = some T₀ ∧ T₀.name = T.name ∧
        T.ctors.map (·.name) = T₀.ctors.map (·.name)

/-- **G2 is well defined**: the constructor list it quotes is a function of the *name*
alone.  Two `.induct` steps of one well-formed history that carry a type of the same name
are the same step, at the same index, with the same type.

This is the assembly of `VEnv.WF'.induct_eq_of_type_name` and
`VInductDecl'.types_eq_of_name_eq` (both `Theory/Inductive/Nested.lean`), and it is what
makes `CompanionComplete` a *check* rather than an existential that a liar could satisfy by
picking a different block. -/
theorem VEnv.WF'.companion_target_uniq {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    {D₀ D₁ : VInductDecl'} {j₀ j₁ : Nat} {T₀ T₁ : VIndType}
    (h₀ : VDecl.induct D₀ ∈ ds) (h₁ : VDecl.induct D₁ ∈ ds)
    (hT₀ : D₀.types[j₀]? = some T₀) (hT₁ : D₁.types[j₁]? = some T₁)
    (hname : T₀.name = T₁.name) : D₀ = D₁ ∧ j₀ = j₁ ∧ T₀ = T₁ := by
  have hD : D₀ = D₁ := H.induct_eq_of_type_name D₀ D₁ h₀ h₁ T₀ (List.mem_of_getElem? hT₀)
    T₁ (List.mem_of_getElem? hT₁) hname
  subst hD
  obtain ⟨hj, hT⟩ := VInductDecl'.types_eq_of_name_eq (H.induct_allNames_nodup D₀ h₀)
    hT₀ hT₁ hname
  exact ⟨rfl, hj, hT⟩

/-- **Exit 4 supplies the "not fewer" direction of G2, wherever an ι-rule exists.**  If any
ι-rule of a recursor named `J.rec` is in `env.defeqs`, then the block of the history that
declared `J` has a *nonempty* constructor list — so a companion claiming `ctors = []` for
that `J` is refuted by the environment alone.

This is exit 4 (`VEnv.WF.iota_type_uniq`, `Theory/Inductive/Nested.lean`) doing the job it
was identified for, and it is what catches `fooCompDecl` below.  Its limit is the one
`VInductDecl'.iotaRules_eq_nil` records: a `J` with genuinely no constructors contributes no
ι-rule, so nothing here fires and the certificate must come from `recType` inversion
instead. -/
theorem VEnv.WF'.ctors_ne_nil_of_iotaRule {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    {D D₀ : VInductDecl'} {j q j₀ : Nat} {T T₀ : VIndType} {C : VIndCtor}
    (hdf : env.defeqs (D.iotaRule j q C)) (hTj : D.types[j]? = some T)
    (h₀ : VDecl.induct D₀ ∈ ds) (hT₀ : D₀.types[j₀]? = some T₀)
    (hname : T₀.name = T.name) : T₀.ctors ≠ [] := by
  obtain ⟨D₁, j₁, T₁, hD₁, hT₁, hn₁, -, -, ⟨q₀, C₀, hC₀, -⟩, -⟩ :=
    H.iota_type_uniq hdf hdf hTj hTj rfl
  obtain ⟨-, -, rfl⟩ := H.companion_target_uniq h₀ hD₁ hT₀ hT₁ (hname.trans hn₁.symm)
  intro he
  rw [he] at hC₀
  exact absurd hC₀ (by simp)

/-! ## Part 4: the witness -/

namespace InductiveDeclExamples

/-- The **companion block** for `Foo`: one member, named `Foo`, claiming `Foo` has **no
constructors**.  Everything else is `fooDecl`'s shape. -/
def fooCompDecl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .zero
  types := [{ name := `Foo, type := .sort .zero, indices := [], ctors := [] }]
  isLE := false

/-- The same companion, now also lying about `Foo`'s *type*: it reports `Foo : Type` where
the environment has `Foo : Prop`.  Used for guard G2a. -/
def fooCompDecl' : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  types := [{ name := `Foo, type := .sort (.succ .zero), indices := [], ctors := [] }]
  isLE := false

/-- The recursor the companion block would declare: `∀ (C : Foo → Prop) (m : Foo), C m`. -/
theorem fooCompDecl_recType_eq : fooCompDecl.recType 0 =
    .forallE (.forallE (.const `Foo []) (.sort .zero))
      (.forallE (.const `Foo []) (.app (.bvar 1) (.bvar 0))) := rfl

theorem fooCompDecl_iotaRules : fooCompDecl.iotaRules = [] := rfl

theorem fooDecl_recType_eq : fooDecl.recType 0 =
    .forallE (.forallE (.const `Foo []) (.sort .zero))
      (.forallE (.forallE (.sort .zero) (.app (.bvar 1) (.app (.const `Foo.mk []) (.bvar 0))))
        (.forallE (.const `Foo []) (.app (.bvar 2) (.bvar 0)))) := rfl

/-! ### The name-level facts, independent of the environment -/

/-- The nested path's renaming: the companion's recursor is `Foo.rec_1`, exactly the shape
`mkAuxRecNameMap` produces (`Lean4Lean/Inductive/Add.lean`). -/
def fooCompRec : Name → Name := fun _ => `Foo.rec_1

/-- The companion block declares **one** constant: the renamed recursor.  No type constant
(`Foo` exists), no constructor constants (it claims none), and no ι-rules
(`fooCompDecl_iotaRules`). -/
theorem fooComp_allConstsC :
    fooCompDecl.allConstsC [`Foo] fooCompRec
      = [(`Foo.rec_1, ⟨0, fooCompDecl.recType 0⟩)] := by
  simp [VInductDecl'.allConstsC, VInductDecl'.typeConstsC, VInductDecl'.ctorConstsC,
    VInductDecl'.recConstsC, VInductDecl'.typeConsts, VInductDecl'.ctorsAll, fooCompDecl,
    fooCompRec, VInductDecl'.recUvars]

/-- **The companion is not complete**: `Foo` really does have a constructor, and the
companion lists none.  This is guard **G2** failing, and it is the *only* thing wrong with
`fooCompDecl` — see `fooComp_WF` and `fooComp_sound`. -/
theorem fooComp_not_complete :
    ¬ fooCompDecl.CompanionComplete [VDecl.induct fooDecl] [`Foo] := by
  rintro ⟨hc⟩
  obtain ⟨D₀, j₀, T₀, hmem, hT₀, -, hnames⟩ :=
    hc 0 { name := `Foo, type := .sort .zero, indices := [], ctors := [] } rfl (by simp)
  simp only [List.mem_singleton, VDecl.induct.injEq] at hmem
  subst hmem
  match j₀, hT₀ with
  | 0, hT₀ =>
    simp [fooDecl] at hT₀
    subst hT₀
    simp at hnames

/-- `∀ p : Prop, p` is a proposition, in any environment and any context. -/
theorem falseProp_hasType (env : VEnv) (U : Nat) (Γ : List VExpr) :
    env.HasType U Γ falseProp (.sort .zero) :=
  .defeqDF
    (.sortDF (l := .imax (.succ .zero) .zero) (l' := .zero) ⟨trivial, trivial⟩ trivial
      VLevel.imax_zero)
    (.forallEDF (u := .succ .zero) (v := .zero)
      (.sortDF trivial trivial (.refl _)) (.bvar .zero))

/-- The inhabitant of `falseProp` the companion's recursor supplies:
`Foo.rec_1 (fun _ => ∀ p : Prop, p) (Foo.mk (∀ p : Prop, p))`. -/
def fooBad : VExpr :=
  .app (.app (.const `Foo.rec_1 []) (.lam (.const `Foo []) falseProp))
    (.app (.const `Foo.mk []) falseProp)

/-- **The witness is caught by exit 4.**  `Foo` has an ι-rule in `fooEnv`
(`fooIota_defeq`, `Theory/Inductive/Nested.lean`), so the environment itself refutes the
companion's claim that `Foo` has no constructors.  The guard is therefore not only
necessary (`fooComp_inconsistent`) but *available* — at every `J` that has a constructor. -/
theorem fooComp_caught : (fooDecl.types[0]!).ctors ≠ [] :=
  fooHistory.ctors_ne_nil_of_iotaRule (D := fooDecl) (j := 0) fooIota_defeq rfl
    (List.Mem.head _) (j₀ := 0) rfl rfl

/-! ### The honest environment, and the facts read off it -/

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' fooDecl = some env₁)
include h

theorem foo_const : env₁.constants `Foo = some ⟨0, .sort .zero⟩ :=
  VEnv.addInduct'_types h (List.Mem.head _)

theorem fooMk_const :
    env₁.constants `Foo.mk = some ⟨0, .forallE (.sort .zero) (.const `Foo [])⟩ :=
  VEnv.addInduct'_ctors h (List.Mem.head _)

theorem fooRec1_fresh : env₁.constants `Foo.rec_1 = none := by
  rw [VEnv.addInduct'_constants_of_not_mem h (by decide)]; rfl

/-! ### Guard G1 is missing: `WF` says nothing about a companion block -/

/-- `addInduct'`'s refusal, at the concrete witness — located at `addIndTypes`, the first
stage. -/
theorem fooComp_addIndTypes_none : env₁.addIndTypes fooCompDecl = none :=
  VEnv.addIndTypes_eq_none_of_declared (List.Mem.head _) (foo_const h)

theorem fooComp_addInduct'_none : env₁.addInduct' fooCompDecl = none :=
  VEnv.addInduct'_eq_none_of_declared (List.Mem.head _) (foo_const h)

/-- **The refusal is not a gate.**  `fooCompDecl` lies about `Foo` — it says `Foo` has no
constructors, when the block that declared `Foo` gave it `Foo.mk` — and yet it satisfies
`VInductDecl'.WF` over the environment that declared `Foo`.

The `ctors` field is where that is decided, and it is discharged by `absurd`: its
hypothesis is `env₁.addIndTypes fooCompDecl = some env₂`, which is exactly the refusal.
So the constructor half of `WF` is **vacuous at every companion block** — which is guard
**G1**: the clause has to be re-staged over `VEnv.addIndTypesC` before a companion member
is admitted, or `WF` stops constraining constructors at all. -/
theorem fooComp_WF : fooCompDecl.WF env₁ where
  types_ne := by simp [fooCompDecl]
  params := trivial
  types := by
    intro T hT
    simp [fooCompDecl] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₂ he
    rw [fooComp_addIndTypes_none h] at he
    exact absurd he nofun
  isLE := by simp [fooCompDecl]

/-! ### Guard G2a is missing as well: `WF` does not pin the companion's *type* -/

/-- **`VInductDecl'.WF` does not relate a companion's stored type to the environment's.**
No clause of `VIndType.WF` mentions `env.constants T.name`: `isType` says the *claimed* type
is a type, and `canon` relates it only to the block's own `params`/`indices`/`lvl`.  Both are
satisfied by `fooCompDecl'` (below), which reports `Foo : Type` when `Foo : Prop`.

That is guard **G2a** — `CompanionSound.type_agree` — and it is independent of G1 and G2. -/
theorem fooComp'_WF : fooCompDecl'.WF env₁ where
  types_ne := by simp [fooCompDecl']
  params := trivial
  types := by
    intro T hT
    simp [fooCompDecl'] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₂ he
    rw [VEnv.addIndTypes_eq_none_of_declared (List.Mem.head _) (foo_const h)] at he
    exact absurd he nofun
  isLE := by simp [fooCompDecl']

/-- …and `CompanionSound.type_agree` is exactly what rejects it. -/
theorem fooComp'_not_sound : ¬ fooCompDecl'.CompanionSound env₁ [`Foo] := by
  rintro ⟨hty, -⟩
  have hx := hty _ (List.Mem.head _) (List.Mem.head _)
  rw [foo_const h] at hx
  exact absurd (congrArg (fun o => o.elim default VConstant.type) hx) (by simp)

/-! ### Guard G2 is missing too: the companion is *sound* and *incomplete* -/

/-- The companion satisfies everything the environment can check: it claims `Foo : Prop`,
which is true, and it claims no constructors, so the constructor clause is vacuous. -/
theorem fooComp_sound : fooCompDecl.CompanionSound env₁ [`Foo] where
  type_agree := by
    intro T hT _
    simp [fooCompDecl] at hT
    subst hT
    exact foo_const h
  ctor_agree := by
    intro j T hT _ C hC
    match j, hT with
    | 0, hT =>
      simp [fooCompDecl] at hT
      subst hT
      simp at hC

/-! ### …and the companion-aware extension admits it, with an inconsistent result -/

/-- **`addInductC` admits the companion member.**  This is the item
`Theory/Inductive/Nested.lean` left open, discharged: the block is the one `addInduct'`
returns `none` on (`fooComp_addInduct'_none`), and the companion-aware extension succeeds
on the very same input over the very same environment. -/
theorem fooComp_admitted :
    ∃ env₂, env₁.addInductC fooCompDecl [`Foo] fooCompRec = some env₂ := by
  refine VEnv.addInductC_eq_some_iff.2 ⟨?_, ?_⟩ <;>
    rw [VInductDecl'.allNamesC, fooComp_allConstsC] <;> simp
  exact fooRec1_fresh h

/-- **The negative.**  Admitting the companion member without guard G2 produces an
inconsistent environment.

`fooCompDecl` passes `VInductDecl'.WF` (`fooComp_WF`) and `CompanionSound`
(`fooComp_sound`); the only thing wrong with it is `CompanionComplete`
(`fooComp_not_complete`).  Its recursor is therefore an eliminator with **no minor
premises** over `Foo`, which `Foo.mk` inhabits, and the two together inhabit
`∀ p : Prop, p`.

This is `Theory/MutualDefUnsound.lean`'s shape — a step that satisfies every stated
condition and produces `falseProp` — relocated from `unsafeDef` to the companion. -/
theorem fooComp_inconsistent {env₂ : VEnv}
    (h2 : env₁.addInductC fooCompDecl [`Foo] fooCompRec = some env₂) :
    ¬ env₂.Consistent := by
  have hle := VEnv.addInductC_le h2
  have hFoo : env₂.constants `Foo = some ⟨0, .sort .zero⟩ := hle.constants (foo_const h)
  have hmk : env₂.constants `Foo.mk = some ⟨0, .forallE (.sort .zero) (.const `Foo [])⟩ :=
    hle.constants (fooMk_const h)
  have hrec : env₂.constants `Foo.rec_1 = some ⟨0, fooCompDecl.recType 0⟩ :=
    VEnv.addInductC_constants h2 _ (by rw [fooComp_allConstsC]; exact List.Mem.head _)
  have hM : env₂.HasType 0 [] (.lam (.const `Foo []) falseProp)
      (.forallE (.const `Foo []) (.sort .zero)) :=
    .lamDF (.constDF hFoo nofun nofun rfl .nil) (falseProp_hasType _ _ _)
  have hmkc : env₂.HasType 0 [] (.const `Foo.mk [])
      (.forallE (.sort .zero) (.const `Foo [])) := .constDF hmk nofun nofun rfl .nil
  have hmajor : env₂.HasType 0 [] (.app (.const `Foo.mk []) falseProp) (.const `Foo []) :=
    .appDF hmkc (falseProp_hasType _ _ _)
  have hR : env₂.HasType 0 [] (.const `Foo.rec_1 []) (fooCompDecl.recType 0) :=
    .constDF hrec nofun nofun rfl .nil
  rw [fooCompDecl_recType_eq] at hR
  have happ : env₂.HasType 0 [] fooBad
      (.app (.lam (.const `Foo []) falseProp) (.app (.const `Foo.mk []) falseProp)) :=
    .appDF (.appDF hR hM) hmajor
  exact fun hcon => hcon ⟨fooBad,
    .defeqDF (.beta (falseProp_hasType _ _ _) hmajor) happ⟩

end

end InductiveDeclExamples

end Lean4Lean

