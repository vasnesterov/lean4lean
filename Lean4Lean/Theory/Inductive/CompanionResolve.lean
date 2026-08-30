import Lean4Lean.Theory.Inductive.Companion

/-!
# G2 made structural: a companion's constructors are *taken*, not *claimed*

`Theory/Inductive/Companion.lean` leaves four guards owed by the companion-aware extension
`VEnv.addInductC`, and one machine-checked negative:

* **G1** — `VInductDecl'.WF.ctors` is staged over `VEnv.addIndTypes`, which a companion
  block makes unsatisfiable, so the whole constructor half of `WF` goes vacuous
  (`fooComp_WF`).
* **G2** — nothing says a companion's `ctors` are *all* of `J`'s.  `fooComp_inconsistent`
  is the negative: a companion claiming `Foo` has no constructors gets the eliminator
  `∀ (C : Foo → Prop) (m : Foo), C m`, which inhabits `∀ p : Prop, p`.
* **G2a** — nothing relates the companion's stored *type* to `J`'s (`fooComp'_WF`).
* **G3** — the `.safe` gate examines only *declared* constants, and a companion declares
  only its recursor.

This file discharges G2 and G2a and installs G1.  The method is the one
`docs/handoff-nested-companion.md` §7 recommended, and the reason it is the right one is
worth restating because it is *not* the reason given there.

## Why a definition and not a check

The handoff argued: exit 4 (`VEnv.WF'.ctors_ne_nil_of_iotaRule`) bounds a companion's
constructor list from *below* wherever an ι-rule exists but gives no upper bound, and a
definition has no upper/lower gap at all.  That is true but it undersells the case, and one
half of it is wrong in a way that matters:

* **The lower bound exit 4 supplies is far weaker than G2.**  `ctors_ne_nil_of_iotaRule`
  concludes `T₀.ctors ≠ []` — it says the *declaring* block has some constructor.  It says
  nothing about the companion's own list, so it does not even exclude a companion that
  drops all but one constructor of a two-constructor `J`.  It catches `fooCompDecl` only
  because that witness claims `[]`, and it catches it via a statement about `fooDecl`, not
  about `fooCompDecl`.
* **The upper bound is the *dangerous* direction, not the lesser one.**  An over-claim adds
  a minor premise and a spurious ι-rule, and the spurious rule's left-hand side is a
  `iotaLhs` of a constructor name that `env` already binds — so it is `IsDefEq`-related to
  the real rule for that constructor and equates two distinct minor premises.
* **Neither direction is what a nested block actually does.**  `restoreNested` does not
  *check* the auxiliary block's constructors against `List`'s; it *copies* them, with the
  parameter instantiation substituted.  A definition is therefore the faithful model and a
  check is the unfaithful one, quite apart from which is easier to prove.

So the repair here is: **resolve first, extend second.**  `VInductDecl'.resolveC` replaces
every companion member of a block by the member the declaration history records under that
name — not just its `ctors`, the whole `VIndType` — and fails if the history records none.
Whatever the caller wrote in a companion member is *discarded*, so there is no field left
to lie in.  `resolveC_complete` is then G2 as a theorem rather than a hypothesis, and
`resolveC_sound` is G2a, modulo one explicitly stated residue
(`VInductDecl'.CompanionShape`) that is exactly what the head generalisation removes.

## What is machine-checked about the witness

`fooComp_resolveC : fooCompDecl.resolveC [.induct fooDecl] [`Foo] = some fooDecl` — by
`rfl`.  The lying block is not rejected; it is *overwritten by the truth*.  Consequently
`fooComp_killed`: for **every** environment the repaired step produces,

```
env₂.constants `Foo.rec_1 ≠ some ⟨0, fooCompDecl.recType 0⟩
```

and that constant equation is the *sole* premise `fooComp_inconsistent`'s proof takes from
the companion (`hrec`).  The false eliminator is not declared, so the witness has no input.

And the repair is not vacuous: `fooComp_admitted_repaired` shows the repaired step succeeds
on that very block, declaring `Foo.rec_1` at `fooDecl.recType 0` — the honest eliminator,
with its minor premise.

## What this file adds beyond the four guards

Part 9 makes the **head** generalisation concrete: `VInductDecl'.tyAppH` is
`J.{ls} A(params) args` with a *stored* instantiation `A`, `tyAppH_bvars` is the
conservativity equation pinning it as a generalisation of `VInductDecl'.tyApp`, and the two
offset moves `Theory/Inductive/Nested.lean` predicted are proved at the stored block
(`liftN_tyAppH`, `instAll_tyAppH`, plus `atRec_tyAppH`).

Part 10 records **G4, a fourth guard nobody had named**: `VEnv.addInductC` threads the
recursor renaming `rn` into `recConstsC` but **not** into `VEnv.addIndRules`, so a companion
declares its recursor as `rn (mkRecName J)` while emitting its ι-rules under `mkRecName J`.
`key_iotaRule_ne_renamed` is the machine-checked core.  Resolution does not fix this and
neither do G1–G3.

## The ordering rule, upgraded from argument to theorem

`docs/handoff-nested-companion.md` ends with "G1 must never land without G2", argued.  Here
it is machine-checked: `fooComp_WFC` proves that the re-staged `VInductDecl'.WFC` — G1,
installed — is **still satisfied by the unsoundness witness**.  Re-staging alone changes
nothing about it, because `∀ C ∈ T.ctors, …` is vacuous at `ctors = []` however it is
staged.  G1 is a prerequisite for G2 having anything to constrain, not a substitute.
-/

namespace Lean4Lean

/-! ## Part 5: resolution -/

namespace VInductDecl'

/-- The index and record of the block's own inductive type of the given name, if any. -/
def findType (D₀ : VInductDecl') (n : Name) : Option (Nat × VIndType) :=
  (D₀.types.zipIdx.find? fun p => p.1.name == n).map fun p => (p.2, p.1)

theorem findType_spec {D₀ : VInductDecl'} {n : Name} {j : Nat} {T : VIndType}
    (h : D₀.findType n = some (j, T)) : D₀.types[j]? = some T ∧ T.name = n := by
  rw [findType, Option.map_eq_some_iff] at h
  obtain ⟨⟨T', j'⟩, hf, heq⟩ := h
  cases heq
  exact ⟨List.mem_zipIdx_iff_getElem?.1 (List.mem_of_find?_eq_some hf),
    by simpa using List.find?_some hf⟩

end VInductDecl'

/-- **Where a name's inductive type comes from.**  Scan the declaration history for the
`.induct` step that declares an inductive type of the given name, and return the block, the
member's index in it, and the member itself.

In a well-formed history there is at most one such step (`VEnv.WF'.companion_target_uniq`),
so this is a *lookup*, not a choice. -/
def VDecl.findIndType : List VDecl → Name → Option (VInductDecl' × Nat × VIndType)
  | [], _ => none
  | d :: ds, n =>
    match d with
    | .induct D₀ =>
      match D₀.findType n with
      | some (j, T) => some (D₀, j, T)
      | none => VDecl.findIndType ds n
    | _ => VDecl.findIndType ds n

/-- **The lookup is sound.**  What it returns really is a member of a block of the history,
at the index it reports, under the name that was asked for. -/
theorem VDecl.findIndType_spec : ∀ {ds : List VDecl} {n : Name} {D₀ : VInductDecl'}
    {j : Nat} {T : VIndType}, VDecl.findIndType ds n = some (D₀, j, T) →
    VDecl.induct D₀ ∈ ds ∧ D₀.types[j]? = some T ∧ T.name = n
  | [], _, _, _, _, h => by simp [VDecl.findIndType] at h
  | d :: ds, n, D₀, j, T, h => by
    have tail : VDecl.findIndType ds n = some (D₀, j, T) →
        VDecl.induct D₀ ∈ d :: ds ∧ D₀.types[j]? = some T ∧ T.name = n := fun h => by
      obtain ⟨h1, h2, h3⟩ := VDecl.findIndType_spec h
      exact ⟨List.mem_cons_of_mem _ h1, h2, h3⟩
    cases d with
    | induct D₁ =>
      simp only [VDecl.findIndType] at h
      split at h
      · next j' T' hf =>
        cases h
        obtain ⟨h1, h2⟩ := VInductDecl'.findType_spec hf
        exact ⟨List.Mem.head _, h1, h2⟩
      · exact tail h
    | «axiom» _ | «def» _ | «opaque» _ | «example» _ | quot | unsafeDef _ =>
      exact tail h

namespace VInductDecl'

/-- Resolve one member.  A **companion** member (name in `K`) is *replaced* by the member
the history declares under that name — name, stored type, indices and constructors alike —
and resolution fails if the history declares none.  A non-companion member is kept.

Nothing the caller wrote in a companion member survives, which is the whole point: there is
no field left for a block to lie in. -/
def resolveType (ds : List VDecl) (K : List Name) (T : VIndType) : Option VIndType :=
  if T.name ∈ K then (VDecl.findIndType ds T.name).map (·.2.2) else some T

def resolveTypes (ds : List VDecl) (K : List Name) : List VIndType → Option (List VIndType)
  | [] => some []
  | T :: Ts => (resolveType ds K T).bind fun T' => (resolveTypes ds K Ts).map (T' :: ·)

/-- **The repaired block.**  `addInductC` must be run on this, never on the caller's `D`. -/
def resolveC (D : VInductDecl') (ds : List VDecl) (K : List Name) : Option VInductDecl' :=
  (resolveTypes ds K D.types).map fun ts => { D with types := ts }

/-! ### Basic facts -/

theorem resolveType_of_not_mem {ds K T} (h : T.name ∉ K) : resolveType ds K T = some T := by
  rw [resolveType, if_neg h]

theorem resolveType_name {ds K} {T T' : VIndType} (h : resolveType ds K T = some T') :
    T'.name = T.name := by
  rw [resolveType] at h
  split at h
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨D₀, j₀, T₀⟩, hf, rfl⟩ := h
    exact (VDecl.findIndType_spec hf).2.2
  · cases h; rfl

/-- A companion member of a resolved block **is** a member of the block of the history that
declared it — the same record, not a copy checked against it. -/
theorem resolveType_companion {ds K} {T T' : VIndType} (h : resolveType ds K T = some T')
    (hK : T.name ∈ K) : ∃ (D₀ : VInductDecl') (j₀ : Nat),
      VDecl.induct D₀ ∈ ds ∧ D₀.types[j₀]? = some T' := by
  rw [resolveType, if_pos hK, Option.map_eq_some_iff] at h
  obtain ⟨⟨D₀, j₀, T₀⟩, hf, rfl⟩ := h
  obtain ⟨h1, h2, -⟩ := VDecl.findIndType_spec hf
  exact ⟨D₀, j₀, h1, h2⟩

theorem resolveTypes_nil_K {ds} : ∀ Ts : List VIndType, resolveTypes ds [] Ts = some Ts
  | [] => rfl
  | T :: Ts => by
    rw [resolveTypes, resolveType_of_not_mem (by simp), resolveTypes_nil_K Ts]; rfl

/-- **Conservativity.**  With no companions, resolution is the identity. -/
@[simp] theorem resolveC_nil (D : VInductDecl') (ds : List VDecl) :
    D.resolveC ds [] = some D := by
  rw [resolveC, resolveTypes_nil_K]; rfl

theorem resolveTypes_getElem {ds K} : ∀ {Ts Ts' : List VIndType}, resolveTypes ds K Ts = some Ts' →
    ∀ {j : Nat} {T' : VIndType}, Ts'[j]? = some T' →
      ∃ T, Ts[j]? = some T ∧ resolveType ds K T = some T'
  | [], Ts', h, j, T', hj => by cases h; simp at hj
  | T :: Ts, Ts', h, j, T', hj => by
    rw [resolveTypes, Option.bind_eq_some_iff] at h
    obtain ⟨T₁, h1, h2⟩ := h
    rw [Option.map_eq_some_iff] at h2
    obtain ⟨Ts₁, h3, h4⟩ := h2
    cases h4
    match j with
    | 0 => cases hj; exact ⟨T, rfl, h1⟩
    | j+1 =>
      obtain ⟨T₂, hm, hr⟩ := resolveTypes_getElem h3 (by simpa using hj)
      exact ⟨T₂, by simpa using hm, hr⟩

/-- The fields resolution does not touch. -/
theorem resolveC_fields {D D' : VInductDecl'} {ds K} (h : D.resolveC ds K = some D') :
    D'.uvars = D.uvars ∧ D'.params = D.params ∧ D'.lvl = D.lvl ∧ D'.isLE = D.isLE := by
  rw [resolveC, Option.map_eq_some_iff] at h
  obtain ⟨ts, -, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem resolveC_getElem {D D' : VInductDecl'} {ds K} (h : D.resolveC ds K = some D')
    {j : Nat} {T' : VIndType} (hj : D'.types[j]? = some T') :
    ∃ T, D.types[j]? = some T ∧ resolveType ds K T = some T' := by
  rw [resolveC, Option.map_eq_some_iff] at h
  obtain ⟨ts, hts, rfl⟩ := h
  exact resolveTypes_getElem hts hj

end VInductDecl'


/-! ## Part 6: G2 and G2a, as theorems about `resolveC`

Everything below is a *consequence of the construction*.  No clause of any `WF` predicate is
consulted, and nothing is assumed about the caller's block beyond the resolution having
succeeded. -/

/-- Forward direction of `VInductDecl'.mem_ctorsAll`. -/
theorem VInductDecl'.mem_ctorsAll_of {D : VInductDecl'} {j : Nat} {T : VIndType}
    {C : VIndCtor} (hT : D.types[j]? = some T) (hC : C ∈ T.ctors) : (j, C) ∈ D.ctorsAll := by
  simp only [VInductDecl'.ctorsAll, List.mem_flatMap, List.mem_map]
  exact ⟨(T, j), List.mem_zipIdx_iff_getElem?.2 hT, C, hC, rfl⟩

/-- The constructor analogue of `VEnv.WF'.constants_induct_type`. -/
theorem VEnv.WF'.constants_induct_ctor {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    (D : VInductDecl') (hD : VDecl.induct D ∈ ds) {j : Nat} {C : VIndCtor}
    (hC : (j, C) ∈ D.ctorsAll) : env.constants C.name = some ⟨D.uvars, C.type D j⟩ := by
  obtain ⟨_, _, h, hle⟩ := H.exists_addInduct' D hD
  exact hle.constants (VEnv.addInduct'_ctors h hC)

/-- A constructor's *stored* type depends on its block only through the block's universe
count, its parameter count, and the name of the type it belongs to.

This is why the un-substituted companion of §5 works at all, and it is exactly the point the
head generalisation has to move: once a companion is headed `J A(params) ι` rather than
`J params ι`, the two sides differ by the instantiation and the equation below becomes a
substitution lemma. -/
theorem VIndCtor.type_congr (C : VIndCtor) {D D' : VInductDecl'} {j j' : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hT' : D'.types[j']? = some T)
    (hu : D.uvars = D'.uvars) (hp : D.params.length = D'.params.length) :
    C.type D j = C.type D' j' := by
  simp only [VIndCtor.type, VIndCtor.canonResult, VInductDecl'.tyApp,
    VInductDecl'.getD_types hT, VInductDecl'.getD_types hT', VInductDecl'.ownLvls, hu, hp]

namespace VInductDecl'

/-- **The residue the head generalisation removes.**  A companion member's parameters are
still the block's own parameter run (`VInductDecl'.tyApp`'s `bvars k D.np`), so the block
declaring `J` must agree with the companion block on the universe count and the parameter
count for the *stored* constructor types to coincide.

`ElimNestedInductive` copies the universe parameters, so the first conjunct is discharged by
the implementation; the second is the one the stored instantiation `A` replaces. -/
def CompanionShape (ds : List VDecl) (D : VInductDecl') (K : List Name) : Prop :=
  ∀ (D₀ : VInductDecl') (j₀ : Nat) (T₀ : VIndType), VDecl.induct D₀ ∈ ds →
    D₀.types[j₀]? = some T₀ → T₀.name ∈ K →
      D₀.uvars = D.uvars ∧ D₀.params.length = D.params.length

/-- **A companion member of a resolved block IS the declaring block's member.**  Not a copy
validated against it — the same `VIndType` record, name, stored type, indices and
constructors together.

This is the sharp form of G2: an *under*-claim and an *over*-claim are both impossible,
because there is no claim. -/
theorem resolveC_companion {D D' : VInductDecl'} {ds : List VDecl} {K : List Name}
    (h : D.resolveC ds K = some D') {j : Nat} {T : VIndType}
    (hT : D'.types[j]? = some T) (hK : T.name ∈ K) :
    ∃ (D₀ : VInductDecl') (j₀ : Nat), VDecl.induct D₀ ∈ ds ∧ D₀.types[j₀]? = some T := by
  obtain ⟨T₀, -, hr⟩ := resolveC_getElem h hT
  exact resolveType_companion hr (resolveType_name hr ▸ hK)

/-- **G2 is a theorem.**  `CompanionComplete` — the check `Companion.lean` had to state as a
hypothesis, and whose absence `fooComp_inconsistent` shows to be fatal — holds of every
resolved block, unconditionally. -/
theorem resolveC_complete {D D' : VInductDecl'} {ds : List VDecl} {K : List Name}
    (h : D.resolveC ds K = some D') : D'.CompanionComplete ds K where
  ctors_complete := by
    intro j T hT hK
    obtain ⟨D₀, j₀, hmem, hidx⟩ := resolveC_companion h hT hK
    exact ⟨D₀, j₀, T, hmem, hidx, rfl, rfl⟩

/-- **The zero-constructor companion, discharged.**  Exit 4's certificate
(`VEnv.WF'.ctors_ne_nil_of_iotaRule`) vanishes exactly when the companion claims no
constructors — which is the unsoundness witness's own shape, so the gap was not cosmetic.

Under resolution there is nothing left to certify: an empty companion constructor list is
*inherited* from the declaring block rather than asserted, so it is empty only when `J`
really has none.  This closes `Theory/Inductive/Nested.lean`'s second open item
(`Void1`/`T1`) for the companion, without any `recType` telescope inversion. -/
theorem resolveC_zero_ctors {D D' : VInductDecl'} {ds : List VDecl} {K : List Name}
    (h : D.resolveC ds K = some D') {j : Nat} {T : VIndType}
    (hT : D'.types[j]? = some T) (hK : T.name ∈ K) (hnil : T.ctors = []) :
    ∃ (D₀ : VInductDecl') (j₀ : Nat) (T₀ : VIndType),
      VDecl.induct D₀ ∈ ds ∧ D₀.types[j₀]? = some T₀ ∧ T₀.name = T.name ∧ T₀.ctors = [] := by
  obtain ⟨D₀, j₀, hmem, hidx⟩ := resolveC_companion h hT hK
  exact ⟨D₀, j₀, T, hmem, hidx, rfl, hnil⟩

/-- **G2a is a theorem too, modulo `CompanionShape`.**  `CompanionSound` — the clause that
rejects `fooCompDecl'`, the companion lying about `Foo`'s *sort* — is a consequence of
resolution over a well-formed history.

The two conjuncts come from different places, and the difference is informative:

* `type_agree` needs only the universe count, because resolution took `T.type` verbatim from
  the declaring block and `WF'.constants_induct_type` says the environment holds it there.
* `ctor_agree` needs the parameter count as well, because `VIndCtor.type` splices the
  parameters as a de Bruijn run (`VIndCtor.type_congr`).  That is the head generalisation's
  obligation, isolated. -/
theorem resolveC_sound {D D' : VInductDecl'} {ds : List VDecl} {env : VEnv} {K : List Name}
    (H : VEnv.WF' ds env) (h : D.resolveC ds K = some D') (hs : D'.CompanionShape ds K) :
    D'.CompanionSound env K where
  type_agree := by
    intro T hTmem hK
    obtain ⟨j, hT⟩ := List.mem_iff_getElem?.1 hTmem
    obtain ⟨D₀, j₀, hmem, hidx⟩ := resolveC_companion h hT hK
    obtain ⟨hu, -⟩ := hs D₀ j₀ T hmem hidx hK
    rw [H.constants_induct_type D₀ hmem (List.mem_of_getElem? hidx), hu]
  ctor_agree := by
    intro j T hT hK C hC
    obtain ⟨D₀, j₀, hmem, hidx⟩ := resolveC_companion h hT hK
    obtain ⟨hu, hp⟩ := hs D₀ j₀ T hmem hidx hK
    rw [H.constants_induct_ctor D₀ hmem (VInductDecl'.mem_ctorsAll_of hidx hC), hu,
      C.type_congr hidx hT hu hp]

/-! ### Guard G3: safety

`Verify/Environment/Basic.lean`'s `AddIndConsts.cons` carries `TrConstant .safe`, so the
`.safe` gate is checked on every **declared** constant.  A companion declares only its
recursor, so its target `J` and `J`'s constructors pass through unexamined — that is G3, and
`Companion.lean` §4 states it as an obligation that has to be written down somewhere because
the abstract theory models no safety tag.

Resolution reduces G3 to a property of the **history** rather than of the companion.  The
companion's target is not a constant recovered from `env.constants` — it is a member of an
`.induct` step of `ds`, by construction.  So whatever gate the history's `.induct` steps
passed, the companion's target passed too; nothing new needs checking at the companion.

The theorem is stated over an abstract `Safe : VInductDecl' → Prop` because `VDecl` carries
no safety tag.  On the refinement side `Safe` is "this block was admitted by `TrEnv'.induct`",
which is gated to `.safe` blocks (`Companion.lean` §4, read off
`Verify/Environment/Basic.lean` — *not* machine-checked here), and the hypothesis
`hsafe` is then discharged by the `TrEnv'` induction. -/
theorem resolveC_target_safe {D D' : VInductDecl'} {ds : List VDecl} {K : List Name}
    {Safe : VInductDecl' → Prop} (hsafe : ∀ D₀, VDecl.induct D₀ ∈ ds → Safe D₀)
    (h : D.resolveC ds K = some D') {j : Nat} {T : VIndType}
    (hT : D'.types[j]? = some T) (hK : T.name ∈ K) :
    ∃ D₀ : VInductDecl', Safe D₀ ∧ VDecl.induct D₀ ∈ ds ∧ T ∈ D₀.types := by
  obtain ⟨D₀, j₀, hmem, hidx⟩ := resolveC_companion h hT hK
  exact ⟨D₀, hsafe D₀ hmem, hmem, List.mem_of_getElem? hidx⟩

end VInductDecl'


/-! ## Part 7: G1, installed — and why it must not travel alone

`VInductDecl'.WF.ctors` is staged over `VEnv.addIndTypes`, which a companion block makes
unsatisfiable, so the constructor half of `WF` is vacuous at exactly the blocks a companion
clause wants to admit (`fooComp_WF`).  `WFC` below is `WF` with that clause re-staged onto
the companion-aware `VEnv.addIndTypesC`, and nothing else changed — `WFC_nil_iff` is the
conservativity theorem.

`fooComp_WFC` is the point of the section, and it is the machine-checked form of the
ordering rule `docs/handoff-nested-companion.md` could only argue: **the unsoundness witness
satisfies the re-staged predicate**.  Re-staging restores the clause's *domain*; it does not
give it any *content* at `ctors = []`, since `∀ C ∈ T.ctors, …` is vacuous however it is
staged.  G1 is what makes G2's constraint reachable, not a substitute for it. -/

theorem VEnv.addIndTypesC_nil (env : VEnv) (D : VInductDecl') :
    env.addIndTypesC D [] = env.addIndTypes D := by
  rw [VEnv.addIndTypesC, VInductDecl'.typeConstsC_nil, VEnv.addIndTypes]

/-- **Guard G1, installed.**  `VInductDecl'.WF` with the constructor clause staged over the
companion-aware `VEnv.addIndTypesC`, so that it constrains companion blocks instead of going
vacuous on them.

Stated here rather than by editing `VInductDecl'.WF` because that record is read by
`Inductive/Lemmas.lean`, `StructureClosed.lean`, `DeclExamples.lean` and every `Verify/`
consumer.  `WFC_nil_iff` says the eventual edit is a no-op on everything already proved. -/
structure VInductDecl'.WFC (env : VEnv) (D : VInductDecl') (K : List Name) : Prop where
  types_ne : D.types ≠ []
  params : OnCtx D.params.reverse (env.IsType D.uvars)
  types : ∀ T ∈ D.types, T.WF env D
  /-- Staged over `addIndTypesC`: the companion members are *already* in `env`, so only the
  genuinely new type constants are added before the constructors are checked. -/
  ctors : ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ j (T : VIndType), D.types[j]? = some T →
      ∀ (C : VIndCtor), C ∈ T.ctors → C.WF env₁ D j T
  isLE : D.isLE = true → D.LECond

/-- **Conservativity of G1.**  With no companions, the re-staged predicate is the old one. -/
theorem VInductDecl'.WFC_nil_iff {env : VEnv} {D : VInductDecl'} : D.WFC env [] ↔ D.WF env := by
  constructor
  · intro h
    exact { types_ne := h.types_ne, params := h.params, types := h.types, isLE := h.isLE,
            ctors := fun env₁ he => h.ctors env₁ (by rwa [VEnv.addIndTypesC_nil]) }
  · intro h
    exact { types_ne := h.types_ne, params := h.params, types := h.types, isLE := h.isLE,
            ctors := fun env₁ he => h.ctors env₁ (by rwa [VEnv.addIndTypesC_nil] at he) }

/-- **The repaired companion step**: resolve, then check the re-staged well-formedness of the
*resolved* block, then extend.

The order is the content.  Checking `D` and extending by `resolveC D` would be unsound in the
other direction (the checked block is not the declared one); checking `resolveC D` and
extending by `D` reinstates the lie.  Both halves quantify over the same `D'`. -/
def VEnv.AddCompanion (ds : List VDecl) (env : VEnv) (D : VInductDecl') (K : List Name)
    (rn : Name → Name) (env' : VEnv) : Prop :=
  ∃ D', D.resolveC ds K = some D' ∧ D'.WFC env K ∧ env.addInductC D' K rn = some env'

/-- **Conservativity of the whole repaired step.**  With no companion members it is exactly
`VDecl.WF.induct`'s premise pair: `D.WF env` together with `env.addInduct' D = some env'`.
So the repair adds no obligation to, and removes none from, any existing declaration. -/
theorem VEnv.AddCompanion_nil {ds : List VDecl} {env env' : VEnv} {D : VInductDecl'} :
    VEnv.AddCompanion ds env D [] id env' ↔ D.WF env ∧ env.addInduct' D = some env' := by
  rw [VEnv.AddCompanion]
  constructor
  · rintro ⟨D', hr, hwf, hadd⟩
    rw [VInductDecl'.resolveC_nil] at hr
    cases hr
    rw [VEnv.addInductC_eq_addInduct'] at hadd
    exact ⟨VInductDecl'.WFC_nil_iff.1 hwf, hadd⟩
  · rintro ⟨hwf, hadd⟩
    exact ⟨D, VInductDecl'.resolveC_nil _ _, VInductDecl'.WFC_nil_iff.2 hwf,
      by rw [VEnv.addInductC_eq_addInduct']; exact hadd⟩

/-- **G2 travels with the step.**  Every environment the repaired step produces came from a
block that is constructor-complete against the history. -/
theorem VEnv.AddCompanion_complete {ds : List VDecl} {env env' : VEnv} {D : VInductDecl'}
    {K : List Name} {rn : Name → Name} (h : VEnv.AddCompanion ds env D K rn env') :
    ∃ D', D.resolveC ds K = some D' ∧ D'.CompanionComplete ds K ∧
      env.addInductC D' K rn = some env' := by
  obtain ⟨D', hr, -, hadd⟩ := h
  exact ⟨D', hr, VInductDecl'.resolveC_complete hr, hadd⟩

/-! ## Part 8: the witness, re-run against the repair -/

namespace InductiveDeclExamples

/-- **The unsoundness witness, resolved.**  The block that claims `Foo` has no constructors
is not *rejected* — it is **overwritten by the truth**.  Resolution against the honest
one-step history returns `fooDecl` itself, on the nose. -/
theorem fooComp_resolveC :
    fooCompDecl.resolveC [VDecl.induct fooDecl] [`Foo] = some fooDecl := rfl

/-- The two recursor types are different terms: the honest one has a minor premise, the
companion's has none.  This is what the kill turns on. -/
theorem fooDecl_recType_ne_comp : fooDecl.recType 0 ≠ fooCompDecl.recType 0 := by
  rw [fooDecl_recType_eq, fooCompDecl_recType_eq]; simp

/-- The resolved block declares one constant — the renamed recursor — at the **honest**
recursor type.  (Compare `fooComp_allConstsC`, the same list at the false type.) -/
theorem fooComp_allConstsC_resolved :
    fooDecl.allConstsC [`Foo] fooCompRec = [(`Foo.rec_1, ⟨0, fooDecl.recType 0⟩)] := by
  simp [VInductDecl'.allConstsC, VInductDecl'.typeConstsC, VInductDecl'.ctorConstsC,
    VInductDecl'.recConstsC, VInductDecl'.typeConsts, VInductDecl'.ctorsAll, fooDecl,
    fooCompRec, VInductDecl'.recUvars]

/-- **G1 alone does not kill the witness.**  The lying block satisfies the *re-staged*
predicate too: `addIndTypesC` succeeds (it adds nothing, `Foo` being a companion), so the
constructor clause is now genuinely reachable — and it still says nothing, because
`∀ C ∈ [], …` is vacuous.

Together with `fooComp_inconsistent` (`Theory/Inductive/Companion.lean`) this is the ordering
rule as a theorem: **re-staging `WF.ctors` while `addInductC` is live and G2 is absent is
exactly the configuration that inhabits `∀ p : Prop, p`.**

Note the binder: `env₁` is arbitrary.  The witness satisfies the re-staged predicate in
*every* environment, which is stronger than `fooComp_WF`'s statement over the honest one. -/
theorem fooComp_WFC {env₁ : VEnv} : fooCompDecl.WFC env₁ [`Foo] where
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
    intro env₂ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp [fooCompDecl] at hT
      subst hT
      simp at hC
  isLE := by simp [fooCompDecl]

/-- **The witness is dead.**  For *every* environment the repaired step produces from the
lying block, the constant `Foo.rec_1` is bound to the **honest** recursor type — and
therefore not to the false one.

`fooComp_inconsistent` (`Theory/Inductive/Companion.lean`) takes exactly one thing from the
companion: the hypothesis

```lean
hrec : env₂.constants `Foo.rec_1 = some ⟨0, fooCompDecl.recType 0⟩
```

which it feeds to `.constDF` to type the eliminator `∀ (C : Foo → Prop) (m : Foo), C m`.
The second conjunct below is the negation of that hypothesis.  The witness has no input, so
the derivation of an inhabitant of `∀ p : Prop, p` does not start.

`env₁` is arbitrary here: the kill does not depend on how the honest environment arose. -/
theorem fooComp_killed {env₁ env₂ : VEnv}
    (h2 : VEnv.AddCompanion [VDecl.induct fooDecl] env₁ fooCompDecl [`Foo] fooCompRec env₂) :
    env₂.constants `Foo.rec_1 = some ⟨0, fooDecl.recType 0⟩ ∧
      env₂.constants `Foo.rec_1 ≠ some ⟨0, fooCompDecl.recType 0⟩ := by
  obtain ⟨D', hr, -, hadd⟩ := h2
  rw [fooComp_resolveC] at hr
  cases hr
  have hrec : env₂.constants `Foo.rec_1 = some ⟨0, fooDecl.recType 0⟩ :=
    VEnv.addInductC_constants hadd _ (by rw [fooComp_allConstsC_resolved]; exact List.Mem.head _)
  refine ⟨hrec, ?_⟩
  rw [hrec]
  intro hx
  exact fooDecl_recType_ne_comp (congrArg (fun o => o.elim default VConstant.type) hx)

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' fooDecl = some env₁)
include h

/-- **The honest companion passes the re-staged predicate.**  Non-vacuity of `WFC`: this is
`fooDecl_WF` (`Theory/Inductive/DeclExamples.lean`) re-run at `K = [`Foo]`, where the staging
environment is `env₁` itself because `typeConstsC` drops the companion member. -/
theorem fooDecl_WFC : fooDecl.WFC env₁ [`Foo] where
  types_ne := by simp [fooDecl]
  params := trivial
  types := by
    intro T hT
    simp [fooDecl] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₂ he j T hT C hC
    have henv : env₂ = env₁ := by
      simpa [VEnv.addIndTypesC, VInductDecl'.typeConstsC, VInductDecl'.typeConsts, fooDecl,
        VEnv.addConstList] using he.symm
    subst henv
    match j, hT with
    | 0, hT =>
      simp [fooDecl] at hT
      subst hT
      simp at hC
      subst hC
      refine { params_len := rfl, params_eq := .zero, fields := ?_,
               args_len := rfl, args_fresh := by simp, args_ty := .nil,
               result := .constDF (foo_const h) nofun nofun rfl .nil }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp at hF
        subst hF
        exact { hasType := .sortDF trivial trivial (.refl _)
                level := fun ls => by simp [VLevel.eval, fooDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.sort .zero, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                        _, .sortDF trivial trivial (.refl _)⟩ }
  isLE := by simp [fooDecl]

/-- **The repair is not vacuous.**  The repaired step succeeds on the very block
`addInduct'` refuses and `addInductC` mis-admitted — same block, same environment. -/
theorem fooComp_admitted_repaired :
    ∃ env₂, VEnv.AddCompanion [VDecl.induct fooDecl] env₁ fooCompDecl [`Foo] fooCompRec env₂ := by
  have hadd : ∃ env₂, env₁.addInductC fooDecl [`Foo] fooCompRec = some env₂ := by
    refine VEnv.addInductC_eq_some_iff.2 ⟨?_, ?_⟩ <;>
      rw [VInductDecl'.allNamesC, fooComp_allConstsC_resolved] <;> simp
    exact fooRec1_fresh h
  exact ⟨hadd.choose, fooDecl, fooComp_resolveC, fooDecl_WFC h, hadd.choose_spec⟩


end

end InductiveDeclExamples

/-! ## Part 9: the companion's *head*

Parts 5–8 fix the companion's **body** — which constructors it has and which type it claims.
They leave the item `docs/handoff-nested-companion.md` §5 identifies as the substantive
remainder: `docs/design-inductive.md` §9.3's second bullet,

> `tyApp` for a companion becomes `J.{ls} A(params) ι` instead of `.const I_j ownLvls …`.

`VInductDecl'.tyApp` puts the parameter block at a de Bruijn offset as `bvars k D.np`, a
contiguous run of variables.  A real `restoreNested` companion for the motivating example is
headed `List (Tree α)` — a **stored instantiation** `A = [Tree α]` over the block's
parameters, not the parameter run itself.

`tyAppH` below is the generalisation, and the three theorems after it are the algebra it has
to obey.  All three are consequences of lemmas that already existed, which is the content of
the estimate `Theory/Inductive/Nested.lean`'s offset-algebra section gave: **generalising the
head does not invalidate the de Bruijn arithmetic.**  What is new here is that the estimate
is now checked rather than argued, and that the conservativity equation
(`tyAppH_bvars`) pins the generalisation as a generalisation.

The stored block is written `A.map (·.liftN k)`: `A` lives over the block's parameter
context, whose binders sit `k` deep at the use site, so each entry is weakened by `k`.  At
`A = bvars 0 D.np` that is `bvars k D.np` — the old head, exactly. -/

namespace VInductDecl'

-- `tyAppH`, `tyAppH_bvars` and `tyAppH_bvars'` moved **verbatim** to
-- `Theory/Inductive/Restore.lean`: they are definitional prerequisites of `VEnv.addInductR`,
-- which has to sit upstream of `Theory/Typing/Env.lean` so that `VDecl.WF` can name the
-- nested step.  Everything else in this Part stays here.

/-! ### The two offset moves, at the stored parameter block

`Theory/Inductive/Nested.lean` argued that the head generalisation needs exactly two moves —
lifting past an outer cut, and instantiating a saturated spine away — and that both hold
under the side condition `cut ≤ k` that every existing offset lemma already supplies
(`hni : ni ≤ K₀` in `tyApp'_instAll'`, `hij : i + j ≤ k` in `shift_atRec_tyApp`).  Here they
are, entrywise on the stored block and then at the head. -/

/-- Lifting the stored block past a cut **below** it: `map_liftN_bvars_lo`'s counterpart.
The side condition is `c ≤ k`, i.e. the cut is below the parameters. -/
theorem map_liftN_map_liftN {A : List VExpr} {k m c : Nat} (h : c ≤ k) :
    (A.map (·.liftN k)).map (VExpr.liftN m · c) = A.map (·.liftN (k + m)) := by
  rw [List.map_map]
  exact List.map_congr_left fun a _ =>
    VExpr.liftN'_liftN' (Nat.zero_le _) (by simpa using h)

/-- Instantiating a saturated spine of `ni` arguments away, entrywise on the stored block:
`map_instAll_bvars_ge`'s counterpart, and the entrywise form of
`VExpr.instAll_liftN_of_le` (`Theory/Inductive/Nested.lean`, the "down payment"). -/
theorem map_instAll_map_liftN {A ιs : List VExpr} {k ni : Nat}
    (hlen : ιs.length = ni) (h : ni ≤ k) :
    (A.map (·.liftN k)).map (VExpr.instAll · ιs 0) = A.map (·.liftN (k - ni)) := by
  rw [List.map_map]
  exact List.map_congr_left fun a _ => VExpr.instAll_liftN_of_le hlen h

/-- **The head under lifting.**  `liftN_atRec_tyApp`/`shift_atRec_tyApp`'s move, at a stored
parameter block: the block slides up by `m`, the arguments are lifted as they stand. -/
theorem liftN_tyAppH {n : Name} {ls : List VLevel} {A args : List VExpr} {k m c : Nat}
    (h : c ≤ k) :
    (tyAppH n ls A k args).liftN m c
      = tyAppH n ls A (k + m) (args.map (VExpr.liftN m · c)) := by
  rw [tyAppH, tyAppH, VExpr.liftN_mkApp, List.map_append, map_liftN_map_liftN h]
  rfl

/-- **The head under a saturated instantiation.**  `tyApp'_instAll`'s move, at a stored
parameter block: the block slides *down* by `ni`, the arguments are instantiated. -/
theorem instAll_tyAppH {n : Name} {ls : List VLevel} {A ιs args : List VExpr} {k ni : Nat}
    (hlen : ιs.length = ni) (h : ni ≤ k) :
    VExpr.instAll (tyAppH n ls A k args) ιs 0
      = tyAppH n ls A (k - ni) (args.map (VExpr.instAll · ιs 0)) := by
  rw [tyAppH, tyAppH, VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append,
    map_instAll_map_liftN hlen h]

/-- **The head under `atRec`.**  Moving a stored block from the block's own universe
numbering into the recursor's commutes with the weakening, so `atRec` distributes entrywise
and the head generalisation costs nothing here either. -/
theorem atRec_tyAppH (D : VInductDecl') {n : Name} {ls : List VLevel} {A args : List VExpr}
    {k : Nat} :
    D.atRec (tyAppH n ls A k args)
      = tyAppH n (ls.map (·.inst D.selfLvls)) (D.atRecTele A) k (D.atRecTele args) := by
  simp only [tyAppH, VInductDecl'.atRec, VInductDecl'.atRecTele, VExpr.instL_mkApp,
    List.map_append, List.map_map, Function.comp_def, VExpr.instL_liftN, VExpr.instL]

end VInductDecl'

/-! ## Part 10: G4 — a fourth guard, unnamed until now: **the ι-rules are not renamed**

`VEnv.addInductC` (`Theory/Inductive/Companion.lean`) is

```lean
def VEnv.addInductC (env) (D) (K) (rn) : Option VEnv :=
  (env.addConstList (D.allConstsC K rn)).map (·.addIndRules D)
```

The renaming `rn` reaches `recConstsC` — the recursor *constants* — and stops there.
`VEnv.addIndRules` takes no renaming, and `VInductDecl'.iotaLhs` and
`VInductDecl'.ihValues` both hard-code the head

```lean
VExpr.const (Lean.mkRecName (D.types.getD j default).name) (VLevel.params D.recUvars)
```

So a companion block **declares** its recursor as `rn (mkRecName J)` and **emits its ι-rules
under `mkRecName J`** — a constant it did not declare, and which for a companion is the
already-declared recursor of the block that owns `J`.

Two consequences, and neither is addressed by G1, G2, G2a or G3:

1. *The companion's own recursor gets no computation rule.*  `rn (mkRecName J)` is declared
   at `D.recType j` and never appears on the left of a defeq, so it is an eliminator that
   does not reduce.  That is not unsound, but it is not the nested path either: the whole
   point of `Foo.rec_1` is that it computes.
2. *This block's minor premises are attached to another block's recursor.*  `iotaRules`
   ranges over `ctorsAll`, which includes the companion members, so a companion with
   constructors emits rules keyed `[mkRecName J, C.name]` whose left-hand sides carry **this**
   block's motive and minor telescopes (`D.nm` motives, `D.nmin` minors), not `J`'s.  Those
   are new equations about `J.rec`.

The second is the dangerous one and it is *not* stopped by resolution: resolution fixes which
constructors a companion has, not which recursor its rules are keyed on.  It should be caught
downstream — the rule's left-hand side is ill-typed against `J.rec`'s declared type whenever
the two blocks differ in motive count, so `VDefEq.WF` fails — but the abstract extension
`addInductC` performs no such check, and `Companion.lean`'s guard list does not mention it.

**The repair is not a check.**  `rn` has to be threaded through `iotaLhs`, `ihValues` and
hence `iotaRule`, exactly as it is threaded through `recConstsC`.  That is a `Decl.lean`
change (or a companion-aware copy of those three definitions), and it belongs with the head
generalisation of Part 9, since both edit the same constructions.

Stated below is the machine-checked core: the key of an ι-rule is the *un-renamed* recursor
name, so under any renaming that actually renames, no rule of `D.iotaRules` is a rule of the
recursor the block declared. -/

/-- **G4.**  An ι-rule's key names the un-renamed recursor, so it is never a rule of the
renamed one. -/
theorem VInductDecl'.key_iotaRule_ne_renamed (D : VInductDecl') (j q : Nat) (C : VIndCtor)
    {rn : Name → Name}
    (hrn : rn (Lean.mkRecName (D.types.getD j default).name)
      ≠ Lean.mkRecName (D.types.getD j default).name) :
    (D.iotaRule j q C).key
      ≠ [rn (Lean.mkRecName (D.types.getD j default).name), C.name] := by
  rw [D.key_iotaRule j q C]
  intro h
  simp only [List.cons.injEq] at h
  exact hrn h.1.symm

namespace InductiveDeclExamples

/-- The nested path's renaming really does rename: `mkAuxRecNameMap` sends `Foo.rec` to
`Foo.rec_1`.  So G4's hypothesis is met at the witness, and `fooCompRec` is not a
degenerate instance of the renaming parameter. -/
theorem fooCompRec_ne_mkRecName : fooCompRec (Lean.mkRecName `Foo) ≠ Lean.mkRecName `Foo := by
  decide

/-- G4 at the witness: the ι-rule `addInductC` would emit is keyed on `Foo.rec`, the
recursor the *original* block declared — not on `Foo.rec_1`, the one the companion
declares. -/
theorem fooComp_iotaRule_misheaded (q : Nat) (C : VIndCtor) :
    (fooDecl.iotaRule 0 q C).key ≠ [fooCompRec (Lean.mkRecName `Foo), C.name] :=
  fooDecl.key_iotaRule_ne_renamed 0 q C fooCompRec_ne_mkRecName

end InductiveDeclExamples

end Lean4Lean
