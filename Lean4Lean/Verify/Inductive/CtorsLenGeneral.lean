import Lean4Lean.Verify.Environment.InductR

/-!
# `TrIndDeclN.trCtorsLen`, in general — the name-skeleton prefix supplies it

`Verify/Environment/InductR.lean`'s `TrIndDeclN` has twelve fields.  Eleven of them are either
block data or have a general producer (`Verify/Inductive/TrIndDeclNProducer.lean`'s
`trIndDeclN_of_ownId`).  The twelfth, `trCtorsLen`, is

```
∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → t.ctors.length = T.ctors.length
```

— a bare length equation between the **user's** `List Constructor` and the **abstract**
`VIndType.ctors`, unstaged (no `addIndTypesC` premise, unlike `trCtors`).  Every instance in the
tree is a concrete-block `intro; cases; rfl`: `Verify/Environment/Induct.lean` (the `Eq` block),
`Verify/Inductive/AddDeclWF.lean` (`R10.Wit.trIndDecl_wit`),
`Verify/Inductive/StagesFiring.lean` (which reuses it) and `Verify/Inductive/NestedRestoreWit.lean`
(`trIndDeclN_wit'` at the **degenerate** `nfnAux`, `uvars = 0`, `params = []`).
`trIndDeclN_of_ownId` carries it as its hypothesis `hclen` and says so in a comment.

## What can supply it, and what provably cannot

* **Not `RestoreData`.**  `Verify/Inductive/CtorPointwise.lean` §3's
  `Lean4Lean.trCtorsLen_not_of_restoreData` refutes that outright: the bundle sees `types` only
  through `types.length` and `(types.headD default).name`.
* **Not the rest of the relation.**  §3 below is the sharper statement, and it is new here:
  `trCtorsLen` is **independent of the other eleven fields**.  Nothing among them constrains how
  many constructors a member has, because `trCtors` and `ctorName_own` quantify over indices at
  which *both* lists are `some`, and `TrIndType` (`Verify/Environment/Induct.lean:86`) is
  `t.name = T.name ∧ TrExprS env Us [] t.type T.type` — it never mentions `ctors`.  So no
  strengthening of the other eleven can be the missing lemma either.
* **Only the surface→abstract construction.**  There is no
  `List InductiveType → VInductDecl'`, no `InductiveType → VIndType` and no
  `Constructor → VIndCtor` in the tree: every `VInductDecl'` is a literal witness block, a record
  update of one, `VInductDecl'.resolveC`, or `VNestedOcc.member` — and the last two are
  abstract→abstract.  `trCtorsLen` is therefore the **fourth** field owed by that one absent
  construction, alongside `trType`, `trCtors` and the `trType` name half.

## What this file does about it

It does not invent the construction.  It reduces `trCtorsLen` to the **smallest sufficient
premise**, and proves the reduction is an equivalence, so nothing is lost:

* §1: `CtorNamesAgree` — the two sides' constructor *names* agree as lists — implies
  `trCtorsLen` by `List.length_map`, and **conversely** given `ctorName_own` (which
  `trIndDeclN_of_ownId` already produces generally).  So `CtorNamesAgree ↔ TrCtorsLen`.
* §2: `SkelPrefix` — the abstract block's **name skeleton extends the user's**,
  `D.nameSkelV = surfNameSkel types ++ tail`.  One `List` equation, and it supplies *three*
  things at once: `trCtorsLen`, `ctorName_own`, and `trType`'s name half.  It too is an
  equivalence, given the length bound.  `surfNameSkel`'s body is verbatim
  `ElimNestedInductive.nameSkel`'s (`Verify/Inductive/NestedRunInvariant.lean:217`) — that module
  is *deliberately not imported* here (see §4) — so a downstream file can chain `SkelPrefix` with
  the already-proved `runSkelExtends`/`nameSkel_prefix_covers_run` by `rfl`.
* §3: the independence refutation described above.
* §4: **the arity-0 witness at `ntreeAux`**, the parameterised nested block
  (`uvars = 1`, `params = [Type u]`, `numNested = 1`), reached through §2 and not by a `rfl` on
  the field's text.

## Structural exclusions

This file imports **only** `Lean4Lean.Verify.Environment.InductR` (142-module closure).  That
closure **excludes** every module holding a hand-built `trCtorsLen`, except the one that declares
the structure:

* excluded: `Lean4Lean.Verify.Inductive.NestedRestoreWit` (the degenerate `nfnAux` `TrIndDeclN`),
  `Lean4Lean.Verify.Inductive.AddDeclWF`, `Lean4Lean.Verify.Inductive.StagesFiring`,
  `Lean4Lean.Verify.Inductive.CtorPointwise`, `Lean4Lean.Verify.Inductive.TrIndDeclNProducer`,
  `Lean4Lean.Verify.Inductive.TrExprSGeneral`, `Lean4Lean.Verify.Inductive.ValAtParam`,
  `Lean4Lean.Verify.Inductive.NestedRunInvariant`.
* **not** excluded, and disclosed: `Lean4Lean.Verify.Environment.Induct`, which declares
  `TrIndDecl` and so cannot be dropped; its hand-built instance is at the `Eq` block, a different
  relation and a different block from §4's.

Because `ValAtParam` is excluded, §4 restates the user's `NTree` block here as `ntreeSurf`, using
the same `exprOf%` splice of Lean's own stored types as `ntreeIndType` does — the two are the same
term.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 The premise `CtorNamesAgree`, and that it is equivalent to the field -/

/-- **`TrIndDeclN.trCtorsLen`'s text**, named so the reductions below can be stated about it and
so a consumer can see which theorem discharges which field. -/
def TrCtorsLen (types : List InductiveType) (D : VInductDecl') : Prop :=
  ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    t.ctors.length = T.ctors.length

/-- **`TrIndDeclN.ctorName_own`'s text**, likewise.  This one already has a general producer:
`trIndDeclN_of_ownId` derives it from `VIndRestore.OwnId.ctorName` plus its `hctr`. -/
def CtorNameOwn (types : List InductiveType) (D : VInductDecl') : Prop :=
  ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → c.name = C.name

/-- The reduction target: on the user's members the two sides' constructor **names agree as
lists**.  A `List` equation, hence index-wise and length-preserving — the shape any
`List InductiveType → VInductDecl'` construction produces by definition. -/
def CtorNamesAgree (types : List InductiveType) (D : VInductDecl') : Prop :=
  ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    t.ctors.map (·.name) = T.ctors.map (·.name)

/-- `TrIndDeclN` gives the field, as expected; recorded so the direction is visible. -/
theorem TrIndDeclN.toTrCtorsLen {env : VEnv} {Us : List Name} {np nn : Nat} {iu : Bool}
    {types : List InductiveType} {D : VInductDecl'} {K : List Name} {R : VIndRestore}
    (h : TrIndDeclN env Us np types iu nn D K R) : TrCtorsLen types D := h.trCtorsLen

/-- …and `ctorName_own`. -/
theorem TrIndDeclN.toCtorNameOwn {env : VEnv} {Us : List Name} {np nn : Nat} {iu : Bool}
    {types : List InductiveType} {D : VInductDecl'} {K : List Name} {R : VIndRestore}
    (h : TrIndDeclN env Us np types iu nn D K R) : CtorNameOwn types D := h.ctorName_own

/-- **The reduction.**  A name-list equation supplies the length equation. -/
theorem trCtorsLen_of_ctorNamesAgree {types : List InductiveType} {D : VInductDecl'}
    (h : CtorNamesAgree types D) : TrCtorsLen types D := by
  intro j t T ht hT
  simpa using congrArg List.length (h j t T ht hT)

/-- **…and the converse, given `ctorName_own`.**  So `CtorNamesAgree` is not a strengthening
that costs anything: at any block where the relation's `ctorName_own` holds, it *is* the field. -/
theorem ctorNamesAgree_of_trCtorsLen {types : List InductiveType} {D : VInductDecl'}
    (hown : CtorNameOwn types D) (hlen : TrCtorsLen types D) : CtorNamesAgree types D := by
  intro j t T ht hT
  refine List.ext_getElem? fun q => ?_
  simp only [List.getElem?_map]
  cases hc : t.ctors[q]? with
  | none =>
    have hq : ¬ q < t.ctors.length := fun h => by
      obtain ⟨c, hc'⟩ := exists_getElem?_of_lt h; rw [hc'] at hc; exact absurd hc nofun
    have : T.ctors[q]? = none := by
      rw [List.getElem?_eq_none_iff]
      rw [← hlen j t T ht hT]; exact Nat.le_of_not_lt hq
    rw [this]; rfl
  | some c =>
    have hq : q < t.ctors.length := (List.getElem?_eq_some_iff.1 hc).1
    obtain ⟨C, hC⟩ := exists_getElem?_of_lt (hlen j t T ht hT ▸ hq)
    rw [hC]
    exact congrArg some (hown j t T ht hT q c C hc hC)

/-- **§1's headline: the reduction is an equivalence.** -/
theorem ctorNamesAgree_iff_trCtorsLen {types : List InductiveType} {D : VInductDecl'}
    (hown : CtorNameOwn types D) : CtorNamesAgree types D ↔ TrCtorsLen types D :=
  ⟨trCtorsLen_of_ctorNamesAgree, ctorNamesAgree_of_trCtorsLen hown⟩

/-! ## §2 The name-skeleton prefix: one `List` equation for three fields

`surfNameSkel` is `ElimNestedInductive.nameSkel`'s body verbatim
(`Verify/Inductive/NestedRunInvariant.lean:217`), restated because that module is excluded from
this file's import closure on purpose; the two are the same term, so
`ElimNestedInductive.runSkelExtends`'s conclusion is `SkelPrefix`'s right-hand side by `rfl`. -/

/-- The names a *surface* block presents: one member name and its constructor names, per member. -/
def surfNameSkel (l : List InductiveType) : List (Name × List Name) :=
  l.map fun t => (t.name, t.ctors.map (·.name))

/-- The same for a `VInductDecl'`.  This is the only new *definition* the reduction needs: it is
the abstract side of the skeleton, which nothing in the tree had. -/
def VInductDecl'.nameSkelV (D : VInductDecl') : List (Name × List Name) :=
  D.types.map fun T => (T.name, T.ctors.map (·.name))

/-- **The premise: the abstract block's name skeleton extends the user's.**  Left-to-right this
is exactly "`D` was built from `types`, with `numNested` members appended", stated at the level of
*names only* — which is the weakest form of "built from" that still pins constructor counts. -/
def SkelPrefix (types : List InductiveType) (D : VInductDecl') : Prop :=
  ∃ tail, D.nameSkelV = surfNameSkel types ++ tail

/-- A list is a prefix of another as soon as it is no longer and agrees at every index of its
own.  Stated here rather than found, so §2 costs no search. -/
private theorem exists_append_of_getElem?_eq {α} {l₁ : List α} :
    ∀ {l₂ : List α}, l₁.length ≤ l₂.length →
      (∀ q, q < l₁.length → l₁[q]? = l₂[q]?) → ∃ tail, l₂ = l₁ ++ tail := by
  induction l₁ with
  | nil => exact fun {l₂} _ _ => ⟨l₂, rfl⟩
  | cons a l₁ ih =>
    intro l₂ hlen h
    match l₂ with
    | [] => exact absurd hlen (by simp)
    | b :: l₂ =>
      have hab : a = b := by
        have := h 0 (by simp); simp only [List.getElem?_cons_zero] at this
        exact Option.some.inj this
      obtain ⟨tail, ht⟩ := ih (l₂ := l₂) (by simpa using hlen) fun q hq => by
        have := h (q + 1) (by simpa using hq); simpa using this
      exact ⟨tail, by rw [ht, hab]; rfl⟩

/-- **What the skeleton prefix says at one member.**  Both halves at once: the member names
agree, and the constructor name lists agree. -/
theorem skelPrefix_entry {types : List InductiveType} {D : VInductDecl'}
    (h : SkelPrefix types D) {j : Nat} {t : InductiveType} {T : VIndType}
    (ht : types[j]? = some t) (hT : D.types[j]? = some T) :
    t.name = T.name ∧ t.ctors.map (·.name) = T.ctors.map (·.name) := by
  obtain ⟨tail, htl⟩ := h
  have hA : (surfNameSkel types)[j]? = some (t.name, t.ctors.map (·.name)) := by
    rw [surfNameSkel, List.getElem?_map, ht]; rfl
  have hB : D.nameSkelV[j]? = some (T.name, T.ctors.map (·.name)) := by
    rw [VInductDecl'.nameSkelV, List.getElem?_map, hT]; rfl
  have hj : j < (surfNameSkel types).length := by
    rw [surfNameSkel, List.length_map]; exact (List.getElem?_eq_some_iff.1 ht).1
  rw [htl, List.getElem?_append_left hj, hA] at hB
  have h2 := Option.some.inj hB
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-- The skeleton prefix supplies `CtorNamesAgree`… -/
theorem ctorNamesAgree_of_skelPrefix {types : List InductiveType} {D : VInductDecl'}
    (h : SkelPrefix types D) : CtorNamesAgree types D :=
  fun _ _ _ ht hT => (skelPrefix_entry h ht hT).2

/-- **…hence `trCtorsLen`, which is what this round was for.** -/
theorem trCtorsLen_of_skelPrefix {types : List InductiveType} {D : VInductDecl'}
    (h : SkelPrefix types D) : TrCtorsLen types D :=
  trCtorsLen_of_ctorNamesAgree (ctorNamesAgree_of_skelPrefix h)

/-- …and `ctorName_own`, for free. -/
theorem ctorNameOwn_of_skelPrefix {types : List InductiveType} {D : VInductDecl'}
    (h : SkelPrefix types D) : CtorNameOwn types D := by
  intro j t T ht hT q c C hc hC
  have h2 := congrArg (fun l => l[q]?) (skelPrefix_entry h ht hT).2
  simp only [List.getElem?_map, hc, hC, Option.map_some] at h2
  exact Option.some.inj h2

/-- …and `TrIndType`'s name half, for free. -/
theorem name_eq_of_skelPrefix {types : List InductiveType} {D : VInductDecl'}
    (h : SkelPrefix types D) {j : Nat} {t : InductiveType} {T : VIndType}
    (ht : types[j]? = some t) (hT : D.types[j]? = some T) : t.name = T.name :=
  (skelPrefix_entry h ht hT).1

/-- **§2's headline: the skeleton prefix is *equivalent* to `trCtorsLen`**, given the length
bound (`TrIndDeclN.length` gives it) and the two name facts that already have general producers
(`TrIndDeclN.trType`'s first component and `ctorName_own`).  So nothing is lost by asking the
absent construction for a skeleton equation instead of for the field. -/
theorem skelPrefix_iff_trCtorsLen {types : List InductiveType} {D : VInductDecl'}
    (hle : types.length ≤ D.types.length)
    (hname : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → t.name = T.name)
    (hown : CtorNameOwn types D) :
    SkelPrefix types D ↔ TrCtorsLen types D := by
  refine ⟨trCtorsLen_of_skelPrefix, fun hlen => ?_⟩
  have hagree := ctorNamesAgree_of_trCtorsLen hown hlen
  refine exists_append_of_getElem?_eq (by simpa [surfNameSkel, VInductDecl'.nameSkelV] using hle)
    fun q hq => ?_
  rw [surfNameSkel, List.length_map] at hq
  obtain ⟨t, ht⟩ := exists_getElem?_of_lt hq
  obtain ⟨T, hT⟩ := exists_getElem?_of_lt (Nat.lt_of_lt_of_le hq hle)
  rw [surfNameSkel, List.getElem?_map, ht, VInductDecl'.nameSkelV, List.getElem?_map, hT]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  exact ⟨hname q t T ht hT, hagree q t T ht hT⟩

/-! ## §3 `trCtorsLen` is independent of the other eleven fields

`Verify/Inductive/CtorPointwise.lean` §3 refuted the `RestoreData` route.  This is the stronger
statement, and it closes the *inside* of the relation: bundle the other eleven fields of
`TrIndDeclN` and there is still no derivation.  The reason is visible in the field texts —
`trCtors` and `ctorName_own` quantify over indices at which **both** constructor lists are `some`,
`TrIndType` never mentions `ctors`, and every other field sees `types` only through
`types.length`.  So the eleven are blind to a member's constructor count, and a one-member block
whose abstract member has *no* constructors satisfies all of them. -/

/-- **`TrIndDeclN` minus `trCtorsLen`**: the other eleven fields, copied verbatim from
`Verify/Environment/InductR.lean`. -/
structure TrIndDeclNSansLen (env : VEnv) (Us : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (numNested : Nat)
    (D : VInductDecl') (K : List Name) (R : VIndRestore) : Prop where
  safe : isUnsafe = false
  uvars : Us.length = D.uvars
  np : nparams = D.np
  length : D.types.length = types.length + numNested
  companions : ∀ (j : Nat) T, D.types[j]? = some T → (T.name ∈ K ↔ types.length ≤ j)
  trType : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T
  trCtors : ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → TrIndCtorR env₁ Us D R j c C
  trSpine : ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → types.length ≤ j →
      ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
        env₁.HasArgs D.uvars D.params.reverse
          (VExpr.splitPis (R.tyArgs j).length (ci.type.instL (R.tyLvls j))).1 (R.tyArgs j)
  ctorName_own : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → c.name = C.name
  recName_own : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    R.recName (Lean.mkRecName T.name) = Lean.mkRecName t.name
  recName_aux : ∀ (j : Nat) T, D.types[j]? = some T → types.length ≤ j →
    R.recName (Lean.mkRecName T.name) = auxRecName types (j - types.length)

/-- The bundle is a weakening, so a derivation from it would be a derivation from `TrIndDeclN`. -/
theorem TrIndDeclN.toSansLen {env : VEnv} {Us : List Name} {np nn : Nat} {iu : Bool}
    {types : List InductiveType} {D : VInductDecl'} {K : List Name} {R : VIndRestore}
    (h : TrIndDeclN env Us np types iu nn D K R) :
    TrIndDeclNSansLen env Us np types iu nn D K R where
  safe := h.safe
  uvars := h.uvars
  np := h.np
  length := h.length
  companions := h.companions
  trType := h.trType
  trCtors := h.trCtors
  trSpine := h.trSpine
  ctorName_own := h.ctorName_own
  recName_own := h.recName_own
  recName_aux := h.recName_aux

namespace CtorsLenJunk

/-- A one-member surface block with one constructor.  Only the counts matter: `trCtorsLen` reads
`ctors.length` and nothing else. -/
def surf : InductiveType where
  name := `_ctorsLenJunk
  type := .sort (.succ .zero)
  ctors := [{ name := `_ctorsLenJunk.mk, type := .sort .zero }]

/-- …and the abstract block that agrees with it on **everything except the constructor count**:
same name, same stored type, no companions, and an empty constructor list. -/
def D : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  types := [{ name := `_ctorsLenJunk, type := .sort (.succ .zero), indices := [], ctors := [] }]
  isLE := false

/-- **All eleven other fields hold**, at the empty environment, no universe parameters, no
companions, and the identity restoration. -/
theorem sansLen : TrIndDeclNSansLen VEnv.empty [] 0 [surf] false 0 D [] D.idRestore where
  safe := rfl
  uvars := rfl
  np := rfl
  length := rfl
  companions := by
    rintro (_ | j) T hT
    · cases hT; simp
    · simp only [D] at hT; exact absurd hT nofun
  trType := by
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; exact ⟨rfl, .sort rfl⟩
    · simp at ht
  trCtors := by
    rintro env₁ hst (_ | j) t T ht hT q c C hc hC
    · cases ht; cases hT; exact absurd hC nofun
    · simp at ht
  trSpine := by
    rintro env₁ hst (_ | j) T hT hj
    · exact absurd hj (by simp)
    · simp only [D] at hT; exact absurd hT nofun
  ctorName_own := by
    rintro (_ | j) t T ht hT q c C hc hC
    · cases ht; cases hT; exact absurd hC nofun
    · simp at ht
  recName_own := by
    rintro (_ | j) t T ht hT
    · cases ht; cases hT; rfl
    · simp at ht
  recName_aux := by
    rintro (_ | j) T hT hj
    · exact absurd hj (by simp)
    · simp only [D] at hT; exact absurd hT nofun

/-- …and the field fails: one constructor against none. -/
theorem not_trCtorsLen : ¬ TrCtorsLen [surf] D := by
  intro h
  exact absurd (h 0 surf _ rfl rfl) (by simp [surf])

end CtorsLenJunk

/-- **THE INDEPENDENCE REFUTATION.**  No theorem derives `trCtorsLen` from the other eleven
fields of `TrIndDeclN`, so the field is not waiting on a strengthening of the relation: it is
waiting on the surface→abstract construction.  Strictly stronger than
`Lean4Lean.trCtorsLen_not_of_restoreData` (`Verify/Inductive/CtorPointwise.lean` §3.2), which
closes the `RestoreData` route only. -/
theorem trCtorsLen_not_of_sansLen :
    ¬ ∀ (env : VEnv) (Us : List Name) (np : Nat) (types : List InductiveType) (iu : Bool)
        (nn : Nat) (D : VInductDecl') (K : List Name) (R : VIndRestore),
        TrIndDeclNSansLen env Us np types iu nn D K R → TrCtorsLen types D :=
  fun h => CtorsLenJunk.not_trCtorsLen
    (h _ _ _ _ _ _ _ _ _ CtorsLenJunk.sansLen)

/-! ## §4 The arity-0 witness at `ntreeAux`, through §2

`InductiveDeclExamples.ntreeAux` (`Theory/Inductive/NestedHead.lean`) is the parameterised nested
block: `inductive NTree (α : Type u) | node : α → List (NTree α) → NTree α` after nested
elimination, `uvars = 1`, `params = [Type u]`, `numNested = 1`, with the auxiliary member
`_nested.List_1` carrying two constructors.  It is **not** `nfnAux`, whose `uvars = 0` and
`params = []`.

`ntreeSurf` is the user's declaration as `Verify/Inductive/ValAtParam.lean`'s `ntreeIndType`
spells it — the same `exprOf%` splices of Lean's own stored types — restated because that module
is excluded from this file's closure (it would drag in `NestedRestoreWit`'s hand-built
`trIndDeclN_wit'`). -/

namespace InductiveDeclExamples

/-- The user's declaration, syntactically: `inductive NTree (α : Type u) | node : …`. -/
def ntreeSurf : InductiveType where
  name := ``NTree
  type := exprOf% NTree
  ctors := [{ name := ``NTree.node, type := exprOf% NTree.node }]

/-- **The premise, at this block.**  `ntreeAux`'s name skeleton is the user's followed by the one
auxiliary member — which is what "`ntreeAux` was produced from this declaration by nested
elimination" says at the level of names. -/
theorem ntreeSurf_skelPrefix : SkelPrefix [ntreeSurf] ntreeAux :=
  ⟨[(`_nested.List_1, [`_nested.List_1.nil, `_nested.List_1.cons])], rfl⟩

/-- **Negative control: the premise is not slack.**  Give the surface block a duplicated
constructor and the skeleton equation fails — so `ntreeSurf_skelPrefix` is doing the work that
`rfl` on the field's text would otherwise do by accident. -/
def ntreeSurfDbl : InductiveType :=
  { ntreeSurf with ctors := ntreeSurf.ctors ++ ntreeSurf.ctors }

theorem ntreeSurfDbl_not_skelPrefix : ¬ SkelPrefix [ntreeSurfDbl] ntreeAux := by
  rintro ⟨tail, h⟩
  have h0 := congrArg (fun l => l[0]?) h
  simp only [VInductDecl'.nameSkelV, surfNameSkel, ntreeAux, ntreeSurfDbl, ntreeSurf,
    List.map_cons, List.map_nil, List.cons_append, List.getElem?_cons_zero] at h0
  exact absurd h0 (by decide)

/-- **THE WITNESS — arity 0.**  `TrIndDeclN.trCtorsLen`'s text at the parameterised nested block,
reached through `trCtorsLen_of_skelPrefix` and **not** through a `rfl` on the field: the only
block-specific input is the name-skeleton equation, and §2 does the rest.  Beside it: the four
anti-`nfnAux` non-degeneracy facts, the two further fields the same premise supplies for free,
and an anti-vacuity conjunct naming the one index the clause bites at together with the fact that
the companion index is where it does not. -/
theorem ntreeAux_trCtorsLen_witness :
    -- non-degeneracy: this is not `nfnAux`
    ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
    ntreeAux.types.length = 2 ∧ ntreeNode.fields.length = 2 ∧
    -- the premise, which is a name-skeleton equation and not the field
    SkelPrefix [ntreeSurf] ntreeAux ∧
    -- THE FIELD, through §2
    TrCtorsLen [ntreeSurf] ntreeAux ∧
    -- the two further fields the same premise supplies
    CtorNameOwn [ntreeSurf] ntreeAux ∧
    (∀ (j : Nat) t T, ([ntreeSurf] : List InductiveType)[j]? = some t →
      ntreeAux.types[j]? = some T → t.name = T.name) ∧
    -- anti-vacuity: `j = 0` is a matching pair with a *nonzero* count on both sides, and the
    -- constructor whose name is compared is Lean's own `NTree.node`
    (∃ t T, ([ntreeSurf] : List InductiveType)[0]? = some t ∧ ntreeAux.types[0]? = some T ∧
      t.ctors.length = 1 ∧ T.ctors.length = 1 ∧
      t.ctors.map (·.name) = [``NTree.node] ∧ T.ctors = [ntreeNode]) ∧
    -- …and `j = 1` is exactly where it is vacuous: the companion has two constructors and no
    -- surface member, which is why `trCtorsLen` bites only on the user's block
    (([ntreeSurf] : List InductiveType)[1]? = none ∧
      ntreeAux.types[1]?.map (·.ctors.length) = some 2) := by
  refine ⟨rfl, rfl, rfl, rfl, ntreeSurf_skelPrefix,
    trCtorsLen_of_skelPrefix ntreeSurf_skelPrefix,
    ctorNameOwn_of_skelPrefix ntreeSurf_skelPrefix,
    fun _ _ _ ht hT => name_eq_of_skelPrefix ntreeSurf_skelPrefix ht hT,
    ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

end InductiveDeclExamples

end Lean4Lean
