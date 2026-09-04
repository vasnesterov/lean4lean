import Lean4Lean.Verify.Inductive.TrIndDeclNProducer
import Lean4Lean.Verify.Inductive.NestedRunInvariant
import Lean4Lean.Verify.Inductive.NestedRestoreWit

/-!
# The pointwise constructor correspondence — and why it does *not* supply `TrIndDeclN.trCtorsLen`

This file was commissioned to unblock `TrIndDeclN.trCtorsLen`
(`Verify/Environment/InductR.lean`) by strengthening
`ElimNestedInductive.Result.RestoreData.ctor` (`Verify/Inductive/NestedRestore.lean`) from its
existential form

```
ctor : … → ∀ C ∈ T.ctors, ∃ c ∈ t.ctors, c.name = C.name
```

to a pointwise one, on the expectation that a length equation would fall out.  **The
strengthening is real and is proved here (§2).  The expectation is backwards**, and §3 proves
that machine-checked rather than asserting it.

## The dependency runs the other way

`Verify/Inductive/TrIndDeclNCtorOwn.lean`'s `Result.ctor_prefix_of_run` already derives
`RestoreData.ctor`'s prefix half *from* a `TrIndDeclN`, and its proof uses `htr.trCtorsLen` by
name to turn `C ∈ T.ctors` into an index into the checker's constructor list.  So `trCtorsLen`
is **upstream** of `RestoreData.ctor`.  Deriving `trCtorsLen` from `ctor` — pointwise or not —
would re-close the cycle `docs/vacuity-ledger.md` rows 80a/91c are about, with `trCtorsLen` as
the repeated edge instead of `OwnId.ctorName`.

## …and it is not merely circular, it is impossible

§3 is the sharper statement.  Reading `RestoreData`'s fourteen fields off, the argument `types`
occurs in the bundle **only** through `types.length` and, via `auxRecName types k =
appendIndexAfter' (mkRecName (types.headD default).name) (k+1)`, through
`(types.headD default).name`.  It never occurs as `types[j].ctors`.  So the bundle cannot
distinguish two blocks that differ only in how many constructors a member has — while
`trCtorsLen` is *exactly* a statement about that number.  `RestoreData.congr_types` (§3.1) is
that invariance, and `trCtorsLen_not_of_restoreData` (§3.2) is the refutation it yields: no
theorem of the form `RestoreData … → trCtorsLen` exists, so no strengthening of `ctor` can be
the missing lemma.

## Where the index-wise structure actually is

Not in `mkRestore`.  It is in `ElimNestedInductive.nameSkel`: `run` extends the *name skeleton*
of the block it was handed (`RunSkelExtends`, proved), and `run_prefix` reads off
`t.ctors.map (·.name) = u.ctors.map (·.name)` on the prefix — a `map` equation, hence index-wise
and length-preserving by construction.  §1 restates that entrywise step over the skeleton
equation alone, with no `run` in it, which is what lets §4's witness exist without a proved
`run`-success (there is none in the tree at any block: `TrIndDeclNCtorOwn.lean` §2 rows C4/C6
record that the `run`-success equation is `#eval`-witnessed only).

## What `trCtorsLen`'s supplier actually is

`trCtorsLen` relates the *user's* `types[j].ctors` to the abstract `D.types[j].ctors`.  Nothing
that speaks only about the checker's `Result` can see the left-hand side and nothing that speaks
only about `D` can see it either: it is a clause of *the translation*, and its supplier is
whatever constructs `D` from `types`.  The tree has no such construction — `TrIndDecl` and
`TrIndDeclN` are both concluded only by arity-0 concrete witnesses plus the `numNested = 0`
bridge `TrIndDecl.toN`, which consumes a `TrIndDecl`.  So `trCtorsLen` is not a cheap field
waiting on one lemma; it is the bookkeeping component of the same missing construction that owes
`trType` and `trCtors`, and it is cheap only *relative to them*, once that construction exists
and builds `D.types[j].ctors` by a `List.map` over `types[j].ctors`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## §1 The entrywise step, over the skeleton equation alone

`ElimNestedInductive.run_prefix` proves this for the particular skeleton equation that
`runSkelExtends` supplies.  Its body never uses `run`, so the general form costs nothing and is
what §2 and §4 are stated over. -/

namespace ElimNestedInductive

/-- **`run_prefix`'s content, with `run` abstracted away.**  If one block's name skeleton extends
another's, then on the prefix the members agree on their name *and on their constructors' names,
in order*. -/
theorem nameSkel_prefix {types rtypes : List InductiveType}
    {tail : List (Name × List Name)} (ht : nameSkel rtypes = nameSkel types ++ tail) :
    ∀ (j : Nat) (t : InductiveType), rtypes[j]? = some t → j < types.length →
      ∃ u, types[j]? = some u ∧ t.name = u.name ∧
        t.ctors.map (·.name) = u.ctors.map (·.name) := by
  intro j t hjt hj
  have h1 : (nameSkel rtypes)[j]? = some (t.name, t.ctors.map (·.name)) := by
    rw [nameSkel, List.getElem?_map, hjt]; rfl
  rw [ht, List.getElem?_append_left (by rwa [nameSkel, List.length_map])] at h1
  rw [nameSkel, List.getElem?_map] at h1
  cases hu : types[j]? with
  | none => rw [hu] at h1; exact absurd h1 nofun
  | some u =>
    rw [hu] at h1
    have h2 := Option.some.injEq .. ▸ h1
    refine ⟨u, rfl, ?_, ?_⟩
    · exact ((Prod.mk.injEq .. ▸ h2).1 : u.name = t.name).symm
    · exact ((Prod.mk.injEq .. ▸ h2).2 :
        List.map (·.name) u.ctors = List.map (·.name) t.ctors).symm

/-- `run_prefix` is the `run` instance of `nameSkel_prefix`; recorded so the abstraction is
visibly a generalisation and not a second proof. -/
theorem nameSkel_prefix_covers_run {cenv : Environment} {fuel np : Nat}
    {types : List InductiveType} {s : State} {r : Result} {s' : State}
    (hs : s.newTypes.toList = types) (h : run fuel np types cenv s = .ok (r, s')) :
    ∃ tail, nameSkel r.types = nameSkel types ++ tail := by
  obtain ⟨tail, ht⟩ := runSkelExtends cenv fuel np types s r s' h
  exact ⟨tail, by rwa [hs] at ht⟩

end ElimNestedInductive

/-- A `map (·.name)` equation is index-wise. -/
theorem getElem?_name_of_map_eq {l l' : List Constructor}
    (h : l.map (·.name) = l'.map (·.name)) {q : Nat} {c c' : Constructor}
    (hc : l[q]? = some c) (hc' : l'[q]? = some c') : c.name = c'.name := by
  have h2 := congrArg (fun m => m[q]?) h
  simp only [List.getElem?_map, hc, hc', Option.map_some] at h2
  exact Option.some.inj h2

/-! ## §2 The pointwise strengthening

Both halves the brief asked for — a **length equation** and an **index-wise name
correspondence** — between the checker's output member and `D`'s member, on the prefix.  This
strictly strengthens `Result.ctor_prefix_of_run`, whose conclusion is the existential
`∀ C ∈ T.ctors, ∃ c ∈ t.ctors, c.name = C.name`; §2.2 derives that from this. -/

/-- **THE POINTWISE CONSTRUCTOR CORRESPONDENCE.**  On the prefix, the checker's output member and
`D`'s member have the *same number* of constructors, and their names agree *at every index*.

Hypotheses: a `TrIndDeclN` (for `trCtorsLen` and `ctorName_own`) and a skeleton extension.  No
`VIndRestore` occurs in the proof, for the reason `TrIndDeclNCtorOwn.lean` §3 records: a
derivation through `OwnId.ctorName` would re-enter rows 80a/91c's cycle. -/
theorem trIndDeclN_ctorPointwise {env : VEnv} {Us : List Name} {npar nn : Nat} {iu : Bool}
    {types : List InductiveType} {D : VInductDecl'} {K : List Name} {R : VIndRestore}
    (htr : TrIndDeclN env Us npar types iu nn D K R)
    {rtypes : List InductiveType} {tail : List (Name × List Name)}
    (hskel : ElimNestedInductive.nameSkel rtypes = ElimNestedInductive.nameSkel types ++ tail)
    (j : Nat) (T : VIndType) (hT : D.types[j]? = some T) (t : InductiveType)
    (hjt : rtypes[j]? = some t) (hj : j < types.length) :
    t.ctors.length = T.ctors.length ∧
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → c.name = C.name := by
  obtain ⟨u, hu, -, hcs⟩ := ElimNestedInductive.nameSkel_prefix hskel j t hjt hj
  have hlen : t.ctors.length = u.ctors.length := by
    simpa using congrArg List.length hcs
  refine ⟨hlen.trans (htr.trCtorsLen j u T hu hT), fun q c C hc hC => ?_⟩
  have hq : q < u.ctors.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hc).1
  obtain ⟨c₀, hc₀⟩ := exists_getElem?_of_lt hq
  exact (getElem?_name_of_map_eq hcs hc hc₀).trans (htr.ctorName_own j u T hu hT q c₀ C hc₀ hC)

/-- …and the same at `run`, which is the shape `Result.ctor_prefix_of_run` is stated in. -/
theorem trIndDeclN_ctorPointwise_of_run {env : VEnv} {Us : List Name} {npar nn : Nat} {iu : Bool}
    {types : List InductiveType} {D : VInductDecl'} {K : List Name} {R : VIndRestore}
    {cenv : Environment} {fuel np : Nat} {s : ElimNestedInductive.State}
    {r : ElimNestedInductive.Result} {s' : ElimNestedInductive.State}
    (htr : TrIndDeclN env Us npar types iu nn D K R)
    (hs : s.newTypes.toList = types)
    (h : ElimNestedInductive.run fuel np types cenv s = .ok (r, s'))
    (j : Nat) (T : VIndType) (hT : D.types[j]? = some T) (t : InductiveType)
    (hjt : r.types[j]? = some t) (hj : j < types.length) :
    t.ctors.length = T.ctors.length ∧
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → c.name = C.name :=
  let ⟨_, hskel⟩ := ElimNestedInductive.nameSkel_prefix_covers_run hs h
  trIndDeclN_ctorPointwise htr hskel j T hT t hjt hj

/-- **The existential form is a consequence**, so §2 subsumes
`ElimNestedInductive.Result.ctor_prefix_of_run` rather than sitting beside it. -/
theorem trIndDeclN_ctor_exists {env : VEnv} {Us : List Name} {npar nn : Nat} {iu : Bool}
    {types : List InductiveType} {D : VInductDecl'} {K : List Name} {R : VIndRestore}
    (htr : TrIndDeclN env Us npar types iu nn D K R)
    {rtypes : List InductiveType} {tail : List (Name × List Name)}
    (hskel : ElimNestedInductive.nameSkel rtypes = ElimNestedInductive.nameSkel types ++ tail)
    (j : Nat) (T : VIndType) (hT : D.types[j]? = some T) (t : InductiveType)
    (hjt : rtypes[j]? = some t) (hj : j < types.length) :
    ∀ C ∈ T.ctors, ∃ c ∈ t.ctors, c.name = C.name := by
  obtain ⟨hlen, hname⟩ := trIndDeclN_ctorPointwise htr hskel j T hT t hjt hj
  intro C hC
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hC
  have hq' : q < t.ctors.length := by
    rw [hlen]; exact (List.getElem?_eq_some_iff.1 hq).1
  obtain ⟨c, hc⟩ := exists_getElem?_of_lt hq'
  exact ⟨c, List.mem_iff_getElem?.2 ⟨q, hc⟩, hname q c C hc hq⟩

/-! ## §3 `RestoreData` cannot supply `trCtorsLen`, and this is a refutation, not a difficulty

§3.1 is the invariance: the bundle sees `types` only through its length and its head member's
name.  §3.2 turns that into `¬ ∀ …`: there is no theorem `RestoreData … → trCtorsLen`, so the
commissioned route is closed, not merely unattractive. -/

namespace ElimNestedInductive.Result.RestoreData

variable {r : Result} {types types' : List InductiveType} {D : VInductDecl'} {K : List Name}
  {as : Nat → List VExpr}

/-- **THE INVARIANCE.**  `RestoreData` depends on `types` only through `types.length` and
`(types.headD default).name`.  In particular it is blind to `types[j].ctors`, for every `j` —
including `j = 0`, where the head member's *name* is read but its constructor list is not. -/
theorem congr_types (h : r.RestoreData types D K as)
    (hlen : types'.length = types.length)
    (hhead : (types'.headD default).name = (types.headD default).name) :
    r.RestoreData types' D K as :=
  have haux : ∀ k, auxRecName types' k = auxRecName types k := fun k => by
    simp only [auxRecName, hhead]
  { len := h.len
    name := h.name
    ctor := h.ctor
    companions := fun j T hT => by rw [hlen]; exact h.companions j T hT
    auxName := fun j t ht hle => h.auxName j t ht (hlen ▸ hle)
    auxCtorName := fun j t ht hle => h.auxCtorName j t ht (hlen ▸ hle)
    auxCtorPrefix := fun j t ht hle => h.auxCtorPrefix j t ht (hlen ▸ hle)
    auxNodup := by rw [hlen]; exact h.auxNodup
    ownName := fun j t ht hlt => h.ownName j t ht (hlen ▸ hlt)
    ownCtor := fun j t ht hlt => h.ownCtor j t ht (hlen ▸ hlt)
    head := fun j t ht hle => h.head j t ht (hlen ▸ hle)
    headNe := fun j t ht hle => h.headNe j t ht (hlen ▸ hle)
    auxRec := fun k => by rw [haux k]; exact h.auxRec k
    args := h.args }

end ElimNestedInductive.Result.RestoreData

/-- **THE REFUTATION.**  No theorem derives `TrIndDeclN.trCtorsLen`'s statement from a
`RestoreData` bundle — the commissioned route for this round.

Witness: `NestedWit.nfnResult_restoreData`, transported by §3.1 to a block whose single member
has its constructor list doubled.  Length and head name are unchanged, so the bundle survives;
the constructor count is not, so the conclusion would have to hold at both `1` and `2`.

Note what this does **not** say: it does not say the pointwise strengthening of §2 is useless
(it strictly strengthens `ctor_prefix_of_run`).  It says the strengthening cannot be *this*
field's supplier, whatever its form. -/
theorem trCtorsLen_not_of_restoreData :
    ¬ ∀ (r : ElimNestedInductive.Result) (types : List InductiveType) (D : VInductDecl')
        (K : List Name) (as : Nat → List VExpr), r.RestoreData types D K as →
      ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
        t.ctors.length = T.ctors.length := by
  intro H
  have hRD := NestedWit.nfnResult_restoreData.congr_types
    (types' := [{ NestedWit.nfnIndType with
      ctors := NestedWit.nfnIndType.ctors ++ NestedWit.nfnIndType.ctors }])
    rfl rfl
  have h2 := H _ _ _ _ _ hRD 0 _ (InductiveDeclExamples.nfnAux.types.getD 0 default) rfl rfl
  simp [NestedWit.nfnIndType, InductiveDeclExamples.nfnAux] at h2

/-! ## §4 Vacuity: an arity-0 witness at the parameterised nested block

`InductiveDeclExamples.ntreeAux` — `uvars = 1`, `params = [.sort (.succ (.param 0))]` —
deliberately **not** the degenerate `nfnAux` (`uvars = 0`, `params = []`).  The numeric conjuncts
are asserted inside the statement so the witness cannot silently drift to the degenerate block.

**Route.**  `trIndDeclN_ctorPointwise` (§2), a general theorem, applied to
`InductiveDeclExamples.ntreeAux_trIndDeclN`'s `TrIndDeclN` and to a skeleton extension.  Nothing
block-specific about *constructors* is re-derived: the conclusion is produced by §2, not by hand.

The `rtypes` here is junk data in the sense `NestedWit.nfnResult_restoreData_junk` is — a
skeleton extension is all §2 reads, and no `run`-success is available at any block to supply a
real one (`TrIndDeclNCtorOwn.lean` §2, rows C4/C6).  The `tail ≠ []` conjunct keeps the witness
off the trivial `rtypes = types` case, where the skeleton equation is `rfl` for a different
reason. -/

namespace InductiveDeclExamples

/-- A junk companion member, present only so §4's skeleton extension has a non-empty tail. -/
def ctorPointwiseJunkAux : InductiveType :=
  { name := `_nested.CtorPointwise_1, type := .sort .zero, ctors := [] }

/-- **THE POINTWISE CORRESPONDENCE AT `ntreeAux`, THROUGH §2, ARITY 0.** -/
theorem ntreeAux_ctorPointwise :
    ∃ (env₁ : VEnv) (rtypes : List InductiveType) (tail : List (Name × List Name)),
      VEnv.empty.addInduct' listDecl = some env₁ ∧
      ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
      rtypes.length = 2 ∧ tail ≠ [] ∧
      ElimNestedInductive.nameSkel rtypes
        = ElimNestedInductive.nameSkel [ntreeIndType] ++ tail ∧
      ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → ∀ t, rtypes[j]? = some t →
        j < [ntreeIndType].length →
        t.ctors.length = T.ctors.length ∧
          ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → c.name = C.name := by
  obtain ⟨env₁, hadd, huv, hpar, htr⟩ := ntreeAux_trIndDeclN
  refine ⟨env₁, [ntreeIndType, ctorPointwiseJunkAux],
    ElimNestedInductive.nameSkel [ctorPointwiseJunkAux],
    hadd, huv, hpar, rfl, by decide, rfl, fun j T hT t hjt hj => ?_⟩
  exact trIndDeclN_ctorPointwise htr rfl j T hT t hjt hj

end InductiveDeclExamples

#print axioms Lean4Lean.trIndDeclN_ctorPointwise
#print axioms Lean4Lean.trCtorsLen_not_of_restoreData
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_ctorPointwise

end Lean4Lean
