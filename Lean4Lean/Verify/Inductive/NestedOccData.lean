import Lean4Lean.Verify.Inductive.NestedRestoreWit
import Lean4Lean.Verify.Inductive.NestedRunInvariant

/-!
# `OccResidue` reduced to its two semantic clauses

`Verify/Inductive/NestedRestoreWit.lean` §6 splits `VInductDecl'.Built` into four clauses the
fourteen-field `RestoreData` bundle discharges and four it cannot, collected as
`ElimNestedInductive.Result.OccResidue`:

| clause | what it says |
| --- | --- |
| `head` | the `Expr` `aux2nested` stores at an auxiliary member is headed by the member the occurrence is at |
| `ctorName_inv` | `restoreCtorName` inverts the auxiliary constructor naming |
| `member` | the companion member **is** the value `VNestedOcc.member` computes |
| `occurs` | the environment already holds the nested block |

**This file closes the first two, in general.**  They come from a six-field bundle `OccData`
of *name-and-head* facts about the checker's `Result` — every field a `Bool`-decidable statement
about `Lean.Name`s and one `Expr.getAppFn`, none of them mentioning `TrExprS`, `VEnv` or any
typing judgement — and from two pieces of general kit proved here:

* §1 the **`Name.replacePrefix` round trip**: `(c.replacePrefix p q).replacePrefix q p = c`
  whenever `p` really is a prefix of `c`, with **no side condition on `q`**.  The proof needs a
  component-count function, because the step that has to be ruled out is
  `q = .str (c.replacePrefix p q) s` — a name equal to a strict extension of itself.
* §2 `Expr.getAppFn` through the four operations `replaceIfNested` composes when it builds the
  stored `Expr`: `mkAppList`, `mkAppRange`, `abstract1` and `instantiate1'`.  So the shape
  `Add.lean:840,844` pushes — `replaceParams params (mkAppRange (.const J I_lvls) 0 I_nparams args) As` —
  has head `.const J I_lvls` **as a theorem** (§3.1), which is what makes `OccData.auxHead` a
  fact about the implementation rather than an assumption about it.

What is left of the residue is `SemResidue` (§5): `member` and `occurs`, and nothing else.
§6 bounds the split both ways at the `NFn`/`PFn` block:

* `nfnResult_occData` — `OccData` holds, so §4's two theorems are not vacuous;
* `nfnOccData_not_occurs` — `RestoreData ∧ OccData` at the *empty* environment still holds and
  `occurs` is false, so `occurs` is not slack;
* `nfnAuxPerturbed_*` — a one-`VExpr` perturbation of `D`'s companion member at which
  `RestoreData ∧ OccData` still hold and `member` is false, so `member` is not slack either.

§7 then re-derives `Built`, `Faithful`, `Canonical`, `AddNested` and `AddNestedStep` from
`RestoreData ∧ OccData ∧ SemResidue`.
-/

open Lean hiding Environment
open Kernel

namespace Lean4Lean

/-! ## 1. The `replacePrefix` round trip

`replaceIfNested` names an auxiliary constructor `J_ctor_name.replacePrefix J_name auxJ_name`
(`Lean4Lean/Inductive/Add.lean:855`) and `restoreCtorName` reads it back as
`c.replacePrefix auxI_name I` (`:698`).  `Built.ctorName_inv` is exactly the statement that the
second undoes the first.

`Name.replacePrefix` matches **outermost-first** — `if n == queryP then newP else …` before
recursing into the parent — so it fires at the unique element of `n`'s prefix chain equal to the
query.  That is why the round trip needs no hypothesis on the *replacement*: after
`c.replacePrefix p q` the chain of the result contains `q`, and `q` is the outermost chain element
equal to `q` because a name is never equal to a strict extension of itself.  `nameDepth` is what
turns "never" into a proof. -/

/-- The number of components of a name — `n.components.length`, without the intermediate list.
Used only to rule out `q = .str q' s` with `q` a chain prefix of `q'`. -/
def nameDepth : Name → Nat
  | .anonymous => 0
  | .str p _ => nameDepth p + 1
  | .num p _ => nameDepth p + 1

namespace Name

theorem isPrefixOf_self : ∀ n : Name, n.isPrefixOf n = true
  | .anonymous => rfl
  | .str .. => by rw [Lean.Name.isPrefixOf]; simp
  | .num .. => by rw [Lean.Name.isPrefixOf]; simp

/-- A prefix has no more components. -/
theorem nameDepth_le_of_isPrefixOf : ∀ {p n : Name}, p.isPrefixOf n = true →
    nameDepth p ≤ nameDepth n
  | p, .anonymous, h => by
    rw [Lean.Name.isPrefixOf] at h
    have : p = .anonymous := eq_of_beq h
    subst this; exact Nat.le_refl _
  | p, .str n' s, h => by
    rw [Lean.Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_trans (nameDepth_le_of_isPrefixOf h) (Nat.le_succ _)
  | p, .num n' i, h => by
    rw [Lean.Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_trans (nameDepth_le_of_isPrefixOf h) (Nat.le_succ _)

/-- **No name is a prefix of its own parent.**  The fact that makes the round trip
unconditional in `q`. -/
theorem not_isPrefixOf_str {r : Name} {s : String} : ¬ (Name.str r s).isPrefixOf r = true := by
  intro h
  have := nameDepth_le_of_isPrefixOf h
  simp [nameDepth] at this
  omega

theorem not_isPrefixOf_num {r : Name} {i : Nat} : ¬ (Name.num r i).isPrefixOf r = true := by
  intro h
  have := nameDepth_le_of_isPrefixOf h
  simp [nameDepth] at this
  omega

/-- `replacePrefix` at the whole name: the outermost test fires. -/
theorem replacePrefix_self : ∀ (n newP : Name), n.replacePrefix n newP = newP
  | .anonymous, _ => rfl
  | .str .., _ => by rw [Lean.Name.replacePrefix]; simp
  | .num .., _ => by rw [Lean.Name.replacePrefix]; simp

/-- After replacing the prefix `p` by `q`, `q` is a prefix of the result. -/
theorem isPrefixOf_replacePrefix : ∀ {n p q : Name}, p.isPrefixOf n = true →
    q.isPrefixOf (n.replacePrefix p q) = true
  | .anonymous, p, q, h => by
    rw [Lean.Name.isPrefixOf] at h
    have : p = .anonymous := eq_of_beq h
    subst this
    show q.isPrefixOf q = true
    exact isPrefixOf_self _
  | .str n' s, p, q, h => by
    rw [Lean.Name.replacePrefix]
    split
    · exact isPrefixOf_self _
    · rename_i hne
      rw [Lean.Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
      have h' := h.resolve_left fun h => hne (by simp [h])
      show (_ || _) = true
      rw [Bool.or_eq_true]
      exact .inr (isPrefixOf_replacePrefix h')
  | .num n' i, p, q, h => by
    rw [Lean.Name.replacePrefix]
    split
    · exact isPrefixOf_self _
    · rename_i hne
      rw [Lean.Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
      have h' := h.resolve_left fun h => hne (by simp [h])
      show (_ || _) = true
      rw [Bool.or_eq_true]
      exact .inr (isPrefixOf_replacePrefix h')

/-- **The round trip.**  `restoreCtorName` inverts `replaceIfNested`'s renaming whenever the
member's name really is a prefix of the constructor's — which is `RestoreData.auxCtorPrefix` on
the auxiliary side and `OccData.srcCtorPrefix` on the source side.

There is **no hypothesis on `q`**: the replacement may be anything, `.anonymous` included. -/
theorem replacePrefix_replacePrefix : ∀ {n p q : Name}, p.isPrefixOf n = true →
    (n.replacePrefix p q).replacePrefix q p = n
  | .anonymous, p, q, h => by
    rw [Lean.Name.isPrefixOf] at h
    have : p = .anonymous := eq_of_beq h
    subst this
    show Lean.Name.replacePrefix q q .anonymous = .anonymous
    exact replacePrefix_self ..
  | .str n' s, p, q, h => by
    rw [Lean.Name.replacePrefix]
    split
    · rename_i he
      rw [replacePrefix_self]; exact (eq_of_beq he).symm
    · rename_i hne
      rw [Lean.Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
      have h' := h.resolve_left fun h => hne (by simp [h])
      show (Lean.Name.str (n'.replacePrefix p q) s).replacePrefix q p = _
      rw [Lean.Name.replacePrefix]
      split
      · rename_i he
        have hpre := isPrefixOf_replacePrefix (n := n') (p := p) (q := q) h'
        have hq : Lean.Name.str (n'.replacePrefix p q) s = q := eq_of_beq he
        have hc : (Lean.Name.str (n'.replacePrefix p q) s).isPrefixOf
            (n'.replacePrefix p q) = true := by rw [hq]; exact hpre
        exact absurd hc not_isPrefixOf_str
      · show Lean.Name.mkStr _ s = _
        rw [replacePrefix_replacePrefix h']
  | .num n' i, p, q, h => by
    rw [Lean.Name.replacePrefix]
    split
    · rename_i he
      rw [replacePrefix_self]; exact (eq_of_beq he).symm
    · rename_i hne
      rw [Lean.Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
      have h' := h.resolve_left fun h => hne (by simp [h])
      show (Lean.Name.num (n'.replacePrefix p q) i).replacePrefix q p = _
      rw [Lean.Name.replacePrefix]
      split
      · rename_i he
        have hpre := isPrefixOf_replacePrefix (n := n') (p := p) (q := q) h'
        have hq : Lean.Name.num (n'.replacePrefix p q) i = q := eq_of_beq he
        have hc : (Lean.Name.num (n'.replacePrefix p q) i).isPrefixOf
            (n'.replacePrefix p q) = true := by rw [hq]; exact hpre
        exact absurd hc not_isPrefixOf_num
      · show Lean.Name.mkNum _ i = _
        rw [replacePrefix_replacePrefix h']

end Name



end Lean4Lean

/-! ## 2. `Expr.getAppFn` through the four operations that build the stored `Expr` -/

namespace Lean.Expr

@[simp] theorem getAppFn_app {f a : Expr} : (Expr.app f a).getAppFn = f.getAppFn := rfl

/-- The head of a spine is the head of its function. -/
@[simp] theorem getAppFn_mkAppList : ∀ (e : Expr) (l : List Expr),
    (mkAppList e l).getAppFn = e.getAppFn
  | _, [] => rfl
  | e, a :: l => by rw [mkAppList, getAppFn_mkAppList, getAppFn_app]

/-- **`getAppFn` of a `mkAppRange`.**  `replaceIfNested`'s `mkAppRange J 0 I_nparams args`
(`Add.lean:840`) is headed by `J`.  The two bounds are `replaceIfNested`'s own
`assert! I_nparams ≤ args.size`. -/
theorem getAppFn_mkAppRange {e : Expr} {i j : Nat} {args : Array Expr}
    (hij : i ≤ j) (hj : j ≤ args.size) : (mkAppRange e i j args).getAppFn = e.getAppFn := by
  have hL : args.toList.length = args.size := by simp
  rw [Expr.mkAppRange_eq (l₁ := args.toList.take i)
      (l₂ := (args.toList.drop i).take (j - i)) (l₃ := (args.toList.drop i).drop (j - i))
      (by rw [List.append_assoc, List.take_append_drop, List.take_append_drop])
      (by rw [List.length_take]; omega)
      (by rw [List.length_append, List.length_take, List.length_take, List.length_drop]; omega),
    getAppFn_mkAppList]

/-- `abstract1` never changes the head constant of a spine. -/
theorem getAppFn_abstract1 : ∀ (v : FVarId) (e : Expr) (k : Nat) (c : Name) (ls : List Level),
    e.getAppFn = .const c ls → (Expr.abstract1 v e k).getAppFn = .const c ls
  | v, .app f a, k, c, ls, h => by
    rw [show abstract1 v (.app f a) k = .app (abstract1 v f k) (abstract1 v a k) from rfl,
      getAppFn_app]
    exact getAppFn_abstract1 v f k c ls h
  | _, .const .., _, _, _, h => h
  | _, .bvar .., _, _, _, h => absurd h nofun
  | _, .fvar .., _, _, _, h => absurd h nofun
  | _, .mvar .., _, _, _, h => absurd h nofun
  | _, .sort .., _, _, _, h => absurd h nofun
  | _, .lam .., _, _, _, h => absurd h nofun
  | _, .forallE .., _, _, _, h => absurd h nofun
  | _, .letE .., _, _, _, h => absurd h nofun
  | _, .lit .., _, _, _, h => absurd h nofun
  | _, .mdata .., _, _, _, h => absurd h nofun
  | _, .proj .., _, _, _, h => absurd h nofun

/-- …and neither does `instantiate1'`. -/
theorem getAppFn_instantiate1' : ∀ (e a : Expr) (k : Nat) (c : Name) (ls : List Level),
    e.getAppFn = .const c ls → (Expr.instantiate1' e a k).getAppFn = .const c ls
  | .app f b, a, k, c, ls, h => by
    rw [show instantiate1' (.app f b) a k
        = .app (instantiate1' f a k) (instantiate1' b a k) from rfl, getAppFn_app]
    exact getAppFn_instantiate1' f a k c ls h
  | .const .., _, _, _, _, h => h
  | .bvar .., _, _, _, _, h => absurd h nofun
  | .fvar .., _, _, _, _, h => absurd h nofun
  | .mvar .., _, _, _, _, h => absurd h nofun
  | .sort .., _, _, _, _, h => absurd h nofun
  | .lam .., _, _, _, _, h => absurd h nofun
  | .forallE .., _, _, _, _, h => absurd h nofun
  | .letE .., _, _, _, _, h => absurd h nofun
  | .lit .., _, _, _, _, h => absurd h nofun
  | .mdata .., _, _, _, _, h => absurd h nofun
  | .proj .., _, _, _, _, h => absurd h nofun

theorem getAppFn_abstractList : ∀ (e : Expr) (vs : List FVarId) (k : Nat) (c : Name)
    (ls : List Level), e.getAppFn = .const c ls →
    (Expr.abstractList e vs k).getAppFn = .const c ls
  | _, [], _, _, _, h => h
  | e, v :: vs, k, c, ls, h => by
    rw [show abstractList e (v :: vs) k = abstractList (abstract1 v e k) vs k from rfl]
    exact getAppFn_abstractList _ vs k c ls (getAppFn_abstract1 v e k c ls h)

theorem getAppFn_instantiateRevList : ∀ (e : Expr) (as : List Expr) (k : Nat) (c : Name)
    (ls : List Level), e.getAppFn = .const c ls →
    (Expr.instantiateRevList e as k).getAppFn = .const c ls
  | _, [], _, _, _, h => h
  | e, a :: as, k, c, ls, h => by
    rw [show instantiateRevList e (a :: as) k
        = instantiate1' (instantiateRevList e as k) a k from rfl]
    exact getAppFn_instantiate1' _ a k c ls (getAppFn_instantiateRevList e as k c ls h)

end Lean.Expr

namespace Lean4Lean

/-! ## 3. `presentedHead` from the stored head

`Result.presentedHead` (`NestedRestore.lean` §5) is `restoreNested`'s
`nested'.withApp fun I …` as a total function; these two lemmas are the only interface `OccData`
needs to it. -/

namespace ElimNestedInductive.Result

/-- If the stored `Expr` is headed by `.const c ls`, `presentedHead` returns `c`. -/
theorem presentedHead_eq {r : Result} {n c : Name} {e : Expr} {ls : List Level}
    (he : r.aux2nested.lookup n = some e) (hfn : e.getAppFn = .const c ls) :
    r.presentedHead n = c := by
  rw [presentedHead, he]
  show (match e.getAppFn with | .const c _ => c | _ => n) = c
  rw [hfn]

/-- **§3.1: the shape `replaceIfNested` stores has the head it should.**  `Add.lean:840,844`
push `(replaceParams params (mkAppRange (.const J I_lvls) 0 I_nparams args) As, auxJ_name)` onto
`nestedAux`, and `replaceParams params e As = (e.abstract As).instantiateRev params`
(`Add.lean:779-781`).  Modulo the two frozen `Expr.abstract_eq`/`instantiateRev_eq` axioms —
which is how every other `abstract`/`instantiateRev` fact in `Verify/` is stated — this says the
stored `Expr`'s `getAppFn` is `.const J I_lvls`, so `OccData.auxHead` is a *consequence* of the
implementation's own shape, not an extra assumption about it.

Stated over the pure models `abstractList`/`instantiateRevList` so that no side condition is
needed here; the transfer to `Expr.abstract`/`Expr.instantiateRev` is the axiom pair. -/
theorem getAppFn_stored {J : Name} {I_lvls : List Level} {np n : Nat} {args : Array Expr}
    {vs : List FVarId} {params : List Expr} (hnp : np ≤ args.size) :
    (Expr.instantiateRevList
        (Expr.abstractList (mkAppRange (.const J I_lvls) 0 np args) vs n) params n).getAppFn
      = .const J I_lvls :=
  Expr.getAppFn_instantiateRevList _ _ _ _ _ <|
    Expr.getAppFn_abstractList _ _ _ _ _ <|
      Expr.getAppFn_mkAppRange (Nat.zero_le _) hnp

end ElimNestedInductive.Result

/-! ## 4. `OccData`, and the two clauses it closes

Six fields.  Read them against `replaceIfNested` (`Lean4Lean/Inductive/Add.lean:821-860`):
`auxName` and `auxCtors` are the lockstep between the `nestedAux.push` at `:845` and the
`newTypes.push` at `:857`; `auxHead` is the `Expr` half of that same push (§3.1); `ctorName` is
`:855` verbatim; `srcCtorPrefix` is the fact that makes `:855`'s `replacePrefix` a rename;
`ctorNodup` is the `Nodup` that makes `restoreCtorName`'s lookup find *its own* entry.

**None of the six mentions `TrExprS`, `VEnv`, or any typing judgement**, and all six are
`Bool`-decidable at a concrete block (§6). -/

namespace ElimNestedInductive.Result

/-- The name-level correspondence between the checker's `Result` and the abstract occurrences,
at the auxiliary tail. -/
structure OccData (r : Result) (types : List Lean.InductiveType) (occ : Nat → VNestedOcc) :
    Prop where
  /-- `nestedAux.push (JAs', auxJ_name)` and `newTypes.push {name := auxJ_name, …}` happen
  together (`Add.lean:845,857`), so the `j`-th auxiliary member of `r.types` carries the name
  the `j`-th occurrence invented. -/
  auxName : ∀ (j : Nat) t, r.types[j]? = some t → types.length ≤ j → (occ j).auxName = t.name
  /-- …and `aux2nested` stores at that name an `Expr` headed by the member the occurrence is at.
  `getAppFn_stored` (§3.1) is why this holds of what `replaceIfNested` pushes. -/
  auxHead : ∀ (j : Nat) t, r.types[j]? = some t → types.length ≤ j →
    ∃ e ls, r.aux2nested.lookup t.name = some e ∧ e.getAppFn = .const (occ j).tyName ls
  /-- `auxJ_ctor_name := J_ctor_name.replacePrefix J_name auxJ_name` (`Add.lean:855`).  Required
  only **on the source block's own constructors** — `VNestedOcc.ctorName` is a total function and
  need not be `replacePrefix` off them (`pfnOcc`'s is not). -/
  ctorName : ∀ (j : Nat), ∀ C ∈ (occ j).src.ctors,
    (occ j).ctorName C.name = C.name.replacePrefix (occ j).tyName (occ j).auxName
  /-- **`J`'s constructor names carry `J`'s own name as a prefix.**  Without it `:855`'s
  `replacePrefix` is the identity and the auxiliary constructor keeps the *source* block's name.
  Neither this kernel nor the C++ one checks it — see §6.1. -/
  srcCtorPrefix : ∀ (j : Nat), ∀ C ∈ (occ j).src.ctors,
    (occ j).tyName.isPrefixOf C.name = true
  /-- The auxiliary member's constructor list is the source block's, renamed. -/
  auxCtors : ∀ (j : Nat) t, r.types[j]? = some t → types.length ≤ j →
    ∀ C ∈ (occ j).src.ctors, ∃ c ∈ t.ctors, c.name = (occ j).ctorName C.name
  /-- **The auxiliary constructor names are pairwise distinct.**  `RestoreData.auxNodup` gives
  this for the auxiliary *member* names only, and that is not enough: two members whose names are
  prefixes of one another could otherwise name the same constructor, and `List.lookup` would
  return the wrong entry. -/
  ctorNodup : ((r.ctorRenames types.length).map (·.1)).Nodup

namespace OccData
variable {r : Result} {types : List Lean.InductiveType} {D : VInductDecl'} {K : List Name}
  {ls : Nat → List VLevel} {as : Nat → List VExpr} {occ : Nat → VNestedOcc}

/-- **`OccResidue.head`, in general.**  `RestoreData.companions` turns `T.name ∈ K` into
`types.length ≤ j`, and `auxHead` plus §3's `presentedHead_eq` do the rest. -/
theorem head (hd : r.OccData types occ) (h : r.RestoreData types D K as)
    (j : Nat) (T : VIndType) (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (t : Lean.InductiveType) (ht : r.types[j]? = some t) :
    r.presentedHead t.name = (occ j).tyName := by
  obtain ⟨e, lvls, he, hfn⟩ := hd.auxHead j t ht ((h.companions j T hT).1 hK)
  exact presentedHead_eq he hfn

/-- The entry of `ctorRenames` that an auxiliary constructor contributes. -/
theorem mem_ctorRenames {j : Nat} {t : Lean.InductiveType} {c : Lean.Constructor}
    (ht : r.types[j]? = some t) (hle : types.length ≤ j) (hc : c ∈ t.ctors) :
    (c.name, c.name.replacePrefix t.name (r.presentedHead t.name))
      ∈ r.ctorRenames types.length :=
  List.mem_flatMap.2 ⟨t, getElem?_mem_drop hle ht, List.mem_map.2 ⟨c, hc, rfl⟩⟩

/-- **`OccResidue.ctorName_inv`, in general.**  Three facts meet here: the round trip (§1), the
head (§4's `head`), and the `Nodup` that makes the lookup find the entry the auxiliary member
contributed rather than an earlier one. -/
theorem ctorName_inv (hd : r.OccData types occ) (h : r.RestoreData types D K as)
    (j : Nat) (T : VIndType) (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (C : VIndCtor) (hC : C ∈ (occ j).src.ctors) :
    (r.mkRestore types D.uvars D.np ls as).ctorName ((occ j).ctorName C.name) = C.name := by
  obtain ⟨t, ht, -, hle⟩ := h.on hT hK
  obtain ⟨c, hc, hcn⟩ := hd.auxCtors j t ht hle C hC
  have hhead : r.presentedHead t.name = (occ j).tyName := hd.head h j T hT hK t ht
  have haux : (occ j).auxName = t.name := hd.auxName j t ht hle
  have hcn' : c.name = C.name.replacePrefix (occ j).tyName t.name := by
    rw [hcn, hd.ctorName j C hC, haux]
  have hval : c.name.replacePrefix t.name (r.presentedHead t.name) = C.name := by
    rw [hhead, hcn']
    exact Name.replacePrefix_replacePrefix (hd.srcCtorPrefix j C hC)
  show ((r.ctorRenames types.length).lookup ((occ j).ctorName C.name)).getD _ = _
  rw [← hcn, List.lookup_eq_some_of_nodup hd.ctorNodup
    (hval ▸ mem_ctorRenames (types := types) ht hle hc)]
  rfl

end OccData
end ElimNestedInductive.Result

/-! ## 5. What is left: two clauses

`SemResidue` is `OccResidue` minus the two clauses §4 closes.  Both of its clauses are about
`env` and the *expression* content of `D`; neither is a name fact.

**A correction, measured.**  `member` has been described — in the handoff this file answers and
in `NestedRestoreWit.lean` §9 — as "the `TrExprS`-level agreement between `restoreNested`'s
output and `VIndCtor.typeR`".  It is not at that level.  `Built.member` is
`T = (occ j).member D.header R`, an equation between two `VIndType`s: `Lean.Name`, `VExpr`,
`List VExpr`, `List VIndCtor`.  The transitive constant cone of its *type* is 29 declarations and
contains no `TrExpr`, `TrExprS` or `Lean.Expr` at all — the same measurement that already
corrected the claim about `VIndRestore.Faithful` (type cone 7, likewise `TrExpr`-free).  At the
`NFn` block `member` is discharged by `rfl`, i.e. by computation in the abstract term language.
What `member` genuinely needs in general is that the checker's `Expr`-level rebuild agrees with
`VNestedOcc.member` *after* translation — so `TrExprS` enters through whatever connects a
`Result` to a `VInductDecl'`, not through this clause. -/

namespace ElimNestedInductive.Result

/-- The genuinely semantic residue of `VInductDecl'.Built`. -/
structure SemResidue (types : List Lean.InductiveType) (D : VInductDecl') (K : List Lean.Name)
    (env : VEnv) (R : VIndRestore) (occ : Nat → VNestedOcc) : Prop where
  /-- The companion member **is** the value the construction computes. -/
  member : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    T = (occ j).member D.header R
  /-- The environment holds the nested block the occurrence is at. -/
  occurs : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → (occ j).Occurs env

namespace OccData
variable {r : Result} {types : List Lean.InductiveType} {D : VInductDecl'} {K : List Name}
  {ls : Nat → List VLevel} {as : Nat → List VExpr} {occ : Nat → VNestedOcc} {env : VEnv}

/-- **The four-clause residue from the two-clause one.**  `head` and `ctorName_inv` are gone. -/
theorem occResidue (hd : r.OccData types occ) (h : r.RestoreData types D K as)
    (hs : SemResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ) :
    r.OccResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ where
  member := hs.member
  occurs := hs.occurs
  ctorName_inv := fun j T hT hK C hC => hd.ctorName_inv h j T hT hK C hC
  head := fun j T hT hK t ht => hd.head h j T hT hK t ht

end OccData
end ElimNestedInductive.Result


/-! ## 7. The nested step, from `RestoreData ∧ OccData ∧ SemResidue` -/

namespace ElimNestedInductive.Result

namespace OccData
variable {r : Result} {types : List Lean.InductiveType} {D : VInductDecl'} {K : List Name}
  {ls : Nat → List VLevel} {as : Nat → List VExpr} {occ : Nat → VNestedOcc} {env : VEnv}

/-- **`VInductDecl'.Built` from the two-clause residue.** -/
theorem mkRestore_built (hd : r.OccData types occ) (h : r.RestoreData types D K as)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hs : SemResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ) :
    D.Built (r.mkRestore types D.uvars D.np ls as) K env occ :=
  h.mkRestore_built hl ha (hd.occResidue h hs)

/-- **`VIndRestore.Faithful`** — still a theorem, now from two clauses instead of four. -/
theorem mkRestore_faithful (hd : r.OccData types occ) (h : r.RestoreData types D K as)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hs : SemResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ) :
    (r.mkRestore types D.uvars D.np ls as).Faithful D env K (fun j => (occ j).decl.np) :=
  (hd.mkRestore_built h hl ha hs).toFaithful

theorem mkRestore_canonical (hd : r.OccData types occ) (h : r.RestoreData types D K as)
    (hown : D.CanonicalOwn K)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hs : SemResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ) :
    D.Canonical :=
  (hd.mkRestore_built h hl ha hs).canonical hown

/-- **The whole nested step, from the checker's data plus `member` and `occurs`.** -/
theorem mkRestore_AddNested {env' : VEnv} (hd : r.OccData types occ)
    (h : r.RestoreData types D K as) (hwf : D.WF env) (hown : D.CanonicalOwn K)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hs : SemResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ)
    (hadd : env.addInductR D K (r.mkRestore types D.uvars D.np ls as) = some env') :
    VEnv.AddNested env D K (r.mkRestore types D.uvars D.np ls as)
      (fun j => (occ j).decl.np) env' :=
  h.mkRestore_AddNested hwf hown hl ha (hd.occResidue h hs) hadd

/-- …and the packaged premise of `VDecl.WF.inductNested`. -/
theorem mkRestore_AddNestedStep {env' : VEnv} (hd : r.OccData types occ)
    (h : r.RestoreData types D K as) (hwf : D.WF env) (hown : D.CanonicalOwn K)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hs : SemResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ)
    (hadd : env.addInductR D K (r.mkRestore types D.uvars D.np ls as) = some env') :
    VEnv.AddNestedStep env D K (r.mkRestore types D.uvars D.np ls as) env' :=
  ⟨_, hd.mkRestore_AddNested h hwf hown hl ha hs hadd⟩

end OccData
end ElimNestedInductive.Result

/-! ## 6. `OccData` at the checker's own data, and the split bounded both ways

The block is `NestedRestoreWit.lean`'s: `NFn` nesting `PFn`, with `nfnResult` the `Result` the
implementation produces (checked against `run` by execution there, §1.1). -/

namespace NestedWit
open InductiveDeclExamples ElimNestedInductive

/-- **`OccData` is satisfiable.**  Six fields, all by computation. -/
theorem nfnResult_occData : nfnResult.OccData [nfnIndType] (fun _ => pfnOcc) where
  auxName := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht; rfl
    · simp [nfnResult] at ht
  auxHead := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht
      exact ⟨.app (.const ``PFn []) (.const ``NFn []), [], rfl, rfl⟩
    · simp [nfnResult] at ht
  ctorName := by
    intro j C hC
    simp only [show pfnOcc.src.ctors = [pfnMk] from rfl, List.mem_cons, List.not_mem_nil,
      or_false] at hC
    subst hC; decide
  srcCtorPrefix := by
    intro j C hC
    simp only [show pfnOcc.src.ctors = [pfnMk] from rfl, List.mem_cons, List.not_mem_nil,
      or_false] at hC
    subst hC; decide
  auxCtors := by
    rintro (_ | _ | j) t ht hle C hC
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht
      simp only [show pfnOcc.src.ctors = [pfnMk] from rfl, List.mem_cons, List.not_mem_nil,
        or_false] at hC
      subst hC; exact ⟨_, List.mem_cons_self, rfl⟩
    · simp [nfnResult] at ht
  ctorNodup := by decide

/-- …and the two clauses §4 closes are the ones §7 of `NestedRestoreWit.lean` discharged by
hand, so this reproduces `nfnResult_occResidue`'s `head` and `ctorName_inv` by theorem. -/
theorem nfnResult_occResidue' {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂) :
    nfnResult.OccResidue [nfnIndType] nfnAux nfnK env₂ nfnRestore' (fun _ => pfnOcc) :=
  nfnResult_occData.occResidue nfnResult_restoreData
    { member := by
        rintro (_ | _ | j) T hT hK
        · cases hT; exact absurd hK (by decide)
        · cases hT; rfl
        · simp [nfnAux] at hT
      occurs := fun _ _ _ _ => pfnOcc_occurs h }

/-! ### 6.1 `OccData` is not slack in `RestoreData`

`nfnResultBadHead` (`NestedRestoreWit.lean` §2.1) satisfies all fourteen `RestoreData` fields and
all four name-discipline obligations.  It fails `OccData` — at `auxHead`, the one field that
reads the stored `Expr` — so the six fields are content the fourteen cannot see. -/

theorem nfnResultBadHead_not_occData :
    ¬ nfnResultBadHead.OccData [nfnIndType] (fun _ => pfnOcc) := by
  intro hd
  obtain ⟨e, lvls, he, hfn⟩ := hd.auxHead 1 _ rfl (by simp)
  rw [show nfnResultBadHead.aux2nested.lookup `_nested.PFn_1
      = some (.const ``NFn []) from rfl] at he
  cases he
  have h1 : (Expr.const ``NFn ([] : List Level)) = .const pfnOcc.tyName lvls := hfn
  injection h1 with h2 _
  exact absurd h2 (by decide)

/-! ### 6.2 `occurs` is not slack: `RestoreData` and `OccData` say nothing about `env`

Neither bundle mentions the environment, so both hold verbatim at `VEnv.empty`, where the nested
block `PFn` has not been declared and `Occurs.ty_const` is false.  This is the lower bound on
`SemResidue.occurs`. -/

theorem semResidue_not_occurs_empty :
    ¬ Result.SemResidue [nfnIndType] nfnAux nfnK VEnv.empty nfnRestore' (fun _ => pfnOcc) := by
  intro hs
  have ho := hs.occurs 1 _ rfl (by decide)
  exact absurd ho.ty_const (by simp [VEnv.empty])

/-! ### 6.3 `member` is not slack either

`pfnOccBadTy` perturbs the **source block** `PFn`'s stored type by one universe: `PFn`'s arity
becomes `Type → Prop` instead of `Type → Type`.  Nothing in `RestoreData` or `OccData` reads
`(occ j).src.type` — the six `OccData` fields see only `src`'s *constructor names*, `tyName` and
`auxName`, all of which are unchanged — and the two semantic parameters `nfnLs`/`nfnAs` still
agree with `pfnOccBadTy.lvls`/`.args`, so `mkRestore_built`'s `hl` and `ha` hold too.  What fails
is `member`: the companion member the construction computes now has type `Prop`, and
`nfnAux`'s does not. -/

def pfnTypeBadTy : VIndType := { pfnType with type := .forallE (.sort (.succ .zero)) (.sort .zero) }

def pfnDeclBadTy : VInductDecl' := { pfnDecl with types := [pfnTypeBadTy] }

/-- The occurrence at the perturbed source block: same index, same levels, same spine, same
names. -/
def pfnOccBadTy : VNestedOcc := { pfnOcc with decl := pfnDeclBadTy }

example : pfnOccBadTy.tyName = pfnOcc.tyName := rfl
example : pfnOccBadTy.src.ctors.map (·.name) = pfnOcc.src.ctors.map (·.name) := rfl
example : pfnOccBadTy.auxName = pfnOcc.auxName := rfl
example : pfnOccBadTy.lvls = nfnLs 1 := rfl
example : pfnOccBadTy.args = nfnAs 1 := rfl

/-- `OccData` still holds — it is the same proof, since every field reads only names. -/
theorem nfnResult_occData_badTy : nfnResult.OccData [nfnIndType] (fun _ => pfnOccBadTy) where
  auxName := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht; rfl
    · simp [nfnResult] at ht
  auxHead := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht
      exact ⟨.app (.const ``PFn []) (.const ``NFn []), [], rfl, rfl⟩
    · simp [nfnResult] at ht
  ctorName := by
    intro j C hC
    simp only [show pfnOccBadTy.src.ctors = [pfnMk] from rfl, List.mem_cons, List.not_mem_nil,
      or_false] at hC
    subst hC; decide
  srcCtorPrefix := by
    intro j C hC
    simp only [show pfnOccBadTy.src.ctors = [pfnMk] from rfl, List.mem_cons, List.not_mem_nil,
      or_false] at hC
    subst hC; decide
  auxCtors := by
    rintro (_ | _ | j) t ht hle C hC
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht
      simp only [show pfnOccBadTy.src.ctors = [pfnMk] from rfl, List.mem_cons, List.not_mem_nil,
        or_false] at hC
      subst hC; exact ⟨_, List.mem_cons_self, rfl⟩
    · simp [nfnResult] at ht
  ctorNodup := by decide

/-- The companion member the construction computes at the perturbed source. -/
theorem pfnOccBadTy_member_type :
    (pfnOccBadTy.member nfnAux.header nfnRestore').type = .sort .zero := rfl

/-- **`member` fails**, at any environment. -/
theorem semResidue_not_member_badTy {env : VEnv} :
    ¬ Result.SemResidue [nfnIndType] nfnAux nfnK env nfnRestore' (fun _ => pfnOccBadTy) := by
  intro hs
  have hm := hs.member 1 _ rfl (by decide)
  have := congrArg VIndType.type hm
  rw [pfnOccBadTy_member_type] at this
  exact absurd this (by simp)

/-- …and so does `Built`, at the same clause. -/
theorem nfnAux_not_built_badTy {env : VEnv} :
    ¬ nfnAux.Built nfnRestore' nfnK env (fun _ => pfnOccBadTy) := by
  intro hb
  exact semResidue_not_member_badTy ⟨hb.member, hb.occurs⟩

/-- **The exact scope of that bound.**  `pfnOccBadTy` also violates `occurs` — `Occurs.ty_const`
pins the source member's *stored* type against the environment, and the perturbation is exactly
that type.  So the bound above says `member` is not slack in
`RestoreData ∧ OccData ∧ hl ∧ ha`; it does **not** say `member` is not slack in those *plus*
`occurs`.  Whether it is remains open, and it turns on whether `VInductDecl'.Declared` pins
`(occ j).src.indices` — which `Theory/Inductive/Decl.lean:694`'s own docstring says is one of the
fields *unrecoverable* from a declaration, so only up to the recursor type's `IsDefEqU`. -/
theorem pfnOccBadTy_not_occurs {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂) :
    ¬ pfnOccBadTy.Occurs env₂ := by
  intro ho
  have h1 := ho.ty_const
  rw [show pfnOccBadTy.tyName = ``PFn from rfl, pfn_const h] at h1
  simp only [Option.some.injEq] at h1
  have h2 : pfnType.type = pfnOccBadTy.src.type := congrArg VConstant.type h1
  simp only [show pfnType.type = .forallE (.sort (.succ .zero)) (.sort (.succ .zero)) from rfl,
    show pfnOccBadTy.src.type = .forallE (.sort (.succ .zero)) (.sort .zero) from rfl,
    VExpr.forallE.injEq, VExpr.sort.injEq] at h2
  exact absurd h2.2 (by simp)

/-! ### 6.4 `member` is not slack even given `occurs` — and the freedom is on the `D` side

Row 75c asked whether `member` is slack once `occurs` is added, and expected the question to turn
on whether `VInductDecl'.Declared` pins `(occ j).src.indices`.  It does not turn on that, and the
answer is **no, `member` is not slack** — for a different and more structural reason.

`occurs` constrains `occ`; it says nothing about `D`.  And **nothing else in the chain constrains
`D`'s companion members either**: `TrIndDeclN.trType` and `trCtors` are quantified over
`types[j]? = some t`, which is `none` past the cut (§8), so the companion members of `D` are
pinned by `Built.member` and by *nothing else anywhere*.  `nfnAuxBadTy` is that freedom used: the
companion member of the **new** block is given type `Prop`, `occ` is left completely alone, and

* all fourteen `RestoreData` fields still hold (`nfnResult_restoreData_badD` — the four that
  mention `D` see only names, which are unchanged);
* all six `OccData` fields still hold — `OccData` does not mention `D` at all, so
  `nfnResult_occData` applies verbatim;
* `hl` and `ha` still hold — they read `D` only through `T.name ∈ K`;
* **`occurs` still holds** — it is `pfnOcc_occurs`, untouched;
* `member` is **false**.

So the residue is genuinely two clauses, and `member` is the one that pins `D`'s companions.  For
the record on the `Declared` half of row 75c: `VEnv.LE.constants` is *exact* equality of the
`VConstant` (`Theory/VEnv.lean:36`), and `addInduct'` runs `addIndRecs`, so `Declared D env` does
pin `D.recType j` exactly, and `recType` mentions `T.indices` syntactically (`Decl.lean:545-551`,
through `atRecTele T.indices` and `bvars 0 ni`).  `Decl.lean:694`'s "unrecoverable" is about
recovering a field from a `Lean.Declaration`, **not** about being pinned by `Declared` against an
environment — I conflated the two in row 75c.  So `indices` is pinned up to injectivity of
`recType` in that field; that injectivity is not proved and is now not needed for this question. -/

/-- `nfnAux` with the **companion** member's stored type perturbed by one universe.  Only `D`
changes; `occ` is `pfnOcc` throughout. -/
def nfnAuxBadTy : VInductDecl' :=
  { nfnAux with types :=
      [{ name := ``NFn, type := .sort (.succ .zero), indices := [], ctors := [nfnNode] },
       { name := `_nested.PFn_1, type := .sort .zero, indices := [], ctors := [pfnAuxMk] }] }

example : nfnAuxBadTy.types.map (·.name) = nfnAux.types.map (·.name) := rfl
example : nfnAuxBadTy.uvars = nfnAux.uvars := rfl
example : nfnAuxBadTy.np = nfnAux.np := rfl

theorem nfnResult_restoreData_badD :
    nfnResult.RestoreData [nfnIndType] nfnAuxBadTy nfnK nfnAs where
  len := rfl
  name := by
    rintro (_ | _ | j) T hT t ht <;> simp only [nfnAuxBadTy, nfnAux, nfnResult] at hT ht ⊢ <;>
      first | (cases hT; cases ht; rfl) | simp at hT
  ctor := by
    rintro (_ | _ | j) T hT t ht C hC <;> simp only [nfnAuxBadTy, nfnAux, nfnResult] at hT ht ⊢ <;>
      first
        | (cases hT; cases ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at hC;
           subst hC; exact ⟨_, List.mem_cons_self, rfl⟩)
        | simp at hT
  companions := by
    rintro (_ | _ | j) T hT <;> simp only [nfnAuxBadTy, nfnAux] at hT <;> [skip; skip; simp at hT] <;>
      cases hT <;> simp [nfnK]
  auxName := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht; decide
    · simp [nfnResult] at ht
  auxCtorName := by
    rintro (_ | _ | j) t ht hle c hc
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · simp [nfnResult] at ht
  auxCtorPrefix := by
    rintro (_ | _ | j) t ht hle c hc
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · simp [nfnResult] at ht
  auxNodup := by decide
  ownName := by
    rintro (_ | _ | j) t ht hlt
    · simp only [nfnResult] at ht; cases ht; decide
    · exact absurd hlt (by simp)
    · exact absurd hlt (by simp)
  ownCtor := by
    rintro (_ | _ | j) t ht hlt c hc
    · simp only [nfnResult] at ht; cases ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · exact absurd hlt (by simp)
    · exact absurd hlt (by simp)
  head := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht; decide
    · simp [nfnResult] at ht
  headNe := by
    rintro (_ | _ | j) t ht hle
    · exact absurd hle (by simp)
    · simp only [nfnResult] at ht; cases ht; decide
    · simp [nfnResult] at ht
  auxRec := nfn_auxRec
  args := by
    intro j a ha
    simp only [nfnAs] at ha
    split at ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; subst ha; decide
    · simp at ha

/-- The `occurs` clause holds at the perturbed `D`: it does not mention `D` except through the
guard, and `occ` is unchanged. -/
theorem occurs_badD {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂) :
    ∀ (j : Nat) (T : VIndType), nfnAuxBadTy.types[j]? = some T → T.name ∈ nfnK →
      pfnOcc.Occurs env₂ := fun _ _ _ _ => pfnOcc_occurs h

/-- The construction's companion member, at the perturbed header.  Its `type` does not depend on
`H.names`, so the perturbation cannot reach it. -/
theorem pfnOcc_member_badD_type :
    (pfnOcc.member nfnAuxBadTy.header nfnRestore').type = .sort (.succ .zero) := rfl

/-- **`member` is false**, with `occurs` satisfied. -/
theorem semResidue_not_member_badD {env : VEnv} :
    ¬ Result.SemResidue [nfnIndType] nfnAuxBadTy nfnK env nfnRestore' (fun _ => pfnOcc) := by
  intro hs
  have hm := hs.member 1 _ rfl (by decide)
  have h2 := congrArg VIndType.type hm
  rw [pfnOcc_member_badD_type] at h2
  exact absurd h2 (by simp)

/-- …hence `Built` is false there too, at `member`. -/
theorem nfnAuxBadTy_not_built {env : VEnv} :
    ¬ nfnAuxBadTy.Built nfnRestore' nfnK env (fun _ => pfnOcc) := fun hb =>
  semResidue_not_member_badD ⟨hb.member, hb.occurs⟩

end NestedWit

/-! ## 8. `RestoreData` at `run`'s monadic output, field by field

`Verify/Inductive/NestedRunInvariant.lean` §7 closes `RunSkelExtends` and gives `run_prefix`: on
the prefix `j < types.length`, `run`'s output member carries the *input* member's name and its
constructors' names, in order.  Here is what each of the four fields I previously claimed as a
bundle actually does with that.

**A correction to my own claim.**  Last round I wrote that `name`, `ctor`, `ownName` and
`ownCtor` "follow from a single statement about `replaceIfNested`".  That was a bundle claim and
it was wrong twice over: `name` and `ctor` are not `r`-side facts at all — they compare `r.types`
to `D.types`, so they need the *translation* (`TrIndDeclN`) as well — and even with it only their
prefix halves follow.  The truth, field by field:

| field | status |
| --- | --- |
| `ownName` | **falls** — `ownName_of_run`, reduced to a hypothesis on the checker's *input* |
| `ownCtor` | **falls** — `ownCtor_of_run`, likewise |
| `name` | **prefix half falls** (`name_prefix_of_run`); tail half declined |
| `ctor` | **declined**, and not for want of plumbing — see below |

`ownName`/`ownCtor` do not become *provable*: they become statements about `types`, which is what
`Environment.addInductive`'s caller hands in, and there they are the unchecked name-discipline
fact `NestedRestore.lean` §8.2 measures (ledger row 58).  That is still progress: the obligation
moves off the checker's *output* — which no caller can inspect — onto its *input*, which the
caller supplies and could in principle check.

**Why the tail halves do not follow.**  `RunSkelExtends` pins only the prefix; it says nothing
about `r.types`' auxiliary tail, by design (`replaceIfNested` *creates* that tail).  And
`TrIndDeclN` has **no** `trType`/`trCtors` clause for `j ≥ types.length`: `trType` is quantified
over `types[j]? = some t`, which is `none` past the cut.  So nothing currently relates
`r.types[j].name` to `D.types[j].name` on the companions — that is `RestoreData.auxName`'s
territory and it needs `mkUniqueName`'s output, not the skeleton.

**Why `ctor` is declined.**  Its prefix half needs `∃ c ∈ t.ctors, c.name = C.name`, and
`TrIndDeclN.trCtors` gives `c.name = R.ctorName C.name` — the *restored* name.  Closing the gap
needs `R.ctorName C.name = C.name` on a user member, which is `VIndRestore.OwnId.ctorName`; and
in the bundle `mkRestore_ownId`'s `ctorName` clause is proved **from `RestoreData.ctor`**
(`NestedRestore.lean:617-622`).  So deriving `ctor` from `OwnId` here would be circular.

The escape route is visible and not taken: `mkRestore.ctorName` misses whenever its argument is
outside the barrier (`ctorRenames_dom` + `List.lookup_eq_none_of_forall`), so
`¬ IsNestedName C.name` for a constructor of a user member would give `R.ctorName C.name = C.name`
outright.  But `C.name` is a `D`-side name and nothing in `TrIndDeclN` or `RunSkelExtends` bounds
it; the fact that would is exactly `mkUniqueName`'s freshness against the *input* block, which is
`auxNodup`/`auxName` territory.  So `ctor` is not slack-in-the-plumbing: it is a genuinely
separate obligation, and I am naming it rather than smuggling it in. -/

namespace ElimNestedInductive.Result

variable {fuel np : Nat} {types : List Lean.InductiveType} {s : ElimNestedInductive.State}
  {r : Result} {s' : ElimNestedInductive.State} {cenv : Environment}

/-- **`RestoreData.ownName` at `run`'s monadic output**, reduced to the same fact about the
checker's *input* block. -/
theorem ownName_of_run (hs : s.newTypes.toList = types)
    (h : ElimNestedInductive.run fuel np types cenv s = .ok (r, s'))
    (hin : ∀ u ∈ types, ¬ IsNestedName u.name) :
    ∀ (j : Nat) t, r.types[j]? = some t → j < types.length → ¬ IsNestedName t.name := by
  intro j t hjt hj
  obtain ⟨u, hu, hn, -⟩ := ElimNestedInductive.run_prefix hs h j t hjt hj
  rw [hn]
  exact hin u (List.mem_iff_getElem?.2 ⟨j, hu⟩)

/-- **`RestoreData.ownCtor` at `run`'s monadic output**, likewise. -/
theorem ownCtor_of_run (hs : s.newTypes.toList = types)
    (h : ElimNestedInductive.run fuel np types cenv s = .ok (r, s'))
    (hin : ∀ u ∈ types, ∀ c ∈ u.ctors, ¬ IsNestedName c.name) :
    ∀ (j : Nat) t, r.types[j]? = some t → j < types.length →
      ∀ c ∈ t.ctors, ¬ IsNestedName c.name := by
  intro j t hjt hj c hc
  obtain ⟨u, hu, -, hcs⟩ := ElimNestedInductive.run_prefix hs h j t hjt hj
  have hmem : c.name ∈ u.ctors.map (·.name) := by
    rw [← hcs]; exact List.mem_map.2 ⟨c, hc, rfl⟩
  obtain ⟨c', hc', hn⟩ := List.mem_map.1 hmem
  rw [← hn]
  exact hin u (List.mem_iff_getElem?.2 ⟨j, hu⟩) c' hc'

/-- **`RestoreData.name` at `run`'s monadic output, on the prefix.**  `run_prefix` moves the
question from `r.types` to `types`, and `TrIndDeclN.trType` answers it there. -/
theorem name_prefix_of_run {venv : VEnv} {Us : List Lean.Name} {npar nn : Nat} {iu : Bool}
    {D : VInductDecl'} {K : List Lean.Name} {R : VIndRestore}
    (htr : TrIndDeclN venv Us npar types iu nn D K R)
    (hs : s.newTypes.toList = types)
    (h : ElimNestedInductive.run fuel np types cenv s = .ok (r, s')) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → ∀ t, r.types[j]? = some t →
      j < types.length → t.name = T.name := by
  intro j T hT t hjt hj
  obtain ⟨u, hu, hn, -⟩ := ElimNestedInductive.run_prefix hs h j t hjt hj
  rw [hn]
  exact (htr.trType j u T hu hT).1

end ElimNestedInductive.Result


/-! ## 9. `member`'s three commutation lemmas: status

Last round I named three commutations as what `member` needs, one level below it, and said they
needed proving.  **One of the three is already proved in the tree** — a correction to that claim:

* **(A) `instantiateLevelParamsNoCache` vs `instL`.**  `Lean4Lean.TrExprS.instL`
  (`Verify/Typing/Lemmas.lean:2465`):
  ```
  env.WF → VLCtx.WF env ls'.length Δ → List.mapM (VLevel.ofLevel Us) ls = some ls' →
    ps.length = ls.length → TrExprS env ps Δ e e' →
    TrExpr env Us (Δ.instL ls') (e.instantiateLevelParamsNoCache ps ls) (VExpr.instL ls' e')
  ```
  It is stated over `instantiateLevelParamsNoCache` — core's pure function, the one PR #42
  re-pointed six checker sites to — and mentions neither `Expr.replace` nor the cached
  `instantiateLevelParams`.  Its side conditions are the level list translating
  (`mapM (VLevel.ofLevel Us) ls = some ls'`) and the arity match `ps.length = ls.length`, and
  `replaceIfNested` supplies both: `I_lvls` comes from a well-formed constant application
  `I.{I_lvls}` and `J_info.levelParams.length = I_lvls.length` is the `numLevelParams` check.
  **One caveat**: it lands in `TrExpr` (∃ up to `IsDefEqU`), not `TrExprS`.  `Built.member` is a
  *syntactic* equality of `VIndType`s, so the `TrExpr`/`TrExprS` gap is real content, not
  bookkeeping — it is where `IsDefEqU` would have to be discharged or the statement of `member`
  routed through `TrExpr`.

* **(B) `instantiateForallParams` vs `splitPis`/`instAll`.**  Not proved.  What is needed:
  `ElimNestedInductive.instantiateForallParams e n ps = .ok body` peels `n` `forallE` nodes off
  `e` and then applies `instantiateRevRange 0 n ps`; the `VExpr` side is
  `VExpr.instAll (splitPis n E).2 Args`.  So this is an `n`-fold `TrExprS` substitution lemma
  composed with a `forallE`-peeling lemma, and it will carry two side conditions — `ps.size = n`
  and each `ps[i]` translating to `Args[i]` — both of which `replaceIfNested` supplies
  (`assert! I_nparams ≤ args.size`, discharged by `isNestedInductiveApp?`, plus the
  already-checked translation of the occurrence's spine).  It also needs
  `Expr.instantiateRevRange_eq`, one of the 24 frozen axioms, which is how every other
  `instantiateRev` fact in `Verify/` is stated.

* **(C) `LocalContext.mkForall` vs `mkPi`.**  Not proved.  `Verify/LocalContext.lean` has the pure
  half (`mkBinding_eq`, `mkBindingList1_abstract`, `mkBindingList_eq_fold`), whose side conditions
  are `b.looseBVarRange' = 0` and `xs.Nodup` — supplied by `withParams`, which allocates each
  parameter with a fresh `mkFreshId`.  What is missing is the `TrExprS` half: that abstracting the
  `As` fvars in declaration order corresponds to `mkPi H.params`.

**Neither (B) nor (C) becomes an `OccData` field.**  Both are proof machinery with side conditions
the call site supplies, exactly as they should be, and the conclusion of §5 stands unrevised:
`member` needs no new field and no new premise. -/


/-! ## 10. `ctor`'s circle does not break, and why: `mkUniqueName` is fresh against the
*environment*, not against the block

§8 declined `RestoreData.ctor` and named the escape: `¬ IsNestedName C.name` on a user member makes
the `ctorRenames` lookup miss, so `R.ctorName C.name = C.name`.  I then said the fact that would
supply it is "`mkUniqueName`'s freshness against the input block".  **That was wrong, and it is
wrong in a way that cannot be patched: no such freshness exists.**

`mkUniqueName`'s loop tests `env.contains r` (`Add.lean:766-773`), and that is *all* it tests —
`mkUniqueName_fresh` (`Verify/Inductive/NestedRunInvariant.lean` §5) is the exact statement.  The
block being declared is not in `env`; keeping its names apart from what is already there is
`Environment.addInductive`'s separate business.  So `mkUniqueName` cannot separate its output from
the input block, and §10.1 exhibits a block where it does not.

### 10.1 A reachable collision (test, not a proof)

Member 0 is **constructor-less** and carries the exact name `mkUniqueName (`_nested ++ ``PFn)`
returns at `nextIdx = 1`; member 1 is an ordinary nested member.  Because member 0 has no
constructors, its name occurs in no constructor *type*, and `checkNoNestedAux` — which scans
constructor types only (`Add.lean:934`) — never sees it.  `run` then invents that same name for the
companion, and `r.types` carries it **twice**.

`Lean4Lean.Environment.addInductive` on this block reports
`(kernel) constant has already been declared '_nested.Lean4Lean.InductiveDeclExamples.PFn_1'`, so
the outcome is a *rejection*, not unsoundness — and the C++ kernel rejects it the same way, for the
same reason.  What the witness settles is the proof-side question: **`RestoreData.ownName` is
exactly what excludes this state, and nothing in the implementation does.**  That is ledger row
58's standing decision meeting the witness it asked for, on `ownName` (not on `srcCtorPrefix`,
which stays flagged and untouched). -/

namespace NestedWit
open InductiveDeclExamples ElimNestedInductive

/-- The name `mkUniqueName (`_nested ++ ``PFn)` returns at `nextIdx = 1`. -/
def collName : Lean.Name := `_nested ++ (``PFn).appendAfter "_1"

/-- A constructor-less member carrying that name: its own name appears in no constructor type. -/
def collA : Lean.InductiveType := { name := collName, type := .sort (.succ .zero), ctors := [] }

/-- …and an ordinary nested member alongside it. -/
def collB : Lean.InductiveType :=
  { name := `CollFoo, type := .sort (.succ .zero),
    ctors := [{ name := `CollFoo.mk,
                type := .forallE `a (.app (.const ``PFn []) (.const `CollFoo []))
                  (.const `CollFoo []) .default }] }

#eval show Lean.CoreM Unit from do
  let kenv := (← Lean.getEnv).toKernelEnv
  let types := [collA, collB]
  for indType in types do
    for ctor in indType.ctors do
      match Lean4Lean.checkNoNestedAux ctor.name ctor.type with
      | Except.ok _ => pure ()
      | Except.error _ => throwError "gate rejected the block -- finding void"
  let .ok r := (ElimNestedInductive.run 1000 0 types kenv).run'
      { lvls := [], newTypes := types.toArray }
    | throwError "run rejected the block"
  let names := r.types.map (·.name)
  unless names.length = 3 && names[0]! = names[2]! do
    throwError "no collision: r.types names = {names}"
  match Lean4Lean.Environment.addInductive kenv [] 0 types false false with
  | Except.ok _ => throwError "addInductive ACCEPTED a block with a duplicated member name"
  | Except.error _ =>
    Lean.logInfo m!"collision: checkNoNestedAux accepts the block, run's r.types names are \
      {names} (member 0 duplicated by the companion), and addInductive then rejects it on the \
      duplicate constant ✓"

/-! ### 10.2 A divergence found on the way: one missing `checkNoNestedAux` call

The C++ kernel applies the reserved-prefix test to **both** a member's own type and each
constructor's type:

```
check_no_nested_aux(*this, ind_type.get_name(), ind_type.get_type());          // inductive.cpp:1241
for (constructor const & cnstr : ind_type.get_cnstrs()) {
    check_no_metavar_no_fvar(*this, constructor_name(cnstr), constructor_type(cnstr));
    check_no_nested_aux(*this, constructor_name(cnstr), constructor_type(cnstr));  // :1244
}
```

`Lean4Lean.Environment.addInductive` (`Lean4Lean/Inductive/Add.lean:930-935`) has the constructor
call and **not** the member one: it runs `checkNoMVarNoFVar indType.name indType.type` and then, per
constructor, `checkNoMVarNoFVar` and `checkNoNestedAux`.  So a member whose *own type* mentions a
`_nested` constant passes lean4lean's gate and is rejected by C++.  The `#eval` below is that
difference, both halves computed.

**FIXED 2026-09-01** in `Lean4Lean/Inductive/Add.lean`: `Environment.addInductive` now calls
`checkNoNestedAux indType.name indType.type` alongside the `checkNoMVarNoFVar` on the same type, so
the two gates agree and there is **no** `divergences.md` entry to make. Arena re-run after the
change: 185 correct / 6 either / 0 wrong, unchanged.

**Correction to how this was first described, and it is the coordinator's.** The commit that made
the fix claimed this `#eval` "throwErrors if the two gates stop disagreeing, so the fix cannot be
silently reverted". **That was false.** The first `#eval` below *models* the old gate by iterating
constructors inline — `divIndType.ctors` is `[]`, so its loop body never runs — and never calls
`Environment.addInductive`, so it passes identically with or without the fix. It demonstrates the
difference between two *checks*; it does not guard the implementation. The second `#eval` is the
actual regression test: it calls the real function and requires the failure to be the
**reserved-prefix** error, which only the member-type call can produce, and which therefore fails if
the fix is reverted. Claiming a test guards something it does not is the failure mode this file's
own §10.1 note exists to prevent. -/

def divIndType : Lean.InductiveType :=
  { name := `DivBar,
    type := .forallE `x (.const `_nested.Foo []) (.sort (.succ .zero)) .default,
    ctors := [] }

#eval show Lean.CoreM Unit from do
  let mut rejected := false
  for ctor in divIndType.ctors do
    match Lean4Lean.checkNoNestedAux ctor.name ctor.type with
    | Except.ok _ => pure () | Except.error _ => rejected := true
  if rejected then throwError "lean4lean's gate rejected it -- finding void"
  match Lean4Lean.checkNoNestedAux divIndType.name divIndType.type with
  | Except.ok _ => throwError "C++'s extra call would also accept -- no divergence"
  | Except.error _ =>
    Lean.logInfo "the shape: the OLD gate (constructor types only) accepts a member whose own \
      type mentions a `_nested` constant, while the call C++ makes on the member type rejects \
      it.  This eval models the old gate and is NOT a regression test -- see the next one ✓"

/-! **The actual regression test for the fix.**  Calls the real `Environment.addInductive` and
requires the failure to be the *reserved-prefix* error.  Only the member-type `checkNoNestedAux`
call can produce that message here (`divIndType` has no constructors), so this `#eval` fails if
that call is removed.  Unlike the eval above, it cannot pass with the fix reverted. -/
#eval show Lean.CoreM Unit from do
  let kenv := (← Lean.getEnv).toKernelEnv
  match Lean4Lean.Environment.addInductive kenv [] 0 [divIndType] false false with
  | Except.ok _ =>
    throwError "REGRESSION: addInductive accepted a member whose own type mentions a `_nested` \
      constant.  The `checkNoNestedAux indType.name indType.type` call in Add.lean is missing."
  | Except.error (.other msg) =>
    unless (msg.splitOn "reserved prefix").length ≥ 2 do
      throwError "addInductive rejected it, but not on the reserved prefix -- the member-type \
        gate may be gone and something else is rejecting.  Message: {msg}"
    Lean.logInfo "regression test: addInductive rejects a member whose own type mentions a \
      `_nested` constant, on the reserved-prefix gate ✓"
  | Except.error _ =>
    throwError "addInductive rejected it, but not with an `.other` message, so the \
      reserved-prefix gate is not what fired"

end NestedWit

/-! ### 10.3 So what does `ctor` need?

Not a name-discipline check.  `RestoreData.ctor` is the bundle's **only** statement that the
checker's constructor names and `D`'s agree on the user's members, and `TrIndDeclN` relates the two
sides *only through* `R.ctorName` (`TrIndCtorR` is `c.name = R.ctorName C.name`).  `ownCtor` bounds
the **checker's** names; `C.name` is a `D`-side name, and no available fact bounds it.

So `ctor` is neither slack nor a fourth row-58 fact: it is a **translation-relation gap**.  Closing
it means one new clause on `TrIndDeclN`, of the shape

```
ctorName_own : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
  ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → c.name = C.name
```

which `Environment.addInductive`'s nested path establishes by construction on the user's members
(their names pass through the pass untouched — `run.loop` rebuilds each constructor as
`{ ctor with type := … }`, and `run_prefix` is the proof).  `TrIndDeclN` is a definition the
`addDecl.WF` chain consumes, so this is **reported, not done**.  Note it is *not* a hypothesis
about the input block and *not* a check any kernel would perform; it is a fact about the
translation, and the machinery to prove it — `run_prefix` — is already in place. -/

end Lean4Lean
