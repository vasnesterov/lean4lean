import Lean4Lean.Theory.Inductive.NestedRules
import Lean4Lean.Verify.Environment.InductR

/-!
# A `VIndRestore` built from the checker's own data, and the name barrier that makes
`SubstFree` expressible

Two gaps closed here.

**Gap 1 — `SubstFree` was not expressible.**  `VIndRestore.SubstFree`
(`Theory/Inductive/NestedRules.lean` §7.4) says the restoration's own heads escape
`R.csubst D K`.  At `K = []` it is free (the substitution is empty), and at the two
hand-written witnesses it is discharged by `decide`.  In general it needs a *reason* why the
restored heads — which are the names of a block the environment already holds — differ from
the auxiliary names `csubst`'s domain is built from, and **no abstract predicate in the tree
constrained `K`'s names at all**.  The implementation's reason is the `_nested` prefix, and
the only `_nested`-prefix test anywhere in the package was `ElimNestedInductive`'s own
`checkNoNestedAux` (`Lean4Lean/Inductive/Add.lean:922-923` — the only two `(`_nested).isPrefixOf`
occurrences in the tree), which nothing abstract consumes.  The abstract theory does use
`Lean.Name` structure elsewhere — `Lean.mkRecName` throughout `csubstList`/`KeysFree`/`recConstsR`,
and `auxRecName`'s `appendIndexAfter'` (`Verify/Environment/InductR.lean:238`) — so what was
missing was specifically a constraint on the **auxiliary members' own** names, not any contact
with `Lean.Name` at all.

§2 supplies the missing predicate: `VIndRestore.NameBarrier R D K P`, parametric in a name
predicate `P`.  `NameBarrier.substFree` derives all four `SubstFree` clauses from it, with no
hypothesis about `env` and no `Faithful`.  §3 instantiates `P` at the concrete `_nested` test
and gives the `Lean.Name` lemmas that make the instantiation `decide`-free.

**Gap 2 — nothing built a `VIndRestore` from checker data.**  Every `VIndRestore` in the tree
was either `VInductDecl'.idRestore` or one of six hand-written examples — seven definitions in
all (`idRestore`, `ntreeRestore`, `nfnRestore`, `nfnJunkRestore`, `pfnJunkRestore`, `badRestore`,
`okRestore`) — and the only place the
implementation supplies one is `Verify/Inductive/AddInductiveStep.lean:408`, gated on
`res.aux2nested = []`.  §4 builds one from `ElimNestedInductive.Result` for the case that gate
excludes, and §5 proves of it: `VIndRestore.OwnId`, `TrIndDeclN`'s two `recName` clauses, and
`NameBarrier` (hence `SubstFree` and `KeysFree`) — the last from a hypothesis that is exactly
what an extended `checkNoNestedAux` would supply.  §6 bounds `NameBarrier` both ways, field by
field.

## What is *not* here

* `Faithful` and `Canonical`.  `Faithful` is about `env`'s stored types, i.e. about
  `TrExprS`-level agreement between `restoreNested`'s output and `VIndCtor.typeR`; `Canonical`
  is a property of `D` alone and does not mention `R`.  Neither is a name-discipline fact and
  neither is reachable from the construction below.
* the discharge of `NestedAuxNames` from `ElimNestedInductive.run`.  §5.3 states it as a
  hypothesis and §7 records precisely why: `mkUniqueName` builds the auxiliary name by
  `appendIndexAfter' (`_nested ++ J_name)`, whose `Name.modifyBase` goes through
  `extractMacroScopes`, and the *declaration's own* names are never tested for the prefix at
  all — `checkNoNestedAux` (`Lean4Lean/Inductive/Add.lean:920`) scans constructor **types**,
  not names.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## 1. Constants of a `VExpr`, filtered by a name predicate

`VExpr.NoCSubst σ` is the fact a bridge proof consumes; it is `σ c = none` at every constant
occurrence.  A *name* barrier gives it uniformly, so the recursion is factored out once. -/

/-- Every constant occurring in `e` fails `P`. -/
def VExpr.NoConstIn (P : Name → Prop) : VExpr → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const c _ => ¬ P c
  | .app a b | .lam a b | .forallE a b => NoConstIn P a ∧ NoConstIn P b

namespace VExpr
variable {P : Name → Prop} {σ : CSubst}

/-- **The barrier discharges `NoCSubst`.**  If everything in σ's domain satisfies `P` and
nothing in `e` does, `e` is σ-free. -/
theorem NoConstIn.noCSubst (hdom : ∀ n v, σ n = some v → P n) :
    ∀ {e : VExpr}, e.NoConstIn P → e.NoCSubst σ
  | .bvar _, _ | .sort _, _ => trivial
  | .const c _, h => by
    cases hc : σ c with
    | none => exact hc
    | some v => exact absurd (hdom c v hc) h
  | .app .., h | .lam .., h | .forallE .., h =>
    ⟨h.1.noCSubst hdom, h.2.noCSubst hdom⟩

@[simp] theorem noConstIn_bvars : ∀ {lo n : Nat}, ∀ a ∈ VExpr.bvars lo n, a.NoConstIn P
  | _, 0, _, h => absurd h (by simp [VExpr.bvars])
  | lo, n+1, a, h => by
    rw [VExpr.bvars, List.mem_cons] at h
    rcases h with rfl | h
    · trivial
    · exact noConstIn_bvars (lo := lo) (n := n) a h

/-- `NoConstIn` is decidable at a decidable predicate — what the `decide`-style bounds of §7
need. -/
instance decNoConstIn [DecidablePred P] : ∀ e : VExpr, Decidable (e.NoConstIn P)
  | .bvar _ | .sort _ => .isTrue trivial
  | .const c _ => inferInstanceAs (Decidable (¬ P c))
  | .app a b | .lam a b | .forallE a b =>
    @instDecidableAnd _ _ (decNoConstIn a) (decNoConstIn b)

/-- …and so is `NoCSubst`, which the negative bounds refute directly. -/
instance decNoCSubst : ∀ e : VExpr, Decidable (e.NoCSubst σ)
  | .bvar _ | .sort _ => .isTrue trivial
  | .const c _ => inferInstanceAs (Decidable (σ c = none))
  | .app a b | .lam a b | .forallE a b =>
    @instDecidableAnd _ _ (decNoCSubst a) (decNoCSubst b)

/-- The empty substitution touches nothing. -/
theorem noCSubst_id : ∀ e : VExpr, e.NoCSubst CSubst.id
  | .bvar _ | .sort _ => trivial
  | .const .. => rfl
  | .app a b | .lam a b | .forallE a b => ⟨noCSubst_id a, noCSubst_id b⟩

end VExpr

/-! ## 2. The name barrier

The six name clauses are the whole content: the three families `csubst`'s domain is built from
lie inside `P`, the three families the restoration *produces* lie outside it, and the presented
parameter spine mentions nothing inside it.  `csubst_dom` (`NestedRules.lean` §7.2) is what
turns that into `SubstFree`, so the derivation needs no `Nodup`, no `env` and no `Faithful`. -/

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {P : Name → Prop}

/-- **The separation `VIndRestore.SubstFree` was missing a reason for.**

`P` is a name predicate that *contains* the auxiliary family and *avoids* everything the
restoration produces.  In the implementation `P n` is "`n` carries the reserved `_nested`
prefix" (§3); the abstract theory needs only that some such `P` exists, which is why this is
parametric.

The asymmetry between the three `aux*` clauses and the three `res*` clauses is the point:
`csubst`'s domain is built from an auxiliary member's own name, its recursor's name and its
constructors' names (`csubst_dom`), while `SubstFree` is about the *restored* names.  Nothing
in `Faithful`, `OwnId` or the two `addConstList` successes separates the two families —
`Faithful` is vacuous at `K = []` and says nothing about `recName` at all, and neither
`typeConstsC` nor `ctorConstsCR` declares an auxiliary member's own names, so freshness cannot
separate them either.  See `Theory/Inductive/Restore.lean`'s `KeysFree` docstring, which says
the same of the weaker property. -/
structure NameBarrier (R : VIndRestore) (D : VInductDecl') (K : List Name)
    (P : Name → Prop) : Prop where
  /-- An auxiliary member's own name is inside the barrier. -/
  auxTy : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → P T.name
  /-- …so is its recursor's. -/
  auxRec : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    P (Lean.mkRecName T.name)
  /-- …and so are its constructors'. -/
  auxCtor : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ C ∈ T.ctors, P C.name
  /-- The presented type head is outside. -/
  resTy : ∀ j, ¬ P (R.tyName j)
  /-- **Quantified over every member, not over `D.ctorsAll`** — the strengthening
  `SubstFree.recName` needs over `KeysFree`, for the member with no constructors that
  `ihValuesR` still calls the recursor of. -/
  resRec : ∀ j, ¬ P (R.recName (Lean.mkRecName (D.types.getD j default).name))
  /-- The presented constructor heads are outside. -/
  resCtor : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → ∀ C ∈ T.ctors,
    ¬ P (R.ctorName C.name)
  /-- The presented parameter spine mentions no name inside the barrier. -/
  resArgs : ∀ j, ∀ a ∈ R.tyArgs j, a.NoConstIn P

/-- **Everything in `csubst`'s domain is inside the barrier.**  This is `csubst_dom` plus the
barrier's three `aux*` clauses, and it is the only place the domain is inspected. -/
theorem NameBarrier.dom (h : R.NameBarrier D K P) {n : Name} {v : VExpr}
    (hn : R.csubst D K n = some v) : P n := by
  obtain ⟨j, T, hT, hK, hd⟩ := csubst_dom hn
  obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨C, hC, rfl, -⟩ := hd
  · exact h.auxTy j T hT hK
  · exact h.auxRec j T hT hK
  · exact h.auxCtor j T hT hK C hC

/-- **The payoff: `SubstFree` from the barrier.**  No `env`, no `Faithful`, no `DomNodup` —
`SubstFree` is a pure name-separation fact and this exhibits it as one. -/
theorem NameBarrier.substFree (h : R.NameBarrier D K P) :
    R.SubstFree D (R.csubst D K) where
  tyName j := by
    cases hc : R.csubst D K (R.tyName j) with
    | none => rfl
    | some v => exact absurd (h.dom hc) (h.resTy j)
  tyArgs j a ha := (h.resArgs j a ha).noCSubst fun _ _ => h.dom
  recName j := by
    cases hc : R.csubst D K (R.recName (Lean.mkRecName (D.types.getD j default).name)) with
    | none => rfl
    | some v => exact absurd (h.dom hc) (h.resRec j)
  ctorName j T hT C hC := by
    cases hc : R.csubst D K (R.ctorName C.name) with
    | none => rfl
    | some v => exact absurd (h.dom hc) (h.resCtor j T hT C hC)

/-- …and therefore `KeysFree`, which `VInductDecl'.key_iotaRuleR_substC` reads the key off. -/
theorem NameBarrier.keysFree (h : R.NameBarrier D K P) : R.KeysFree D K :=
  h.substFree.keysFree

end VIndRestore

/-! ## 3. The concrete barrier: the reserved `_nested` prefix

The implementation's barrier is `Lean.Name.isPrefixOf `_nested`.  `ElimNestedInductive` builds
every auxiliary member's name as `mkUniqueName (`_nested ++ J_name)`
(`Lean4Lean/Inductive/Add.lean:841`) and every auxiliary constructor's as
`J_ctor_name.replacePrefix J_name auxJ_name` (`:855`), so the auxiliary family is inside; the
restored names are the real ones, which are outside **provided the declaration's own names are
not `_nested`-prefixed** — and *that is not checked*, here or in the C++ kernel.  §7 records
the measurement. -/

/-- `n` carries the kernel's reserved `_nested` prefix, component-wise.  This is exactly
`checkNoNestedAux`'s test (`Lean4Lean/Inductive/Add.lean:920`) and the C++ kernel's
`check_no_nested_aux` (`src/kernel/inductive.cpp:1222`), lifted from `Bool` to `Prop`. -/
def IsNestedName (n : Name) : Prop := (`_nested).isPrefixOf n = true

instance : DecidablePred IsNestedName := fun _ => inferInstanceAs (Decidable (_ = true))

namespace IsNestedName

@[simp] theorem nested : IsNestedName `_nested := rfl

@[simp] theorem not_anonymous : ¬ IsNestedName .anonymous := by decide

/-- `isPrefixOf` at a `.str` node unfolds to a disjunction, and this is it.  Note the left
disjunct: `.str .anonymous "_nested"` **is** `` `_nested ``, so the prefix can appear at the
node itself and not only in its parent. -/
theorem str_iff {p : Name} {s : String} :
    IsNestedName (.str p s) ↔ (Name.str p s = `_nested ∨ IsNestedName p) := by
  show (_ || _) = true ↔ _
  rw [Bool.or_eq_true, beq_iff_eq, IsNestedName]
  exact ⟨fun h => h.imp Eq.symm id, fun h => h.imp Eq.symm id⟩

theorem num_iff {p : Name} {i : Nat} : IsNestedName (.num p i) ↔ IsNestedName p := by
  show (_ || _) = true ↔ _
  rw [Bool.or_eq_true, beq_iff_eq]
  exact ⟨fun h => h.elim (fun h => absurd h (by simp)) id, .inr⟩

/-- The prefix survives an extra component — the direction `mkRecName` needs. -/
theorem str {p : Name} {s : String} (h : IsNestedName p) : IsNestedName (.str p s) :=
  str_iff.2 (.inr h)

/-- **`mkRecName` preserves the barrier**: `_nested.X.rec` is `_nested`-prefixed.  This is the
`auxRec` clause of every `NameBarrier` instance below. -/
theorem mkRecName {n : Name} (h : IsNestedName n) : IsNestedName (Lean.mkRecName n) := str h

/-- …and appending anything to `` `_nested `` **by `appendCore`** lands inside it. -/
theorem appendCore : ∀ {n : Name}, IsNestedName (Name.appendCore `_nested n)
  | .anonymous => nested
  | .str p _ => str (appendCore (n := p))
  | .num p _ => num_iff.2 (appendCore (n := p))

/-- **`mkUniqueName`'s `` `_nested ++ J_name `` is inside the barrier — when `J_name` carries no
macro scopes.**

The side condition is not an artefact.  `Lean.Name.append` is *not* `appendCore`: on a
macro-scoped argument it splits the scopes off with `extractMacroScopes`, appends to the base
and re-`review`s them (`Init/Prelude.lean`, `Name.append`).  The prefix does survive that —
`review` only adds components on top of the appended base — but establishing it needs
`extractMacroScopes`/`review` reasoning that this file does not carry, so the macro-scope-free
case is what is proved and §5.3's `auxTy` field is what covers the rest.  A name reaching
`ElimNestedInductive` from `Environment.addInductive` has passed
`Environment.checkNoMVarNoFVar`, which does *not* exclude macro scopes. -/
theorem append {n : Name} (h : n.hasMacroScopes = false) : IsNestedName (`_nested ++ n) := by
  show IsNestedName (Name.append _ _)
  rw [Name.append, show (`_nested).hasMacroScopes = false from by decide, h]
  exact appendCore

/-- `replacePrefix` never lands on `.anonymous` when the query really is a prefix and the
replacement is not itself anonymous — the base case the barrier's `.str` step needs. -/
theorem replacePrefix_ne_anonymous {p q newP : Name} (h : newP ≠ .anonymous)
    (hq : q.isPrefixOf p = true) : p.replacePrefix q newP ≠ .anonymous := by
  match p with
  | .anonymous =>
    have : q = .anonymous := by
      simpa using (beq_iff_eq (a := q) (b := .anonymous)).1 (by simpa [Name.isPrefixOf] using hq)
    subst this; rw [Name.replacePrefix]; exact h
  | .str p' s' => rw [Name.replacePrefix]; split <;> simp_all
  | .num p' i' => rw [Name.replacePrefix]; split <;> simp_all

/-- **The restored constructor name stays outside the barrier.**

`ElimNestedInductive.Result.restoreCtorName` is `c.replacePrefix auxI_name I`
(`Lean4Lean/Inductive/Add.lean:695-698`), so this is the clause `NameBarrier.resCtor` needs at
an auxiliary member.  Both side conditions are real: `hq` because `replacePrefix` is the
identity when the query is not a prefix (and then the result is the *auxiliary* name, which
**is** inside), and `hne` because `replacePrefix .anonymous .anonymous newP = newP` with
`newP = .anonymous` would let a `` `_nested `` component reappear at the base as
`.str .anonymous "_nested"`. -/
theorem replacePrefix : ∀ {n q newP : Name}, ¬ IsNestedName newP → newP ≠ .anonymous →
    q.isPrefixOf n = true → ¬ IsNestedName (n.replacePrefix q newP)
  | .anonymous, q, newP, hnew, _, hq => by
    have : q = .anonymous := by
      simpa using (beq_iff_eq (a := q) (b := .anonymous)).1 (by simpa [Name.isPrefixOf] using hq)
    subst this; rw [Name.replacePrefix]; exact hnew
  | .str p s, q, newP, hnew, hne, hq => by
    rw [Name.replacePrefix]
    split
    · exact hnew
    · rename_i hqne
      have hqp : q.isPrefixOf p = true := by
        rw [Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at hq
        exact hq.resolve_left fun h => hqne (by simp [h])
      refine fun h => ?_
      rcases str_iff.1 h with h | h
      · rw [show (`_nested : Name) = .str .anonymous "_nested" from rfl,
            Name.str.injEq] at h
        exact replacePrefix_ne_anonymous hne hqp h.1
      · exact replacePrefix (n := p) hnew hne hqp h
  | .num p i, q, newP, hnew, hne, hq => by
    rw [Name.replacePrefix]
    split
    · exact hnew
    · rename_i hqne
      have hqp : q.isPrefixOf p = true := by
        rw [Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at hq
        exact hq.resolve_left fun h => hqne (by simp [h])
      exact fun h => replacePrefix (n := p) hnew hne hqp (num_iff.1 h)

end IsNestedName

/-- The barrier at the reserved prefix — the instance the implementation supplies. -/
abbrev VIndRestore.NestedBarrier (R : VIndRestore) (D : VInductDecl') (K : List Name) : Prop :=
  R.NameBarrier D K IsNestedName

/-! ### `mkRecName` is transparent to the barrier

`IsNestedName (n.rec)` is `IsNestedName n`: the extra component cannot *create* the prefix,
because `` `_nested `` is `.str .anonymous "_nested"` and `"rec" ≠ "_nested"`.  Both directions
are used — `→` for the auxiliary recursors' membership, `←` for the declared ones' absence. -/
theorem IsNestedName.mkRecName_iff {n : Name} :
    IsNestedName (Lean.mkRecName n) ↔ IsNestedName n := by
  refine ⟨fun h => (str_iff.1 h).resolve_left fun h => ?_, str⟩
  rw [show (`_nested : Name) = .str .anonymous "_nested" from rfl, Name.str.injEq] at h
  exact absurd h.2 (by decide)

/-! ## 4. Two association-list facts

`mkRestore`'s two renaming fields are `List.lookup … |>.getD`, so the barrier proof needs
exactly two things about a lookup: it *misses* a key no domain entry matches, and when it
*hits* the value is one the list actually contains. -/

namespace List
variable {α β : Type _} [BEq α] [LawfulBEq α]

/-- A lookup misses whenever the key fails a property every domain entry has. -/
theorem lookup_eq_none_of_forall {P : α → Prop} {l : List (α × β)}
    (hd : ∀ p ∈ l, P p.1) {n : α} (hn : ¬ P n) : l.lookup n = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.lookup_cons]
    have hne : (n == a.1) = false := by
      cases h : n == a.1
      · rfl
      · exact absurd (by rw [eq_of_beq h]; exact hd a List.mem_cons_self) hn
    rw [hne]
    exact ih fun p hp => hd p (List.mem_cons_of_mem _ hp)

/-- `(l.lookup n).getD n` is either `n` itself or the value of an entry `l` really holds. -/
theorem lookup_getD_cases {l : List (Lean.Name × β)} {n : Lean.Name} {d : β} :
    (l.lookup n).getD d = d ∨ ∃ p ∈ l, (l.lookup n).getD d = p.2 := by
  cases h : l.lookup n with
  | none => exact .inl rfl
  | some v => exact .inr ⟨(n, v), Lean4Lean.List.lookup_mem h, rfl⟩

end List

/-! ## 5. The construction

`ElimNestedInductive.Result` carries everything the restoration's **name** fields need:
`aux2nested` maps each auxiliary member's name to the nested application `J As` it stands for
(open over `r.params`), and `types` is the user's block followed by the auxiliary tail.  The two
*semantic* fields — `tyLvls` and `tyArgs` — are `List VLevel`/`List VExpr`, and the checker
holds `Lean.Level`/`Lean.Expr`; there is no translation *function* (`TrExprS` is a relation), so
they are parameters here, defaulted to the identity presentation on the members the user wrote.
That split is what makes `OwnId` provable outright rather than assumed. -/

namespace ElimNestedInductive.Result

variable (r : Result)

/-- **`K`.**  The auxiliary members' names, read off `aux2nested`'s domain.  `run` builds
`aux2nested` by folding `nestedAux`, which `replaceIfNested` pushes in lockstep with
`newTypes`, so as a *set* this is the tail `r.types.drop types.length` — which is the form
`TrIndDeclN.companions` compares against. -/
def companionNames : List Name := r.aux2nested.map (·.1)

/-- The head constant of the nested application member `n` is presented as: `List` for
`_nested.List_1`.  This is `restoreCtorName`'s `let .const I _ := e.getAppFn` (`Add.lean:697`)
and `restoreNested`'s `nested'.withApp fun I …` (`:730`), as a total function. -/
def presentedHead (n : Name) : Name :=
  match r.aux2nested.lookup n with
  | some e => match e.getAppFn with
    | .const c _ => c
    | _ => n
  | none => n

/-- **`ctorName`, as an association list.**  `Result.restoreCtorName` reads the auxiliary
member off `env'.find? c |>.induct`; this reads it off `r.types` instead, which agrees whenever
`env'` is the environment `AddInductive.run` produced from `r.types` (there `ctorInfo.induct` is
the member's name) and needs no `Environment`. -/
def ctorRenames (nt : Nat) : List (Name × Name) :=
  (r.types.drop nt).flatMap fun T =>
    T.ctors.map fun C => (C.name, C.name.replacePrefix T.name (r.presentedHead T.name))

/-- **`recName`, as an association list** — `mkAuxRecNameMap` (`Add.lean:901-918`) without the
`Environment` detour.  `mkAuxRecNameMap` reads the auxiliary tail off `mainInfo.all` and names
the `k`-th renamed recursor `appendIndexAfter' (mkRecName mainName) (k+1)`, which is exactly
`auxRecName types k` (`Verify/Environment/InductR.lean:238`); `mainInfo.all` is the block's own
name list, i.e. `r.types.map (·.name)`. -/
def recRenames (types : List Lean.InductiveType) : List (Name × Name) :=
  (r.types.drop types.length).zipIdx.map fun (T, k) => (Lean.mkRecName T.name, auxRecName types k)

/-- **The restoration the checker's data determines.**

`uvars`/`np` are the block's, `tyLvls`/`tyArgs` are the presented level list and parameter
spine at an *auxiliary* member — the two pieces that live in the abstract term language and so
cannot be computed from `Lean.Expr`.  On a member the user wrote every field is the identity
presentation, which is `VIndRestore.OwnId` and is proved, not assumed
(`mkRestore_ownId`). -/
def mkRestore (types : List Lean.InductiveType) (uvars np : Nat)
    (tyLvls : Nat → List VLevel) (tyArgs : Nat → List VExpr) : VIndRestore where
  tyName j :=
    match r.types[j]? with
    | none => .anonymous
    | some T => if j < types.length then T.name else r.presentedHead T.name
  tyLvls j := if j < types.length then VLevel.params uvars else tyLvls j
  tyArgs j := if j < types.length then VExpr.bvars 0 np else tyArgs j
  ctorName c := ((r.ctorRenames types.length).lookup c).getD c
  recName n := ((r.recRenames types).lookup n).getD n

end ElimNestedInductive.Result

/-! ## 6. What the construction proves

`RestoreData` collects the implementation-side facts the proofs consume.  Every field is a
statement about names the checker computes, `decide`-able at a concrete block; §7 records which
are already true of `ElimNestedInductive.run` and which need `checkNoNestedAux` extended. -/

namespace ElimNestedInductive.Result

/-- Membership in a `drop` gives an index at or past the cut. -/
theorem mem_drop_getElem? {α : Type _} {l : List α} {n : Nat} {a : α} (h : a ∈ l.drop n) :
    ∃ i, n ≤ i ∧ l[i]? = some a := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  refine ⟨n + i, Nat.le_add_right .., ?_⟩
  rwa [List.getElem?_drop] at hi

/-- …and conversely, an index at or past the cut is in the `drop`. -/
theorem getElem?_mem_drop {α : Type _} {l : List α} {n i : Nat} {a : α}
    (hi : n ≤ i) (h : l[i]? = some a) : a ∈ l.drop n := by
  refine List.mem_iff_getElem?.2 ⟨i - n, ?_⟩
  rw [List.getElem?_drop, show n + (i - n) = i from by omega]; exact h

/-- **The facts about the checker's names that the construction's proofs consume.**

Split into three groups: the correspondence between `r.types` and `D.types` (`len`, `name`,
`ctor`, `companions`), the auxiliary tail's name shape (`auxName`, `auxCtor*`, `auxNodup`), and
the *declared* members' and the restored heads' avoidance of the reserved prefix (`ownName`,
`ownCtor`, `head*`, `auxRec`).

**Only the third group is not already established by `ElimNestedInductive`** — see §7. -/
structure RestoreData (r : Result) (types : List Lean.InductiveType) (D : VInductDecl')
    (K : List Name) (tyArgs : Nat → List VExpr) : Prop where
  len : r.types.length = D.types.length
  name : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
    ∀ t, r.types[j]? = some t → t.name = T.name
  ctor : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → ∀ t, r.types[j]? = some t →
    ∀ C ∈ T.ctors, ∃ c ∈ t.ctors, c.name = C.name
  companions : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
    (T.name ∈ K ↔ types.length ≤ j)
  /-- `mkUniqueName (`_nested ++ J_name)`. -/
  auxName : ∀ (j : Nat) t, r.types[j]? = some t → types.length ≤ j → IsNestedName t.name
  /-- `J_ctor_name.replacePrefix J_name auxJ_name`. -/
  auxCtorName : ∀ (j : Nat) t, r.types[j]? = some t → types.length ≤ j →
    ∀ c ∈ t.ctors, IsNestedName c.name
  /-- …and the auxiliary member's name really is a prefix of its constructors' — which is what
  makes `restoreCtorName`'s `replacePrefix` a rename rather than the identity. -/
  auxCtorPrefix : ∀ (j : Nat) t, r.types[j]? = some t → types.length ≤ j →
    ∀ c ∈ t.ctors, t.name.isPrefixOf c.name = true
  /-- `mkUniqueName`'s output is pairwise distinct. -/
  auxNodup : ((r.types.drop types.length).map (·.name)).Nodup
  /-- **Not checked by the implementation.**  §7. -/
  ownName : ∀ (j : Nat) t, r.types[j]? = some t → j < types.length → ¬ IsNestedName t.name
  /-- **Not checked by the implementation.**  §7. -/
  ownCtor : ∀ (j : Nat) t, r.types[j]? = some t → j < types.length →
    ∀ c ∈ t.ctors, ¬ IsNestedName c.name
  head : ∀ (j : Nat) t, r.types[j]? = some t → types.length ≤ j →
    ¬ IsNestedName (r.presentedHead t.name)
  headNe : ∀ (j : Nat) t, r.types[j]? = some t → types.length ≤ j →
    r.presentedHead t.name ≠ .anonymous
  auxRec : ∀ k, ¬ IsNestedName (auxRecName types k)
  args : ∀ j, ∀ a ∈ tyArgs j, a.NoConstIn IsNestedName

namespace RestoreData
variable {r : Result} {types : List Lean.InductiveType} {D : VInductDecl'} {K : List Name}
  {ls : Nat → List VLevel} {as : Nat → List VExpr}
  (h : r.RestoreData types D K as)

include h

/-- The member of `r.types` matching a member of `D.types`. -/
theorem get {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) :
    ∃ t, r.types[j]? = some t ∧ t.name = T.name := by
  have hj : j < r.types.length := by
    rw [h.len]; exact List.getElem?_eq_some_iff.1 hT |>.1
  obtain ⟨t, ht⟩ := exists_getElem?_of_lt hj
  exact ⟨t, ht, h.name j T hT t ht⟩

/-- **Every key of the recursor renaming is inside the barrier.** -/
theorem recRenames_dom : ∀ p ∈ r.recRenames types, IsNestedName p.1 := by
  intro p hp
  rw [Result.recRenames, List.mem_map] at hp
  obtain ⟨⟨t, k⟩, hk, rfl⟩ := hp
  have hk' : r.types[types.length + k]? = some t := by
    have := List.mk_mem_zipIdx_iff_getElem?.1 hk
    rwa [List.getElem?_drop] at this
  exact IsNestedName.mkRecName_iff.2 (h.auxName _ t hk' (Nat.le_add_right ..))

/-- **Every key of the constructor renaming is inside the barrier.** -/
theorem ctorRenames_dom : ∀ p ∈ r.ctorRenames types.length, IsNestedName p.1 := by
  intro p hp
  rw [Result.ctorRenames, List.mem_flatMap] at hp
  obtain ⟨t, ht, hp⟩ := hp
  rw [List.mem_map] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  obtain ⟨i, hi, hit⟩ := mem_drop_getElem? ht
  exact h.auxCtorName i t hit hi c hc

/-- **Every *value* of the constructor renaming is outside it** — `IsNestedName.replacePrefix`
at the presented head. -/
theorem ctorRenames_val : ∀ p ∈ r.ctorRenames types.length, ¬ IsNestedName p.2 := by
  intro p hp
  rw [Result.ctorRenames, List.mem_flatMap] at hp
  obtain ⟨t, ht, hp⟩ := hp
  rw [List.mem_map] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  obtain ⟨i, hi, hit⟩ := mem_drop_getElem? ht
  exact IsNestedName.replacePrefix (h.head i t hit hi) (h.headNe i t hit hi)
    (h.auxCtorPrefix i t hit hi c hc)

/-- …and every value of the recursor renaming is `auxRecName`, hence outside it. -/
theorem recRenames_val : ∀ p ∈ r.recRenames types, ¬ IsNestedName p.2 := by
  intro p hp
  rw [Result.recRenames, List.mem_map] at hp
  obtain ⟨⟨t, k⟩, -, rfl⟩ := hp
  exact h.auxRec k

end RestoreData
end ElimNestedInductive.Result

namespace List
/-- A key the list holds really is found. -/
theorem exists_lookup_of_mem {β : Type _} : ∀ {l : List (Lean.Name × β)} {p : Lean.Name × β},
    p ∈ l → ∃ v, l.lookup p.1 = some v
  | (a, b) :: l, p, hp => by
    rw [List.lookup_cons]
    cases hb : p.1 == a
    · rcases List.mem_cons.1 hp with rfl | hp'
      · exact absurd hb (by simp)
      · exact exists_lookup_of_mem hp'
    · exact ⟨b, rfl⟩

/-- An injective image of a `Nodup` list is `Nodup`.  (Local: `List.Nodup.map` is a `Mathlib`
lemma and this file's import chain does not reach it.) -/
theorem nodup_map_of_inj {α β : Type _} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj hf hnd.2⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.1 hm
    cases hf b a he
    exact hnd.1 hb
end List

namespace ElimNestedInductive.Result
namespace RestoreData
variable {r : Result} {types : List Lean.InductiveType} {D : VInductDecl'} {K : List Name}
  {ls : Nat → List VLevel} {as : Nat → List VExpr}
  (h : r.RestoreData types D K as)

include h

/-- A `D`-member off `K` sits before the cut, and its `r`-counterpart's names avoid the
barrier — the shape every `OwnId` field's lookup argument needs. -/
theorem off {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∉ K) :
    ∃ t, r.types[j]? = some t ∧ t.name = T.name ∧ j < types.length := by
  obtain ⟨t, ht, hn⟩ := h.get hT
  exact ⟨t, ht, hn, Nat.lt_of_not_le fun hle => hK ((h.companions j T hT).2 hle)⟩

/-- …and a `D`-member on `K` sits at or past it. -/
theorem on {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    ∃ t, r.types[j]? = some t ∧ t.name = T.name ∧ types.length ≤ j := by
  obtain ⟨t, ht, hn⟩ := h.get hT
  exact ⟨t, ht, hn, (h.companions j T hT).1 hK⟩

/-- **`VIndRestore.OwnId` for the construction.**  The restoration is the identity on every
member the step declares: this is what makes `VEnv.addInductR` agree with `addInduct'` on the
user's block, and it is the field `AddInductiveStep.lean:408` got for free from `idRestore`. -/
theorem mkRestore_ownId : (r.mkRestore types D.uvars D.np ls as).OwnId D K where
  tyName j T hT hK := by
    obtain ⟨t, ht, hn, hj⟩ := h.off hT hK
    simp only [Result.mkRestore, ht, if_pos hj]; exact hn
  tyLvls j T hT hK := by
    obtain ⟨t, ht, -, hj⟩ := h.off hT hK
    simp only [Result.mkRestore, if_pos hj]; rfl
  tyArgs j T hT hK := by
    obtain ⟨t, ht, -, hj⟩ := h.off hT hK
    simp only [Result.mkRestore, if_pos hj]
  recName j T hT hK := by
    obtain ⟨t, ht, hn, hj⟩ := h.off hT hK
    simp only [Result.mkRestore]
    rw [← hn, List.lookup_eq_none_of_forall h.recRenames_dom
      (fun hx => h.ownName j t ht hj (IsNestedName.mkRecName_iff.1 hx))]
    rfl
  ctorName j T hT hK C hC := by
    obtain ⟨t, ht, -, hj⟩ := h.off hT hK
    obtain ⟨c, hc, hcn⟩ := h.ctor j T hT t ht C hC
    simp only [Result.mkRestore]
    rw [← hcn, List.lookup_eq_none_of_forall h.ctorRenames_dom (h.ownCtor j t ht hj c hc)]
    rfl

/-- **`TrIndDeclN.recName_own`** — a member the user wrote keeps its recursor name. -/
theorem mkRestore_recName_own {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    (hK : T.name ∉ K) :
    (r.mkRestore types D.uvars D.np ls as).recName (Lean.mkRecName T.name)
      = Lean.mkRecName T.name :=
  (h.mkRestore_ownId (ls := ls) (as := as)).recName j T hT hK

/-- …in the exact shape `TrIndDeclN.recName_own` states it, against the input list's member. -/
theorem mkRestore_recName_own' {j : Nat} {T : VIndType} {t : Lean.InductiveType}
    (hT : D.types[j]? = some T) (hK : T.name ∉ K) (hn : t.name = T.name) :
    (r.mkRestore types D.uvars D.np ls as).recName (Lean.mkRecName T.name)
      = Lean.mkRecName t.name := by
  rw [hn]; exact h.mkRestore_recName_own hT hK

/-- The domain keys of the recursor renaming, as a list — the form the `Nodup` transfer needs. -/
theorem recRenames_keys :
    (r.recRenames types).map (·.1)
      = (r.types.drop types.length).map (fun T => Lean.mkRecName T.name) := by
  rw [Result.recRenames, List.map_map,
    show ((fun p : Lean.Name × Lean.Name => p.1) ∘
        fun q : Lean.InductiveType × Nat => (Lean.mkRecName q.1.name, auxRecName types q.2))
      = ((fun T : Lean.InductiveType => Lean.mkRecName T.name) ∘
          fun q : Lean.InductiveType × Nat => q.1) from rfl,
    ← List.map_map, List.zipIdx_map_fst]

theorem recRenames_nodup : ((r.recRenames types).map (·.1)).Nodup := by
  rw [h.recRenames_keys,
    show (fun T : Lean.InductiveType => Lean.mkRecName T.name)
      = (fun n : Lean.Name => Lean.mkRecName n) ∘ (fun T : Lean.InductiveType => T.name) from rfl,
    ← List.map_map]
  exact List.nodup_map_of_inj (fun _ _ => Lean4Lean.mkRecName_inj) h.auxNodup

/-- **`TrIndDeclN.recName_aux`** — an auxiliary member's recursor is renamed to
`mkAuxRecNameMap`'s `I.rec_k`.  This is the one clause where the `Nodup` of `mkUniqueName`'s
output is load-bearing: without it `List.lookup` could return an earlier entry. -/
theorem mkRestore_recName_aux {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    (hle : types.length ≤ j) :
    (r.mkRestore types D.uvars D.np ls as).recName (Lean.mkRecName T.name)
      = auxRecName types (j - types.length) := by
  obtain ⟨t, ht, hn⟩ := h.get hT
  have hmem : (Lean.mkRecName t.name, auxRecName types (j - types.length))
      ∈ r.recRenames types := by
    refine List.mem_map.2 ⟨(t, j - types.length), List.mk_mem_zipIdx_iff_getElem?.2 ?_, rfl⟩
    rw [List.getElem?_drop, show types.length + (j - types.length) = j from by omega]
    exact ht
  simp only [Result.mkRestore]
  rw [← hn, List.lookup_eq_some_of_nodup h.recRenames_nodup hmem]
  rfl

/-- **The barrier for the construction** — hence `SubstFree` and `KeysFree`, by
`VIndRestore.NameBarrier.substFree`.

Read the seven clauses against the seven `RestoreData` fields they use: the three `aux*` ones
are `auxName`/`auxCtorName` transported through the `r`↔`D` correspondence, the three `res*`
ones are `ownName`/`ownCtor` before the cut and `head`/`auxRec`/`ctorRenames_val` after it, and
`resArgs` is `noConstIn_bvars` before the cut and `args` after. -/
theorem mkRestore_nestedBarrier :
    (r.mkRestore types D.uvars D.np ls as).NestedBarrier D K where
  auxTy j T hT hK := by
    obtain ⟨t, ht, hn, hle⟩ := h.on hT hK
    exact hn ▸ h.auxName j t ht hle
  auxRec j T hT hK := by
    obtain ⟨t, ht, hn, hle⟩ := h.on hT hK
    exact IsNestedName.mkRecName_iff.2 (hn ▸ h.auxName j t ht hle)
  auxCtor j T hT hK C hC := by
    obtain ⟨t, ht, -, hle⟩ := h.on hT hK
    obtain ⟨c, hc, hcn⟩ := h.ctor j T hT t ht C hC
    exact hcn ▸ h.auxCtorName j t ht hle c hc
  resTy j := by
    simp only [Result.mkRestore]
    cases ht : r.types[j]? with
    | none => exact IsNestedName.not_anonymous
    | some t =>
      show ¬ IsNestedName (if j < types.length then t.name else r.presentedHead t.name)
      by_cases hj : j < types.length
      · rw [if_pos hj]; exact h.ownName j t ht hj
      · rw [if_neg hj]; exact h.head j t ht (Nat.le_of_not_lt hj)
  resRec j := by
    simp only [Result.mkRestore]
    by_cases hx : IsNestedName (Lean.mkRecName (D.types.getD j default).name)
    · -- the key is inside the barrier, so `j` is an auxiliary member and the lookup hits
      have hlt : j < D.types.length := by
        by_contra hge
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hx
        exact absurd (IsNestedName.mkRecName_iff.1 hx) IsNestedName.not_anonymous
      obtain ⟨T, hT⟩ := exists_getElem?_of_lt hlt
      have hgd : D.types.getD j default = T := by rw [List.getD_eq_getElem?_getD, hT]; rfl
      obtain ⟨t, ht, hn⟩ := h.get hT
      have hle : types.length ≤ j := by
        by_contra hj
        rw [hgd, ← hn] at hx
        exact h.ownName j t ht (Nat.lt_of_not_le hj) (IsNestedName.mkRecName_iff.1 hx)
      have hmem : (Lean.mkRecName t.name, auxRecName types (j - types.length))
          ∈ r.recRenames types := by
        refine List.mem_map.2 ⟨(t, j - types.length), List.mk_mem_zipIdx_iff_getElem?.2 ?_, rfl⟩
        rw [List.getElem?_drop, show types.length + (j - types.length) = j from by omega]
        exact ht
      rw [hgd, ← hn, List.lookup_eq_some_of_nodup h.recRenames_nodup hmem]
      exact h.auxRec _
    · rw [List.lookup_eq_none_of_forall h.recRenames_dom hx]; exact hx
  resCtor j T hT C hC := by
    simp only [Result.mkRestore]
    by_cases hx : IsNestedName C.name
    · -- inside the barrier: `j` is auxiliary, so the lookup hits and the value is restored
      obtain ⟨t, ht, -⟩ := h.get hT
      obtain ⟨c, hc, hcn⟩ := h.ctor j T hT t ht C hC
      have hle : types.length ≤ j := by
        by_contra hj
        exact h.ownCtor j t ht (Nat.lt_of_not_le hj) c hc (hcn ▸ hx)
      have hmem : (c.name, c.name.replacePrefix t.name (r.presentedHead t.name))
          ∈ r.ctorRenames types.length :=
        List.mem_flatMap.2 ⟨t, getElem?_mem_drop hle ht, List.mem_map.2 ⟨c, hc, rfl⟩⟩
      obtain ⟨v, hv⟩ := List.exists_lookup_of_mem hmem
      rw [← hcn, hv]
      exact h.ctorRenames_val _ (Lean4Lean.List.lookup_mem hv)
    · rw [List.lookup_eq_none_of_forall h.ctorRenames_dom hx]; exact hx
  resArgs j a ha := by
    simp only [Result.mkRestore] at ha
    by_cases hj : j < types.length
    · rw [if_pos hj] at ha; exact VExpr.noConstIn_bvars a ha
    · rw [if_neg hj] at ha; exact h.args j a ha

/-- …and therefore `VIndRestore.SubstFree` at the construction — the obligation
`Theory/Inductive/NestedRules.lean` §7.4 leaves to the caller and that nothing in the tree could
discharge for a block the implementation actually produces. -/
theorem mkRestore_substFree :
    (r.mkRestore types D.uvars D.np ls as).SubstFree D
      ((r.mkRestore types D.uvars D.np ls as).csubst D K) :=
  h.mkRestore_nestedBarrier.substFree

/-- …and `VIndRestore.KeysFree`, which `VInductDecl'.key_iotaRuleR_substC` reads the ι-rule's
key off. -/
theorem mkRestore_keysFree :
    (r.mkRestore types D.uvars D.np ls as).KeysFree D K :=
  h.mkRestore_nestedBarrier.keysFree

/-- **The premise ordering is satisfiable.**

A sibling stream proposed adding `VIndRestore.SubstFree` as a conjunct of `VEnv.AddNested` /
`VInductDecl'.Built`, and the ruling against it was that the implementation-side discharge comes
first.  That ruling set an unsatisfiable precondition only for as long as no construction
existed.  This is the discharge, in the shape such a conjunct would take: from the checker's own
`ElimNestedInductive.Result` there is a `K` and an `R` satisfying all four name-discipline
obligations at once.

What is *still* owed for a full `VEnv.AddNested` is `Faithful` and `Canonical` — neither is a
name-discipline fact (see this file's header), and neither is reachable from `RestoreData`. -/
theorem mkRestore_discipline :
    (r.mkRestore types D.uvars D.np ls as).OwnId D K ∧
      (r.mkRestore types D.uvars D.np ls as).NestedBarrier D K ∧
      (r.mkRestore types D.uvars D.np ls as).SubstFree D
        ((r.mkRestore types D.uvars D.np ls as).csubst D K) ∧
      (r.mkRestore types D.uvars D.np ls as).KeysFree D K :=
  ⟨h.mkRestore_ownId, h.mkRestore_nestedBarrier, h.mkRestore_substFree, h.mkRestore_keysFree⟩

end RestoreData
end ElimNestedInductive.Result

/-! ## 7. `NameBarrier` bounded both ways, field by field

`docs/vacuity-ledger.md` rows 11/11a: a two-way bound on a *structure* has to be checked field
by field, because a positive witness at a degenerate configuration can leave the one broken
field untested.  §7.1 is the positive bound — all seven fields at the nested witness the tree
already carries.  §7.2 refutes each of the four `res*` fields at a one-field override of that
same witness, and shows `SubstFree` false at each; §7.3 does the `aux*` group by moving `K`
instead of `R`.

`NameBarrier` also is **not** `K`-vacuous, which is the specific defect
`VIndRestore.faithful_of_nil` records of `Faithful`: the four `res*` clauses do not mention `K`
at all, so they have content at `K = []` (§7.4). -/

namespace InductiveDeclExamples
open VIndRestore

/-! ### 7.1 The positive bound: the barrier holds at the nested witness -/

/-- **All seven fields, at `nfnRestore`/`nfnAux`/`nfnK`.**  `nfnK = [`_nested.PFn_1]` is inside
the barrier and every name `nfnRestore` produces — `NFn`, `PFn`, `NFn.rec`, `NFn.rec_1`,
`PFn.mk`, `NFn.node` — is outside it. -/
theorem nfnRestore_nestedBarrier : nfnRestore.NestedBarrier nfnAux nfnK where
  auxTy := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; decide
    · simp [nfnAux] at hT
  auxRec := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; decide
    · simp [nfnAux] at hT
  auxCtor := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT; exact absurd hK (by decide)
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; decide
    · simp [nfnAux] at hT
  resTy j := by by_cases hj : j = 1 <;> simp only [nfnRestore, hj] <;> decide
  resRec := by
    rintro (_ | _ | j)
    · decide
    · decide
    · exact show ¬ IsNestedName
        (nfnRestore.recName (Lean.mkRecName (default : VIndType).name)) from by decide
  resCtor := by
    rintro (_ | _ | j) T hT C hC
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; decide
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; decide
    · simp [nfnAux] at hT
  resArgs j a ha := by
    by_cases hj : j = 1
    · rw [show nfnRestore.tyArgs j = [.const ``NFn []] from by simp [nfnRestore, hj]] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha; decide
    · rw [show nfnRestore.tyArgs j = [] from by simp [nfnRestore, hj]] at ha
      exact absurd ha nofun

/-- **The barrier route reproduces the hand proof.**  `nfnRestore_substFree`
(`Theory/Inductive/NestedRules.lean` §7.8) is four `decide`-style field proofs; this is the same
statement out of `NameBarrier.substFree`, so the abstract route is not weaker than the
witness-by-witness one it is meant to replace. -/
theorem nfnRestore_substFree' :
    nfnRestore.SubstFree nfnAux (nfnRestore.csubst nfnAux nfnK) :=
  nfnRestore_nestedBarrier.substFree

/-- …and the same at the *junk* restoration, which `nfnJunk_substFree` also establishes by hand.
`nfnJunkRestore` presents the declared member `NFn` as `Nat`, which is outside the barrier, so
the barrier does not see the `OwnId` violation — correctly: `SubstFree` is not about `OwnId`. -/
theorem nfnJunkRestore_nestedBarrier : nfnJunkRestore.NestedBarrier nfnAux nfnK where
  auxTy := nfnRestore_nestedBarrier.auxTy
  auxRec := nfnRestore_nestedBarrier.auxRec
  auxCtor := nfnRestore_nestedBarrier.auxCtor
  resTy j := by by_cases hj : j = 1 <;> simp only [nfnJunkRestore, nfnRestore, hj] <;> decide
  resRec := nfnRestore_nestedBarrier.resRec
  resCtor := nfnRestore_nestedBarrier.resCtor
  resArgs j a ha := nfnRestore_nestedBarrier.resArgs j a (nfnJunk_tyArgs_eq ▸ ha)

/-! ### 7.2 The negative bound on the four `res*` fields

Each override changes **one** field of `nfnRestore` to an auxiliary name, refutes exactly that
field of the barrier, and refutes the matching clause of `SubstFree`.  So none of the four is
decoration, and the barrier is not implied by the rest of the configuration. -/

/-- `resTy` broken: the presented *type* head is the auxiliary name itself. -/
def nfnBarrierJunkTy : VIndRestore := { nfnRestore with tyName := fun _ => `_nested.PFn_1 }

theorem nfnBarrierJunkTy_not_barrier : ¬ nfnBarrierJunkTy.NestedBarrier nfnAux nfnK :=
  fun h => h.resTy 0 (by decide)

theorem nfnBarrierJunkTy_not_substFree :
    ¬ nfnBarrierJunkTy.SubstFree nfnAux (nfnBarrierJunkTy.csubst nfnAux nfnK) :=
  fun h => absurd (h.tyName 0) (by decide)

/-- `resRec` broken: the presented *recursor* head is the auxiliary recursor's name. -/
def nfnBarrierJunkRec : VIndRestore :=
  { nfnRestore with recName := fun _ => `_nested.PFn_1.rec }

theorem nfnBarrierJunkRec_not_barrier : ¬ nfnBarrierJunkRec.NestedBarrier nfnAux nfnK :=
  fun h => h.resRec 0 (by decide)

theorem nfnBarrierJunkRec_not_substFree :
    ¬ nfnBarrierJunkRec.SubstFree nfnAux (nfnBarrierJunkRec.csubst nfnAux nfnK) :=
  fun h => absurd (h.recName 0) (by decide)

/-- `resCtor` broken: the presented *constructor* head is the auxiliary constructor's name. -/
def nfnBarrierJunkCtor : VIndRestore :=
  { nfnRestore with ctorName := fun _ => `_nested.PFn_1.mk }

theorem nfnBarrierJunkCtor_not_barrier : ¬ nfnBarrierJunkCtor.NestedBarrier nfnAux nfnK :=
  fun h => h.resCtor 0 _ rfl nfnNode List.mem_cons_self (by decide)

theorem nfnBarrierJunkCtor_not_substFree :
    ¬ nfnBarrierJunkCtor.SubstFree nfnAux (nfnBarrierJunkCtor.csubst nfnAux nfnK) :=
  fun h => absurd (h.ctorName 0 _ rfl nfnNode List.mem_cons_self) (by decide)

/-- `resArgs` broken: the presented parameter *spine* mentions an auxiliary constant.  This is
the field `KeysFree` has no counterpart for — it is about `VExpr` subterms, not names. -/
def nfnBarrierJunkArgs : VIndRestore :=
  { nfnRestore with tyArgs := fun _ => [.const `_nested.PFn_1 []] }

theorem nfnBarrierJunkArgs_not_barrier : ¬ nfnBarrierJunkArgs.NestedBarrier nfnAux nfnK :=
  fun h => h.resArgs 0 (.const `_nested.PFn_1 []) List.mem_cons_self (by decide)

theorem nfnBarrierJunkArgs_not_substFree :
    ¬ nfnBarrierJunkArgs.SubstFree nfnAux (nfnBarrierJunkArgs.csubst nfnAux nfnK) :=
  fun h => absurd (h.tyArgs 0 (.const `_nested.PFn_1 []) List.mem_cons_self) (by decide)

/-! ### 7.3 The negative bound on the `aux*` group

These three clauses are about `K`, not about `R`, so the witness moves `K` instead: presenting
the *declared* member `NFn` as a companion puts a non-`_nested` name in `csubst`'s domain, all
four `res*` clauses still hold (they do not mention `K`), and `SubstFree.tyName` is false.  One
witness refutes all three, which is why they are not bounded separately. -/

/-- `K` naming the declared member instead of the auxiliary one. -/
def nfnBadK : List Lean.Name := [``NFn]

theorem nfnBadK_not_barrier : ¬ nfnRestore.NestedBarrier nfnAux nfnBadK :=
  fun h => absurd (h.auxTy 0 _ rfl (by decide)) (by decide)

theorem nfnBadK_not_substFree :
    ¬ nfnRestore.SubstFree nfnAux (nfnRestore.csubst nfnAux nfnBadK) :=
  fun h => absurd (h.tyName 0) (by decide)

/-- …and the four `res*` clauses are untouched by the move, so the refutation really is
localised in the `aux*` group. -/
theorem nfnBadK_res_still_hold :
    (∀ j, ¬ IsNestedName (nfnRestore.tyName j)) ∧
    (∀ j, ¬ IsNestedName (nfnRestore.recName (Lean.mkRecName (nfnAux.types.getD j default).name))) :=
  ⟨nfnRestore_nestedBarrier.resTy, nfnRestore_nestedBarrier.resRec⟩

/-! ### 7.4 The barrier is not `K`-vacuous

`VIndRestore.faithful_of_nil` says `Faithful` holds of **every** restoration at `K = []`, which
is the defect `OwnId` was introduced to cover.  `NameBarrier` does not have that shape: its
`res*` clauses are unguarded, so at `K = []` it still forbids a restoration from presenting a
member under an auxiliary name. -/
theorem not_nestedBarrier_nil : ¬ nfnBarrierJunkTy.NestedBarrier nfnAux [] :=
  fun h => h.resTy 0 (by decide)

/-- …while `SubstFree` *is* free at `K = []`, since the substitution is empty.  So the barrier
is **strictly stronger** than the obligation it discharges, and the gap is deliberate: it is
what makes the barrier a property of `R` alone that survives `K` growing. -/
theorem substFree_nil (R : VIndRestore) (D : VInductDecl') :
    R.SubstFree D (R.csubst D []) where
  tyName _ := by rw [R.csubst_nil D]; rfl
  tyArgs _ a _ := by rw [R.csubst_nil D]; exact VExpr.noCSubst_id a
  recName _ := by rw [R.csubst_nil D]; rfl
  ctorName _ _ _ _ _ := by rw [R.csubst_nil D]; rfl

end InductiveDeclExamples


/-! ## 8. The residue, measured

### 8.1 `RestoreData`, field by field

`RestoreData` has fourteen fields.  Nine are facts `ElimNestedInductive.run` establishes by
construction (they need a `run`-level invariant proof, not a new check); two — `ownName` and
`ownCtor` — are established **nowhere**, here or in the C++ kernel; and three more (`head`,
`headNe`, `auxRec`) rest on the same missing check, since they are about names the *environment*
holds and about the main type's own name.

| field | status |
| --- | --- |
| `len`, `name`, `ctor` | the `r.types`↔`D.types` correspondence.  `run` seeds `newTypes` with `types.toArray` and only ever `set!`s a member's **`ctors`** (`Add.lean:869`), replacing each `ctor` by `{ ctor with type := … }` — so names are preserved at every index.  Needs a `run`-level invariant proof, not a new check. |
| `companions` | `TrIndDeclN.companions`, already a clause of the translation relation. |
| `auxName` | `mkUniqueName (`_nested ++ J_name)` (`Add.lean:841`).  `IsNestedName.append` proves it **when `J_name` carries no macro scopes**; the macro-scoped case needs `extractMacroScopes`/`review` reasoning (`Lean.Name.append` is not `appendCore`). |
| `auxCtorName`, `auxCtorPrefix` | `J_ctor_name.replacePrefix J_name auxJ_name` (`Add.lean:855`).  Both follow from `auxName` plus a `replacePrefix` prefix lemma. |
| `auxNodup` | `mkUniqueName`'s output is distinct — the fact `Add.lean:937`'s comment already asserts for `aux2nested`'s keys. |
| `head`, `headNe` | the presented head is the *real* nested type `J`, a constant the environment already holds.  Requires the environment invariant of §8.2. |
| `auxRec` | `auxRecName types k = appendIndexAfter' (mkRecName types[0].name) (k+1)`.  Requires the **main type's own name** to avoid the prefix — §8.2 — plus a `modifyBase` lemma. |
| `args` | a property of the *supplied* `tyArgs`, i.e. of the translation of `aux2nested`'s stored spine.  `replaceIfNested` builds it from the nested occurrence's parametric arguments, which passed `checkNoNestedAux`. |
| **`ownName`**, **`ownCtor`** | **not established.**  §8.2. |

### 8.2 The check that is missing, in both kernels

`ownName`/`ownCtor` say the declaration's *own* type and constructor names do not carry the
`_nested` prefix.  Nothing checks this.

* `Lean4Lean`: `checkNoNestedAux` (`Lean4Lean/Inductive/Add.lean:920-925`) scans, for each
  constructor, `anySubterm` of its **type** for a `.const` or `.proj` whose name is
  `_nested`-prefixed.  Its `n : Name` argument is used only in the error message.
* the C++ kernel: `check_no_nested_aux` (`src/kernel/inductive.cpp:1219-1233`) is the same scan,
  called from `environment::add_inductive` (`:1238-1246`) on each type's **type** and each
  constructor's **type**.  Its `name const & n` is likewise only formatted into the message.
  There is no name-level test against `*g_nested` anywhere in `src/kernel`; `check_constant_val`
  (`src/kernel/environment.cpp:127`) tests only for re-declaration.
* elaboration does not catch it either: `Lean.isReservedName`
  (`src/Lean/ResolveName.lean:48-53`) is a registry, and no registration in the Lean 4 tree
  installs `_nested`.

So `inductive _nested.Foo` is accepted by both kernels.  Two facts blunt it as an *attack*:
`mkUniqueName`/`mk_unique_name` skip names the environment already holds, so a user-declared
`_nested.X_1` cannot be silently reused as an auxiliary name; and the renamed recursors
`mkAuxRecNameMap` produces end in `rec_k`, never `rec`, so they cannot collide with an auxiliary
member's `mkRecName`.  **This file does not claim an exploit** — no witness was constructed, and
the two mitigations may well close every path.  What is measured is narrower and certain: the
prefix is *not* an invariant of the environment, so it cannot be used as a name barrier without
the check, and `ownName`/`ownCtor` therefore stay hypotheses.

The check `ownName`/`ownCtor` would need is one line per name at
`Lean4Lean/Inductive/Add.lean:930-935`, beside the existing `checkNoNestedAux` calls:

    checkNoNestedAuxName indType.name
    checkNoNestedAuxName ctor.name

with `checkNoNestedAuxName n := if (`_nested).isPrefixOf n then throw … else pure ()`.  That is
an edit to a file this stream does not own, and it is a **behavioural divergence from the C++
kernel** (it rejects declarations the C++ kernel accepts), so it belongs in `divergences.md` and
needs the orchestrator's decision, not this file's.

### 8.3 What the construction still does not give

* `VIndRestore.Faithful` — the environment must hold `R.tyName j` at a stored type whose
  instantiation *is* the auxiliary member's, and `R.ctorName C.name` likewise.  That is a
  `TrExprS`-level agreement between `restoreNested`'s output and `VIndCtor.typeR`, not a name
  fact; `Faithful.ctors_complete` additionally needs `VInductDecl'.Declared`.
* `VInductDecl'.Canonical` — a property of `D` alone, unrelated to `R`.
* the two *semantic* fields `tyLvls`/`tyArgs` of `mkRestore` are parameters, because there is no
  `Lean.Expr → VExpr` function (`TrExprS` is a relation).  Supplying them is the same obligation
  as `TrIndDeclN.trType`/`trCtors` and is where `aux2nested`'s stored `Expr`s enter.
* `RestoreData` is stated of `r`, `types`, `D`, `K`; nothing here connects it to
  `ElimNestedInductive.run`'s *monadic* output.  `Verify/Inductive/AddInductiveStep.lean`'s `EWF`
  machinery is the right vehicle — it already proves `res.aux2nested = []` for the non-nested
  path (`:293`, `:315`) — and the nested analogue is the next step.
-/
