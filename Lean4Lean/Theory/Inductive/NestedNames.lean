import Lean4Lean.Theory.Typing.ConstSubst
import Lean4Lean.Theory.Inductive.Telescope

/-!
# Reserved names, and constants of a `VExpr` filtered by a name predicate

Two pieces of **spec-level** name vocabulary, relocated here from
`Verify/Inductive/NestedRestore.lean` (2026-09-03) so that `Theory/` can state them:

* `VExpr.NoConstIn P` — every constant occurring in `e` fails `P`;
* `IsNestedName` — `n` carries the kernel's reserved `_nested` prefix.

Neither mentions `Lean.Expr`, `TrExprS`, or anything else from the refinement layer:
`NoConstIn` needs only `VExpr` (and `CSubst`, for `NoConstIn.noCSubst`), `IsNestedName` only
`Lean.Name`.  They were written in `Verify/` because that is where their first consumer lived,
but they are properties of the abstract syntax and the kernel's name discipline, so they belong
under `Theory/`.

**Why the move was forced.**  `VNestedOcc.OccursN`
(`Theory/Inductive/NestedBuild.lean`) strengthens `VNestedOcc.Occurs` with the clause
`∀ a ∈ N.args, a.NoConstIn IsNestedName`, and `VInductDecl'.Built.occurs` is stated at
`OccursN`.  `Verify/Inductive/NestedRestore.lean` transitively imports `NestedBuild.lean`, so
stating that clause at the old definition site was a genuine import cycle, not an
inconvenience.

Everything here is verbatim from the old site; no proof changed.  `NestedRestore.lean` keeps
`VIndRestore.NameBarrier` and `VIndRestore.NestedBarrier`, which are about a *restoration* and
so stay in the refinement layer.
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

/-! ### `mkRecName` is transparent to the barrier

`IsNestedName (n.rec)` is `IsNestedName n`: the extra component cannot *create* the prefix,
because `` `_nested `` is `.str .anonymous "_nested"` and `"rec" ≠ "_nested"`.  Both directions
are used — `→` for the auxiliary recursors' membership, `←` for the declared ones' absence. -/
theorem IsNestedName.mkRecName_iff {n : Name} :
    IsNestedName (Lean.mkRecName n) ↔ IsNestedName n := by
  refine ⟨fun h => (str_iff.1 h).resolve_left fun h => ?_, str⟩
  rw [show (`_nested : Name) = .str .anonymous "_nested" from rfl, Name.str.injEq] at h
  exact absurd h.2 (by decide)

end Lean4Lean
