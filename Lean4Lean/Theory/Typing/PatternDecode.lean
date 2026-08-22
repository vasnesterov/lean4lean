import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Inductive.Telescope

/-!
# Decoding a `VDefEq` into a `Pattern`

`VEnv.Params` asks for a relation `Pat : (p : Pattern) → p.RHS × p.Check → Prop` together
with `extra_pat`, which says that *every* rule of the environment is a `Pat`-registered
pattern under some leading lambdas.  An instance therefore has to produce, from a rule, the
pattern it is.

## Why this is a syntactic decoder and not an environment traversal

**`VEnv.defeqs` is a `VDefEq → Prop`, not a list.**  There is nothing to recurse over: an
environment does not carry the sequence of declarations that built it, and `addDefEq` only
ever widens a predicate.  So `Pat` cannot be defined by walking the environment and reading
each declaration's shape off the `VInductDecl'` that produced it.

Instead the pattern is recovered from the *syntax* of `df.lhs`: peel the leading lambdas,
split the body into a head and a spine, and read off whether the last spine entry is itself
a constant application (an ι-rule) or whether there is no spine at all (a δ-rule).
Correctness is then proved separately against each rule shape — `VInductDecl'.iotaRule`,
`VDefVal.toDefEq`, and `Theory/Quot.lean`'s rules — rather than by construction.

Do not "simplify" this into an environment traversal.  It cannot be done, and the reason is
not incidental: `Params.env` is an arbitrary `VEnv` satisfying `WF`, and `WF` is an
existential over *some* declaration list, so even a rule that provably came from an
inductive block cannot be tied back to it without a `VEnv.Sig`-style signature (design
§7.7, ledger I1), which does not exist.

## What is here

The syntactic half: `peelLams`/`spine` with their inverses, the decoder itself, and the
`Matches` lemma for a `varN` chain together with the path accessor that reads an argument
back out.  The `RHS`/`Check` construction for each rule shape builds on this.
-/

namespace Lean4Lean

open VExpr (mkPi mkLams mkApp bvars)

namespace VExpr

/-! ## Peeling leading lambdas -/

/-- Split a term into its maximal leading `lam` telescope and the body underneath. -/
def peelLams : VExpr → List VExpr × VExpr
  | .lam A b => let r := peelLams b; (A :: r.1, r.2)
  | e => ([], e)

@[simp] theorem peelLams_lam : peelLams (.lam A b) = (A :: (peelLams b).1, (peelLams b).2) :=
  rfl

theorem mkLams_peelLams : ∀ e : VExpr, mkLams (peelLams e).1 (peelLams e).2 = e
  | .lam A b => by rw [peelLams_lam, VExpr.mkLams_cons, mkLams_peelLams b]
  | .bvar _ | .sort _ | .const .. | .app .. | .forallE .. => rfl

/-- The body of a maximal `lam` telescope is not itself a `lam`. -/
theorem peelLams_not_lam : ∀ e : VExpr, ∀ A b, (peelLams e).2 ≠ .lam A b
  | .lam _ b, A', b' => peelLams_not_lam b A' b'
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _ | .app .., _, _
  | .forallE .., _, _ => nofun

theorem instL_peelLams : ∀ (e : VExpr) (ls : List VLevel),
    peelLams (e.instL ls)
      = ((peelLams e).1.map (VExpr.instL ls), (peelLams e).2.instL ls)
  | .lam A b, ls => by
    show peelLams (.lam (A.instL ls) (b.instL ls)) = _
    rw [peelLams_lam, peelLams_lam, instL_peelLams b ls]
    rfl
  | .bvar _, _ | .sort _, _ | .const .., _ | .app .., _ | .forallE .., _ => rfl

/-! ## Splitting an application spine -/

/-- Split a term into its head and its argument spine, left to right. -/
def spine : VExpr → VExpr × List VExpr
  | .app f a => let r := spine f; (r.1, r.2 ++ [a])
  | e => (e, [])

@[simp] theorem spine_app : spine (.app f a) = ((spine f).1, (spine f).2 ++ [a]) := rfl

theorem mkApp_spine : ∀ e : VExpr, mkApp (spine e).1 (spine e).2 = e
  | .app f a => by
    rw [spine_app, VExpr.mkApp_concat, mkApp_spine f]
  | .bvar _ | .sort _ | .const .. | .lam .. | .forallE .. => rfl

/-- The head of a spine is not itself an application. -/
theorem spine_head_not_app : ∀ e : VExpr, ∀ f a, (spine e).1 ≠ .app f a
  | .app g _, f', a' => spine_head_not_app g f' a'
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lam .., _, _
  | .forallE .., _, _ => nofun

theorem spine_mkApp' : ∀ (as : List VExpr) (e : VExpr),
    spine (mkApp e as) = ((spine e).1, (spine e).2 ++ as)
  | [], e => by simp
  | a :: as, e => by
    rw [VExpr.mkApp_cons, spine_mkApp' as, spine_app, List.append_assoc]
    rfl

theorem spine_mkApp {e : VExpr} (h : ∀ f a, e ≠ .app f a) (as : List VExpr) :
    spine (mkApp e as) = (e, as) := by
  rw [spine_mkApp']
  have : spine e = (e, []) := by
    cases e
    case app f a => exact absurd rfl (h f a)
    all_goals rfl
  rw [this]
  simp

end VExpr

/-! ## Matching a `varN` chain

`SimplePattern.toPattern` is built out of `Pattern.varN (.const c) n`, which matches a
constant applied to exactly `n` arguments.  `argPath` names the path at which the `i`-th of
those arguments sits, so that an `RHS` can select it. -/

/-- Reverse (snoc) induction on lists.  Written out rather than imported: this file sits
under `Theory/` and must not pull in `Mathlib`, where `List.reverseRecOn` lives. -/
theorem List.revRec {α : Type _} {motive : List α → Prop}
    (nil : motive []) (snoc : ∀ l a, motive l → motive (l ++ [a])) : ∀ l, motive l := by
  have h : ∀ r : List α, motive r.reverse := by
    intro r
    induction r with
    | nil => exact nil
    | cons a r ih => rw [List.reverse_cons]; exact snoc _ _ ih
  intro l; simpa using h l.reverse

namespace Pattern

/-- The path selecting argument `i` (0-based, left to right) of a `varN` chain of depth `n`;
`none` when `i` is out of range.  The outermost `.var` holds the *last* argument, so
argument `n-1` is `none` and earlier ones are `some` of the corresponding shallower path. -/
def argPath (q : Pattern) : (n i : Nat) → Option (Pattern.varN q n).Path
  | 0, _ => none
  | n+1, i => if i = n then some none else (argPath q n i).map some

/-- Out of range, there is no path. -/
theorem argPath_eq_none (q : Pattern) : ∀ {n i : Nat}, n ≤ i → argPath q n i = none
  | 0, _, _ => rfl
  | n+1, i, h => by
    rw [argPath, if_neg (by omega), argPath_eq_none q (by omega)]
    rfl

theorem argPath_lt (q : Pattern) {n i : Nat} {p} (h : argPath q n i = some p) : i < n := by
  rcases Nat.lt_or_ge i n with h' | h'
  · exact h'
  · rw [argPath_eq_none q h'] at h; exact absurd h (by simp)

/-- Every list is `[]` or a snoc. -/
theorem _root_.Lean4Lean.List.eq_concat {α : Type _} :
    ∀ l : List α, l = [] ∨ ∃ L b, l = L ++ [b] :=
  List.revRec (Or.inl rfl) fun l a _ => Or.inr ⟨l, a, rfl⟩

/-- **The matching lemma.**  A constant applied to `as` matches the `varN` chain of depth
`as.length`, with every `const` leaf carrying the head's level list, and with the `i`-th
argument readable at `argPath … i`.

The depth is a separate variable `n` with `as.length = n` rather than `as.length` itself:
`Pattern.varN q n`'s `Path` is a dependent type, and `(as ++ [a]).length` does not *reduce*
to `as.length + 1`, so a snoc induction on the list cannot rewrite the index without
tripping the motive. Inducting on `n` and decomposing the list instead keeps every
`varN q (n+1)` definitionally a `.var`. -/
theorem matches_varN_mkApp (c : Lean.Name) (ls : List VLevel) :
    ∀ (n : Nat) (as : List VExpr), as.length = n →
    ∃ m2, Matches (Pattern.varN (.const c) n)
        ((VExpr.const c ls).mkApp as) (fun _ => ls) m2 ∧
      ∀ i p, argPath (.const c) n i = some p → as[i]? = some (m2 p)
  | 0, as, h => by
    rw [List.length_eq_zero_iff.1 h]
    exact ⟨nofun, .const, by rintro i p ⟨⟩⟩
  | n+1, as, h => by
    obtain rfl | ⟨as', a, rfl⟩ := List.eq_concat as
    · simp at h
    have hlen : as'.length = n := by simpa using h
    obtain ⟨g, hg, hga⟩ := matches_varN_mkApp c ls n as' hlen
    refine ⟨(·.elim a g), ?_, ?_⟩
    · rw [VExpr.mkApp_concat]; exact .var hg
    · intro i p hp
      rw [argPath] at hp
      split at hp
      · rename_i hi
        subst hi
        cases hp
        rw [List.getElem?_append_right (Nat.le_of_eq hlen), hlen, Nat.sub_self]
        rfl
      · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hp
        rw [List.getElem?_append_left (hlen ▸ argPath_lt _ hp')]
        exact hga i p' hp'

end Pattern

/-! ## The decoder -/

/-- Read a `SimplePattern` off the body of a rule's left-hand side.  An ι-rule is a constant
applied to a spine whose last entry is itself a constant application; a δ-rule is a bare
constant. -/
def decodeSimple (e : VExpr) : Option SimplePattern :=
  match e.spine with
  | (.const c _, args) =>
    match args.reverse with
    | [] => some (.defn c)
    | last :: rest =>
      match last.spine with
      | (.const c' _, args') => some (.iota c rest.length c' args'.length)
      | _ => none
  | _ => none

/-! ### The whole argument list at once

`argPath` is `Option`-valued, so selecting an argument for an `RHS` would need a total
selector, and `(varN q n).Path` is `Empty` when `n = 0` — there is no default to fall back
on.  Producing the *list* of all `n` paths instead sidesteps that: `RHS.var` can be mapped
over it, and the readback becomes a single list equation rather than an indexed family. -/

namespace Pattern

/-- All `n` argument paths of a `varN` chain, left to right.  The outermost `.var` holds the
last argument, hence `map some ++ [none]`. -/
def argPaths (q : Pattern) : (n : Nat) → List (Pattern.varN q n).Path
  | 0 => []
  | n+1 => argPathsSucc q n (argPaths q n)
where
  /-- The successor step, written at the *unfolded* type `List (Option _)`.

  This is not cosmetic.  Inlining it makes `++` elaborate its `HAppend` instance at
  `List (varN q (n+1)).Path`; `rw [List.length_append]` then fails to match even though the
  two types are definitionally equal, because `rw` is syntactic and the instance is not.
  Naming the step gives every lemma below a clean type to `show` its way into. -/
  argPathsSucc (q : Pattern) (n : Nat) (l : List (Pattern.varN q n).Path) :
      List (Option (Pattern.varN q n).Path) :=
    l.map some ++ [none]

@[simp] theorem length_argPaths (q : Pattern) : ∀ n, (argPaths q n).length = n
  | 0 => rfl
  | n+1 => by
    show (argPaths.argPathsSucc q n (argPaths q n)).length = n + 1
    rw [argPaths.argPathsSucc, List.length_append, List.length_map, length_argPaths q n]
    rfl

/-- **Readback, as a list equation.**  Matching a constant applied to `as` against the
`varN` chain of depth `as.length` recovers `as` exactly by mapping the match over
`argPaths`.

Indexed by a depth variable `n` with `as.length = n` rather than by `as.length` itself —
see note 0b at the head of `Theory/Inductive/Lemmas.lean`; `(as ++ [a]).length` does not
reduce, so a snoc induction cannot rewrite the `Path`'s index. -/
theorem matches_varN_argPaths (c : Lean.Name) (ls : List VLevel) :
    ∀ (n : Nat) (as : List VExpr), as.length = n →
    ∃ m2, Matches (Pattern.varN (.const c) n)
        ((VExpr.const c ls).mkApp as) (fun _ => ls) m2 ∧
      (argPaths (.const c) n).map m2 = as
  | 0, as, h => by
    rw [List.length_eq_zero_iff.1 h]
    exact ⟨nofun, .const, rfl⟩
  | n+1, as, h => by
    obtain rfl | ⟨as', a, rfl⟩ := List.eq_concat as
    · simp at h
    have hlen : as'.length = n := by simpa using h
    obtain ⟨g, hg, hga⟩ := matches_varN_argPaths c ls n as' hlen
    -- the domain ascription keeps `List.map`'s instance at the unfolded type; see
    -- `argPaths.argPathsSucc`
    refine ⟨(fun x : Option (Pattern.varN (.const c) n).Path => x.elim a g), ?_, ?_⟩
    · rw [VExpr.mkApp_concat]; exact .var hg
    · show List.map _ (argPaths.argPathsSucc (.const c) n (argPaths (.const c) n)) = _
      rw [argPaths.argPathsSucc, List.map_append, List.map_map, List.map_cons, List.map_nil]
      exact congrArg (· ++ [a]) hga

end Pattern

/-! ## Building an `RHS` and a `Check`

`Pattern.RHS` and `Pattern.Check` are cons-shaped: `RHS` has a binary `app`, `Check` threads
a `rest`.  Both rule shapes need to build one from a *list* — the ι-rule's right-hand side
is `iotaLam` applied to a whole spine of matched paths, and its check is three groups of
clauses concatenated — so the list-shaped constructors and their `apply`/`OK` laws come
first. -/

namespace Pattern

/-- `RHS` applied to a spine. -/
def RHS.mkApp {p : Pattern} (f : p.RHS) : List p.RHS → p.RHS
  | [] => f
  | a :: as => (f.app a).mkApp as

theorem RHS.apply_mkApp {p : Pattern} {m1 m2} (f : p.RHS) : ∀ as : List p.RHS,
    (f.mkApp as).apply m1 m2 = VExpr.mkApp (f.apply m1 m2) (as.map (RHS.apply m1 m2))
  | [] => rfl
  | a :: as => by
    rw [RHS.mkApp, apply_mkApp (f.app a) as, RHS.apply, List.map_cons, VExpr.mkApp_cons]

/-- Concatenate two check lists. -/
def Check.append {p : Pattern} : p.Check → p.Check → p.Check
  | .true, d => d
  | .defeq x y rest, d => .defeq x y (rest.append d)
  | .level x i y j rest, d => .level x i y j (rest.append d)

theorem Check.OK_append {p : Pattern} {df m1 m2} : ∀ c d : p.Check,
    (c.append d).OK df m1 m2 ↔ c.OK df m1 m2 ∧ d.OK df m1 m2
  | .true, d => by simp [Check.append, Check.OK]
  | .defeq x y rest, d => by
    rw [Check.append, Check.OK, Check.OK, Check.OK_append rest d]
    exact ⟨fun ⟨h, h1, h2⟩ => ⟨⟨h, h1⟩, h2⟩, fun ⟨⟨h, h1⟩, h2⟩ => ⟨h, h1, h2⟩⟩
  | .level x i y j rest, d => by
    rw [Check.append, Check.OK, Check.OK, Check.OK_append rest d]
    exact ⟨fun ⟨h, h1, h2⟩ => ⟨⟨h, h1⟩, h2⟩, fun ⟨⟨h, h1⟩, h2⟩ => ⟨h, h1, h2⟩⟩

/-- A block of `defeq` clauses. -/
def Check.ofDefeqs {p : Pattern} : List (p.RHS × p.RHS) → p.Check
  | [] => .true
  | (x, y) :: rest => .defeq x y (ofDefeqs rest)

theorem Check.OK_ofDefeqs {p : Pattern} {df m1 m2} : ∀ l : List (p.RHS × p.RHS),
    (Check.ofDefeqs l).OK df m1 m2
      ↔ ∀ xy ∈ l, df (xy.1.apply m1 m2) (xy.2.apply m1 m2)
  | [] => by simp [Check.ofDefeqs, Check.OK]
  | (x, y) :: rest => by
    rw [Check.ofDefeqs, Check.OK, Check.OK_ofDefeqs rest]
    simp

/-- A block of `level` clauses. -/
def Check.ofLevels {p : Pattern} : List (p.LPath × Nat × p.LPath × Nat) → p.Check
  | [] => .true
  | (x, i, y, j) :: rest => .level x i y j (ofLevels rest)

theorem Check.OK_ofLevels {p : Pattern} {df m1 m2} :
    ∀ l : List (p.LPath × Nat × p.LPath × Nat),
    (Check.ofLevels l).OK df m1 m2
      ↔ ∀ t ∈ l, ((m1 t.1).getD t.2.1 .zero ≈ (m1 t.2.2.1).getD t.2.2.2 .zero)
  | [] => by simp [Check.ofLevels, Check.OK]
  | (x, i, y, j) :: rest => by
    rw [Check.ofLevels, Check.OK, Check.OK_ofLevels rest]
    simp

end Pattern

/-! ## Decoder correctness

Two shapes, each proved directly rather than by construction — the decoder cannot know
which rule it is looking at. -/

theorem decodeSimple_defn (c : Lean.Name) (ls : List VLevel) :
    decodeSimple (.const c ls) = some (.defn c) := rfl

theorem decodeSimple_iota (r c : Lean.Name) (ls ls' : List VLevel) (as bs : List VExpr) :
    decodeSimple ((VExpr.const r ls).mkApp (as ++ [(VExpr.const c ls').mkApp bs]))
      = some (.iota r as.length c bs.length) := by
  simp only [decodeSimple,
    VExpr.spine_mkApp (e := VExpr.const r ls) (by nofun),
    VExpr.spine_mkApp (e := VExpr.const c ls') (by nofun),
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.length_reverse]

/-- **The ι-shape matches its pattern.**  Both level lists are recorded — the recursor's at
the left leaf and the constructor's at the right — which is what lets a `Check.level` clause
relate them. -/
theorem matches_iota (r c : Lean.Name) (ls ls' : List VLevel) {m n : Nat}
    (as bs : List VExpr) (hm : as.length = m) (hn : bs.length = n) :
    ∃ m1 m2, Pattern.Matches (SimplePattern.iota r m c n).toPattern
        ((VExpr.const r ls).mkApp (as ++ [(VExpr.const c ls').mkApp bs])) m1 m2 ∧
      (∀ i p, Pattern.argPath (.const r) m i = some p → as[i]? = some (m2 (.inl p))) ∧
      (∀ i p, Pattern.argPath (.const c) n i = some p → bs[i]? = some (m2 (.inr p))) := by
  obtain ⟨g1, hg1, hga1⟩ := Pattern.matches_varN_mkApp r ls m as hm
  obtain ⟨g2, hg2, hga2⟩ := Pattern.matches_varN_mkApp c ls' n bs hn
  refine ⟨Sum.elim (fun _ => ls) (fun _ => ls'), Sum.elim g1 g2, ?_, hga1, hga2⟩
  rw [VExpr.mkApp_concat]
  exact .app hg1 hg2

end Lean4Lean
