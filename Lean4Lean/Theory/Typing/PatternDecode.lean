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

/-! ## Peeling leading pis

The companion to `peelLams`, used to tell a recursor's stored type from a constructor's: both
are `mkPi` telescopes, and what distinguishes them is the *head of the body* — a `bvar` for
the recursor's motive application, a `const` for the constructor's `I p args`. -/

/-- Split a term into its maximal leading `forallE` telescope and the body underneath. -/
def peelPis : VExpr → List VExpr × VExpr
  | .forallE A b => let r := peelPis b; (A :: r.1, r.2)
  | e => ([], e)

@[simp] theorem peelPis_forallE :
    peelPis (.forallE A b) = (A :: (peelPis b).1, (peelPis b).2) := rfl

theorem peelPis_mkPi : ∀ (As : List VExpr) (B : VExpr),
    peelPis (mkPi As B) = (As ++ (peelPis B).1, (peelPis B).2)
  | [], _ => rfl
  | A :: As, B => by rw [VExpr.mkPi_cons, peelPis_forallE, peelPis_mkPi As B]; rfl

theorem peelPis_app : peelPis (.app f a) = ([], .app f a) := rfl

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

theorem peelPis_mkApp_app : ∀ (as : List VExpr) (f a : VExpr),
    peelPis (mkApp (.app f a) as) = ([], mkApp (.app f a) as)
  | [], _, _ => rfl
  | b :: as, f, a => by rw [VExpr.mkApp_cons, peelPis_mkApp_app as]

/-- The head of a term's body, after all leading pis are peeled: the discriminator. -/
def piBodyHead (e : VExpr) : VExpr := (spine (peelPis e).2).1

theorem piBodyHead_mkPi_mkApp (As : List VExpr) {f : VExpr}
    (hf : ∀ g a, f ≠ .app g a) (hp : ∀ A b, f ≠ .forallE A b) (as : List VExpr) :
    piBodyHead (mkPi As (mkApp f as)) = f := by
  rw [piBodyHead, peelPis_mkPi]
  cases as with
  | nil =>
    show (spine (peelPis f).2).1 = f
    cases f
    case forallE A b => exact absurd rfl (hp A b)
    all_goals exact congrArg Prod.fst (spine_mkApp hf [])
  | cons a as =>
    show (spine (peelPis (mkApp f (a :: as))).2).1 = f
    rw [VExpr.mkApp_cons, peelPis_mkApp_app, ← VExpr.mkApp_cons, spine_mkApp hf]

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

/-! ## The right-hand sides

Both shapes' right-hand sides are "a closed term, instantiated at a leaf's levels, applied to
some of the matched arguments".  Neither construction needs to know it is about an inductive
block: the ι-shape is parameterised by *where* to cut the two argument lists, and the tie-in
to `VInductDecl'.iotaRule` happens at the use site. -/

/-- A δ-rule's right-hand side: the closed value, at the head's levels. -/
def deltaRHS (c : Lean.Name) (v : VExpr) (h : v.Closed) : (Pattern.const c).RHS :=
  .fixed v () h

@[simp] theorem deltaRHS_apply {c v h m1 m2} :
    (deltaRHS c v h).apply m1 m2 = v.instL (m1 ()) := rfl

/-- The constructor's `const` leaf of an ι-pattern.  (The recursor's is `LPath.head`.) -/
def iotaLeafCtor (r c : Lean.Name) (m n : Nat) :
    (SimplePattern.iota r m c n).toPattern.LPath :=
  Sum.inr (Pattern.LPath.head _)

/-- An ι-rule's right-hand side: a closed term at the recursor leaf's levels, applied to the
first `k` matched *recursor* arguments and then the matched *constructor* arguments from `i`
on.

For `VInductDecl'.iotaRule` the closed term is `iotaLam`, `k = np + nm + nmin` (parameters,
motives, minors — taken from the recursor's side) and `i = np` (the constructor's fields,
its parameters being dropped because the recursor's copies were already taken).  In the rule
itself the two copies of the parameters are literally the same variables, so either side
would do; a `Check.defeq` clause is what makes the choice sound for an arbitrary match. -/
def iotaRHS (r c : Lean.Name) (m n : Nat) (v : VExpr) (h : v.Closed) (k i : Nat) :
    (SimplePattern.iota r m c n).toPattern.RHS :=
  Pattern.RHS.mkApp (Pattern.RHS.fixed v (Pattern.LPath.head _) h)
    ((((Pattern.argPaths (.const r) m).take k).map fun x =>
        (Pattern.RHS.var (p := (SimplePattern.iota r m c n).toPattern) (Sum.inl x)))
      ++ (((Pattern.argPaths (.const c) n).drop i).map fun y =>
        (Pattern.RHS.var (p := (SimplePattern.iota r m c n).toPattern) (Sum.inr y))))

theorem iotaRHS_apply {r c : Lean.Name} {m n : Nat} {v : VExpr} {h : v.Closed} {k i : Nat}
    {m1 m2} {as bs : List VExpr}
    (ha : (Pattern.argPaths (.const r) m).map (fun p => m2 (Sum.inl p)) = as)
    (hb : (Pattern.argPaths (.const c) n).map (fun p => m2 (Sum.inr p)) = bs) :
    (iotaRHS r c m n v h k i).apply m1 m2
      = (v.instL (m1 (Pattern.LPath.head _))).mkApp (as.take k ++ bs.drop i) := by
  subst ha; subst hb
  rw [iotaRHS, Pattern.RHS.apply_mkApp, List.map_append, List.map_map, List.map_map,
    List.map_take, List.map_drop]
  rfl

/-! ## The checks

**Do not simplify these to `Check.true`.**

`extra_pat` alone would be satisfied by `Check.true`: the rule's own left-hand side has the
recursor's and the constructor's copies of the parameters as *literally the same variables*,
so any clause relating them holds by `rfl` and dropping the clauses only makes `extra_pat`
easier.  That is precisely the trap.  `pat_wf` quantifies over an **arbitrary** well-typed
`e` matching the pattern — `rec.{ls} a₁ … a_m (c.{ls'} b₁ … b_n)` with the `aᵢ` and `bⱼ`
unrelated terms and `ls`, `ls'` unrelated level lists — and the *only* lever for pinning
them together is the check.  With `Check.true` the redex's reduct is not determined by the
match, `pat_wf` becomes unprovable by anyone, and nothing in the tree records why.

So the clauses below are the ones `pat_wf` demands, and `extra_pat` discharges them for
real:

* `iotaParamsCheck` — the recursor's `i`-th parameter argument is defeq to the
  constructor's.  Needed because `iotaRHS` takes the parameters from the recursor's side
  while the major premise supplies the constructor's.
* `iotaIndicesCheck` — the recursor's index arguments are defeq to the constructor's result
  indices, computed from its parameters and fields.  Without this the ι-rule would fire on
  a redex whose index arguments disagree with the major premise's type.
* `iotaLevelsCheck` — the level list at the recursor leaf agrees with the one at the
  constructor leaf, entry by entry.  `Pattern.Matches` deliberately records a list at every
  `const` leaf rather than one for the whole match, for exactly this.

`Check.true` is correct only for a δ-rule, where the head carries no arguments at all. -/

/-- The parameter-agreement clauses: recursor argument `t` against constructor argument `t`,
for the first `np` of each. -/
def iotaParamsCheck (r c : Lean.Name) (m n np : Nat) :
    (SimplePattern.iota r m c n).toPattern.Check :=
  Pattern.Check.ofDefeqs <|
    (((Pattern.argPaths (.const r) m).take np).zip ((Pattern.argPaths (.const c) n).take np)).map
      fun xy =>
        (Pattern.RHS.var (p := (SimplePattern.iota r m c n).toPattern) (Sum.inl xy.1),
         Pattern.RHS.var (p := (SimplePattern.iota r m c n).toPattern) (Sum.inr xy.2))

/-- The index-agreement clauses: the recursor's index arguments — everything after the first
`k` — against the supplied computed indices. -/
def iotaIndicesCheck (r c : Lean.Name) (m n k : Nat)
    (computed : List (SimplePattern.iota r m c n).toPattern.RHS) :
    (SimplePattern.iota r m c n).toPattern.Check :=
  Pattern.Check.ofDefeqs <|
    (((Pattern.argPaths (.const r) m).drop k).zip computed).map fun xy =>
      (Pattern.RHS.var (p := (SimplePattern.iota r m c n).toPattern) (Sum.inl xy.1), xy.2)

/-- The level-agreement clauses: entry `ij.1` of the recursor leaf's list against entry
`ij.2` of the constructor leaf's. -/
def iotaLevelsCheck (r c : Lean.Name) (m n : Nat) (pairs : List (Nat × Nat)) :
    (SimplePattern.iota r m c n).toPattern.Check :=
  Pattern.Check.ofLevels <|
    pairs.map fun ij =>
      (Pattern.LPath.head _, ij.1, iotaLeafCtor r c m n, ij.2)

/-- The whole ι-check. -/
def iotaCheck (r c : Lean.Name) (m n np k : Nat)
    (computed : List (SimplePattern.iota r m c n).toPattern.RHS) (pairs : List (Nat × Nat)) :
    (SimplePattern.iota r m c n).toPattern.Check :=
  (iotaParamsCheck r c m n np).append
    ((iotaIndicesCheck r c m n k computed).append (iotaLevelsCheck r c m n pairs))

theorem iotaCheck_OK {r c : Lean.Name} {m n np k : Nat} {computed pairs} {df m1 m2} :
    (iotaCheck r c m n np k computed pairs).OK df m1 m2
      ↔ (∀ xy ∈ ((Pattern.argPaths (.const r) m).take np).zip
              ((Pattern.argPaths (.const c) n).take np),
            df (m2 (Sum.inl xy.1)) (m2 (Sum.inr xy.2)))
        ∧ (∀ xy ∈ ((Pattern.argPaths (.const r) m).drop k).zip computed,
            df (m2 (Sum.inl xy.1)) (xy.2.apply m1 m2))
        ∧ (∀ ij ∈ pairs,
            ((m1 (Pattern.LPath.head _)).getD ij.1 .zero
              ≈ (m1 (iotaLeafCtor r c m n)).getD ij.2 .zero)) := by
  rw [iotaCheck, Pattern.Check.OK_append, Pattern.Check.OK_append, iotaParamsCheck,
    iotaIndicesCheck, iotaLevelsCheck, Pattern.Check.OK_ofDefeqs,
    Pattern.Check.OK_ofDefeqs, Pattern.Check.OK_ofLevels]
  simp only [List.mem_map]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun xy hxy => h1 _ ⟨xy, hxy, rfl⟩, fun xy hxy => h2 _ ⟨xy, hxy, rfl⟩,
      fun ij hij => h3 _ ⟨ij, hij, rfl⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rintro _ ⟨xy, hxy, rfl⟩; exact h1 xy hxy,
      by rintro _ ⟨xy, hxy, rfl⟩; exact h2 xy hxy,
      by rintro _ ⟨ij, hij, rfl⟩; exact h3 ij hij⟩

/-! ### The ι-rule's spine alignment

The one arithmetic fact item 6 needs, isolated as its own lemma so the assembly never
reasons about `bvars` offsets inline.

An ι-rule's left-hand side applies the recursor to the parameter, motive and minor variable
blocks *and* the constructor to the parameter and field blocks; `iotaRHS` then takes the
first three from the recursor's side and the fields from the constructor's.  What comes back
must be `bvars 0 |Γ'|` — the ι-rule's whole binder context in order — and that is this
equation. -/
theorem bvars_spine_align (np nm nmin nf : Nat) :
    (bvars (nf + (nm + nmin)) np ++ bvars (nf + nmin) nm ++ bvars nf nmin) ++ bvars 0 nf
      = bvars 0 (np + nm + nmin + nf) := by
  rw [show np + nm + nmin + nf = (np + nm + nmin) + nf from rfl, VExpr.bvars_add,
    Nat.zero_add, VExpr.bvars_add₃, Nat.add_assoc nf nm nmin]

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

/-- **The ι-shape matches its pattern, with both argument lists read back.**  The `varN`
readback on each side, combined.  Both level lists are recorded — the recursor's at every
left leaf and the constructor's at every right leaf — which is what lets a `Check.level`
clause relate them. -/
theorem matches_iota_paths (r c : Lean.Name) (ls ls' : List VLevel) {m n : Nat}
    (as bs : List VExpr) (hm : as.length = m) (hn : bs.length = n) :
    ∃ m1 m2, Pattern.Matches (SimplePattern.iota r m c n).toPattern
        ((VExpr.const r ls).mkApp (as ++ [(VExpr.const c ls').mkApp bs])) m1 m2 ∧
      (∀ x, m1 (Sum.inl x) = ls) ∧ (∀ y, m1 (Sum.inr y) = ls') ∧
      (Pattern.argPaths (.const r) m).map (fun p => m2 (Sum.inl p)) = as ∧
      (Pattern.argPaths (.const c) n).map (fun p => m2 (Sum.inr p)) = bs := by
  obtain ⟨g1, hg1, hga1⟩ := Pattern.matches_varN_argPaths r ls m as hm
  obtain ⟨g2, hg2, hga2⟩ := Pattern.matches_varN_argPaths c ls' n bs hn
  refine ⟨Sum.elim (fun _ => ls) (fun _ => ls'), Sum.elim g1 g2, ?_,
    fun _ => rfl, fun _ => rfl, hga1, hga2⟩
  rw [VExpr.mkApp_concat]
  exact .app hg1 hg2

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

/-! ## Inverting `Pattern.inter` and `Subpattern`

`Params.pat_uniq` is driven entirely by these two: its hypotheses are `Subpattern p₃ p₁` and
`p₂.inter p₃ = some p₄`, and every case of the proof begins by asking what shapes those two
admit.  Both are stated as *inversions* — hypothesis in, structure out — rather than as
`simp` lemmas, because `inter` is written with `do` notation and `simp only
[Option.bind_eq_some_iff]` does not fire on the resulting term (the same mismatch recorded in
`Theory/Typing/DeltaUnique.lean`); naming the `bind` chain and closing by `rfl` is what
works. -/

namespace Pattern

theorem inter_const_const {c c' p} : (Pattern.const c).inter (.const c') = some p →
    c = c' ∧ p = .const c := by
  simp only [inter]; split
  · rintro ⟨rfl⟩; exact ⟨‹_›, rfl⟩
  · exact nofun

theorem inter_const_app {c F A p} : (Pattern.const c).inter (.app F A) ≠ some p := nofun
theorem inter_const_var {c f p} : (Pattern.const c).inter (.var f) ≠ some p := nofun
theorem inter_app_const {F A c p} : (Pattern.app F A).inter (.const c) ≠ some p := nofun
theorem inter_var_const {f c p} : (Pattern.var f).inter (.const c) ≠ some p := nofun

theorem inter_app_var {F A f p} : (Pattern.app F A).inter (.var f) = some p →
    ∃ x, F.inter f = some x ∧ p = .app x A := by
  rw [show (Pattern.app F A).inter (.var f) = (F.inter f).bind (fun x => some (.app x A)) from rfl,
    Option.bind_eq_some_iff]
  rintro ⟨x, hx, hp⟩; exact ⟨x, hx, (Option.some_inj.1 hp).symm⟩

theorem inter_app_app {F A F' A' p} : (Pattern.app F A).inter (.app F' A') = some p →
    ∃ x y, F.inter F' = some x ∧ A.inter A' = some y ∧ p = .app x y := by
  rw [show (Pattern.app F A).inter (.app F' A')
      = (F.inter F').bind (fun x => (A.inter A').bind (fun y => some (.app x y))) from rfl,
    Option.bind_eq_some_iff]
  rintro ⟨x, hx, h⟩
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨y, hy, hp⟩ := h
  exact ⟨x, y, hx, hy, (Option.some_inj.1 hp).symm⟩

theorem inter_var_var {f f' p} : (Pattern.var f).inter (.var f') = some p →
    ∃ x, f.inter f' = some x ∧ p = .var x := by
  rw [show (Pattern.var f).inter (.var f') = (f.inter f').bind (fun x => some (.var x)) from rfl,
    Option.bind_eq_some_iff]
  rintro ⟨x, hx, hp⟩; exact ⟨x, hx, (Option.some_inj.1 hp).symm⟩

/-- **The `varN` case.**  Two `varN` chains over constants intersect only if both the name
and the depth agree — the arity is as rigid as the head. -/
theorem inter_varN_const {c c' : Lean.Name} : ∀ {m k p},
    ((Pattern.const c).varN m).inter ((Pattern.const c').varN k) = some p →
      c = c' ∧ m = k ∧ p = (Pattern.const c).varN m
  | 0, 0, _, h => by obtain ⟨rfl, rfl⟩ := inter_const_const h; exact ⟨rfl, rfl, rfl⟩
  | 0, _+1, _, h => absurd h inter_const_var
  | _+1, 0, _, h => absurd h inter_var_const
  | _+1, _+1, _, h => by
    obtain ⟨x, hx, rfl⟩ := inter_var_var h
    obtain ⟨rfl, rfl, rfl⟩ := inter_varN_const hx
    exact ⟨rfl, rfl, rfl⟩

end Pattern

/-- A subpattern of a `varN` chain is either a shorter chain or a subpattern of its base. -/
theorem Subpattern.varN_inv {q p : Pattern} : ∀ {n}, Subpattern q (p.varN n) →
    (∃ k, k ≤ n ∧ q = p.varN k) ∨ Subpattern q p
  | 0, h => .inr h
  | n+1, h => by
    cases h with
    | refl => exact .inl ⟨n+1, Nat.le_refl _, rfl⟩
    | varL h =>
      rcases varN_inv h with ⟨k, hk, rfl⟩ | h
      · exact .inl ⟨k, Nat.le_succ_of_le hk, rfl⟩
      · exact .inr h

/-- A constant has no proper subpatterns. -/
theorem Subpattern.const_inv {q : Pattern} {c} (h : Subpattern q (.const c)) : q = .const c := by
  cases h; rfl

theorem Subpattern.varN_const_inv {q : Pattern} {c n}
    (h : Subpattern q ((Pattern.const c).varN n)) :
    ∃ k, k ≤ n ∧ q = (Pattern.const c).varN k := by
  rcases h.varN_inv with h | h
  · exact h
  · exact ⟨0, Nat.zero_le _, h.const_inv⟩

end Lean4Lean
