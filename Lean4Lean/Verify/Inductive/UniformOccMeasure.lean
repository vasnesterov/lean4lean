import Lean4Lean.Experimental.ConeJoin

/-!
# The specification of `check_uniform_ind_occs` — and the check it is now tested against

**This file changes no implementation and weakens no statement.**  It began as the scoping round
for ledger row 116e: the C++ kernel runs a purely syntactic uniformity pre-pass on constructor
types — `check_uniform_ind_occs` in `src/kernel/inductive.cpp`, called from
`environment::add_inductive` immediately before `elim_nested_inductive_fn`, exactly where
`Environment.addInductive`'s guard loop sits — and lean4lean had no counterpart, so lean4lean
**accepted more than C++** here.

**Row 116e is closed as of 2026-09-02.**  `Lean4Lean.checkUniformIndOccs` is installed, in the
guard loop's inner (per-constructor) body, where C++ puts it.  This file's role changed
accordingly, and in one direction only: it is the **specification**, and §3.0 proves the installed
check *equals* it (`uio_impl_eq`), so §3's exactness results are results about the real check.
Every `#eval` in §5 and §6 now runs `Lean4Lean.noNonUniformOcc` — the implementation — rather than
this file's `uioOk`; a table that agreed with its own twin would measure nothing.
`Verify/Inductive/RunIdentity.lean` §6.2 carries the consequence, `rejectsNonUniform`.

Every name is prefixed `uio`/`UIO` (ledger row 113f: inside the `ConeJoin` closure a short name
collides, and a silent resolution produces a confidently wrong measurement).  Per row 116h this
file **must never be listed in `ConeJoin.lean`** — it imports it, so the reverse edge is a build
cycle.

## 1. The C++ condition, transcribed

`check_uniform_ind_occs(env, d)` is
`for_each(constructor_type(cnstr), λ (t, offset) => …)` for every constructor of every member,
with the *offset-taking* overload, i.e. `for_each_offset_fn` of `kernel/for_each_fn.cpp`.  That
visitor:

* visits every subterm at `offset` = the number of enclosing binders.  `lam`/`forallE` bump the
  **body** by one (`apply(binding_domain(e), offset); apply(binding_body(e), offset+1)`);
  `letE` bumps its **body** by one but not its type or value; `mdata` and `proj` do not bump;
* at an `App` node visits `app_fn` **and** `app_arg` at the same offset — so every **partial**
  application of a spine is itself a visited subterm.  (This is `for_each_offset_fn`, which has
  no `partial_apps` switch; it always behaves like `for_each_fn<true>`.)
* visits `Const`/`BVar`/`Sort` without consulting the memo and **ignores the returned `bool`**
  there (they have no children); every other node is memoised on `(pointer, offset)`, which is
  semantically neutral because a node's verdict depends only on the node and the offset;
* descends when the visitor returns `true`, does not descend when it returns `false`, and aborts
  when it throws.

At each visited node `t` the body computes `fn = get_app_args(t, args)` — and `get_app_args` is a
plain `while (is_app(*it))` loop, so it does **not** look through `mdata`: an `mdata`-wrapped
head is not a `Const` and the node merely descends.  Then, with `nparams = d.get_nparams()` and
`lvls = lparams_to_levels(d.get_lparams())`:

* `fn` not a constant, or not one of the block's member names: **return true** (descend);
* `args.size() > nparams`: **return true** (descend).  Its own comment: *"Over-applied: descend,
  so that occurrences in the indices are checked too.  The parameter application itself is
  visited as a subterm of `t` and checked below."*  So an over-applied occurrence imposes no
  requirement *at that node*; the requirement lands on its `nparams`-prefix, which is a visited
  subterm at the same offset;
* otherwise require, all four conjuncts, `args.size() == nparams`, `offset >= nparams`,
  `const_levels(fn) == lvls`, and `is_bvar(args[i], offset - 1 - i)` for every `i < nparams`;
  **throw** on failure, **return false** (do not descend) on success.

Two consequences worth stating because they are easy to get wrong:

* the pruning is what makes the check satisfiable at all.  `I p₀ … p_{np-1}` contains the partial
  application `I p₀ … p_{np-2}`, whose head is a block constant applied to `np-1 ≤ np` arguments;
  C++ never visits it, because the visitor returned `false` at the saturated node.  A closed form
  that quantified over *all* subterms would refuse `List`.  `uio_naive_too_strong` proves that
  rather than asserting it;
* the walk starts at `offset = 0` on the **whole** constructor type, parameter binders included,
  so an occurrence inside a *parameter's own type* sits at `offset < nparams` and is always
  rejected.  A block member therefore cannot appear in a parameter type at all.

Nothing here is `whnf`-ed, and the C++ comment says why: *"Later phases inspect the constructor
types modulo `whnf`, which can erase an occurrence (as in `(fun _ => Unit) (T Nat)`), and the
parametric arguments of a nested occurrence are dropped from the auxiliary declaration
altogether, so a non-uniform occurrence could escape checking there.  Reduction never creates an
occurrence of a datatype being declared, since those are not yet in the environment, so checking
the syntactic occurrences here covers all of them."*  Upstream already knew about the
`whnf`-erasure gap and closed the soundness-relevant half syntactically.

C++ runs this on the **submitted** declaration `d`, on **constructor** types only — not on the
members' own types (unlike the two `check_no_nested_aux` calls beside it, which do both).

`uioNArgs`/`uioFn`/`uioArgs`/`uioArgsOk`/`uioOwnLevels`/`uioOk` below are that, as pure
structural recursions on `Lean.Expr`; `UIOCond` is the same condition in `Prop`; and §3.0 proves
each one equal to its installed counterpart in `Lean4Lean/Inductive/Add.lean`.

## 2. What is proved here

| result | content |
| --- | --- |
| `uioOk_iff` | **the exactness lemma**: the `Bool` check decides `UIOCond` and nothing else |
| `uioOwnLevels_iff` | the level comparison decides `us = lps.map .param`, with no `Level.beq` |
| `uioArgsOk_iff` | the spine walk decides C++'s `is_bvar(args[i], offset-1-i)` loop |
| `uio_occOk_np_le_d` | C++'s `offset >= nparams` conjunct is subsumed by that loop |
| `uio_ok_of_occ` | **instrument 7's dual**: no uniform occurrence is refused |
| `uio_naive_too_strong` | the pruning-free reading is unsatisfiable, so it is not the condition |
| `uio_uniformOcc_iff_prefix` | **§4: the C++ condition IS `VInductDecl'.uniformOcc?`** |
| `uio_uniformOcc_iff` | …literally the same predicate on the nodes C++ checks |
| `uio_impl_eq` | **§3.0: the specification IS the installed `Lean4Lean.noNonUniformOcc`** |
| `uio_impl_check_eq` | …and `uioCheck` is `Lean4Lean.checkUniformIndOccs`, wrappers included |
| `uio_impl_iff` | so the installed check decides `UIOCond` and nothing else |
| `uio_not_blockUniformOccs_uioE` | **§7: `RejectsNonUniform`'s hypothesis, inhabited** |
| `uio_rejectsNonUniform_fires` | `addInductive` rejects the arena's non-uniform block, proved |
| `uio_uioL_uniform` | …and still accepts the uniform nested vehicle, so it is not "reject all" |

No frozen axiom: the `#print axioms` block of §9 is the guard, and it is checked
against `{propext, Classical.choice, Quot.sound}` by `Verify/Guard.lean`'s check 1 for anything
that ever reaches `kernel_sound`.  In particular `uioOwnLevels` pattern-matches `.param` and
compares only `Name`s rather than using `Lean.Level.beq`, whose lawfulness is the **frozen**
axiom `Lean.Level.instLawfulBEqLevel` (`Verify/Axioms.lean`) — the same move
`checkNoLooseBVars` makes when it avoids `Expr.looseBVarRange` and `Expr.mkData_eq`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace UIOGuard

/-! ## 3. The check, and its exactness -/

def uioNArgs : Expr → Nat
  | .app f _ => uioNArgs f + 1
  | _ => 0

def uioFn : Expr → Expr
  | .app f _ => uioFn f
  | e => e

def uioArgs : Expr → List Expr
  | .app f a => uioArgs f ++ [a]
  | _ => []

/-- C++'s `is_bvar(args[i], offset - 1 - i)`, written `j + 1 + i == d` so that no truncated
subtraction is involved: it entails `i < d`, which is how C++'s separate `offset >= nparams`
conjunct is subsumed (`uio_occOk_np_le_d`). -/
def uioIsParamArg (d i : Nat) : Expr → Bool
  | .bvar j => j + 1 + i == d
  | _ => false

def uioArgsOk (d : Nat) : Expr → Bool
  | .app f a => uioArgsOk d f && uioIsParamArg d (uioNArgs f) a
  | _ => true

/-- `us` is the block's own level list, i.e. `lps.map Level.param`.

Deliberately **not** `us == lps.map .param`: `Lean.Level.beq` is `@[extern] opaque`, so that
comparison is only usable through the frozen axiom `Lean.Level.instLawfulBEqLevel`
(`Verify/Axioms.lean`).  Pattern-matching `.param` and comparing only `Name`s keeps the check —
and `uioOwnLevels_iff` — free of every frozen axiom. -/
def uioOwnLevels : List Name → List Level → Bool
  | [], [] => true
  | p :: ps, .param q :: us => p == q && uioOwnLevels ps us
  | _, _ => false

/-- **The specification of the guard**, transcribed from `check_uniform_ind_occs` with the
visitor's pruning built in.  `names` are the block's member names, `lps` its level parameters,
`np` its `nparams`, `d` the binder depth (C++'s `offset`) at which `e` sits.

**Installed since 2026-09-02** as `Lean4Lean.noNonUniformOcc`, under different names so that this
file stays a specification; `uio_impl_eq` (§3.0) proves the two are the same function. -/
def uioOk (names : List Name) (lps : List Name) (np : Nat) : Nat → Expr → Bool
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .lit _ => true
  | _, .const c us => !names.contains c || (np == 0 && uioOwnLevels lps us)
  | d, .mdata _ e => uioOk names lps np d e
  | d, .proj _ _ e => uioOk names lps np d e
  | d, .lam _ t b _ => uioOk names lps np d t && uioOk names lps np (d + 1) b
  | d, .forallE _ t b _ => uioOk names lps np d t && uioOk names lps np (d + 1) b
  | d, .letE _ t v b _ =>
    uioOk names lps np d t && uioOk names lps np d v && uioOk names lps np (d + 1) b
  | d, .app f a =>
    match uioFn (.app f a) with
    | .const c us =>
      if names.contains c && !decide (np < uioNArgs (.app f a)) then
        uioNArgs (.app f a) == np && uioArgsOk d (.app f a) && uioOwnLevels lps us
      else uioOk names lps np d f && uioOk names lps np d a
    | _ => uioOk names lps np d f && uioOk names lps np d a

/-- Rejection wrapper, in the shape of `checkNoLooseBVars`/`checkNoNestedAux`.  Installed as
`Lean4Lean.checkUniformIndOccs`; `uio_impl_check_eq` proves this is it.

The message names the **constructor** rather than the offending datatype, where C++ names the
datatype (`"invalid occurrence of datatype '" << const_name(fn) << "' being declared"`).  Matching
that would mean returning the offending constant, i.e. an `Option Name` in place of the `Bool`;
see §8.  Nothing observable depends on the text — the arena grades on accept/reject, not on
`stderr` — so this is a wording note, not a divergence. -/
def uioCheck (names : List Name) (lps : List Name) (np : Nat) (n : Name) (e : Expr) :
    Except Exception Unit := do
  unless uioOk names lps np 0 e do
    throw <| .other s!"invalid occurrence of a datatype being declared in '{n}': it must be \
      applied to the parameters and universe levels of the mutual declaration"

/-! ### 3.0 The specification IS the implementation

Since 2026-09-02 the check is **installed**: `Environment.addInductive`'s pre-`run` guard loop
calls `Lean4Lean.checkUniformIndOccs (types.map (·.name)) lparams nparams` on every constructor
type, in the inner loop only, exactly where C++ calls `check_uniform_ind_occs`.  The
implementation's names are deliberately different from this file's (`spineNArgs`/`spineHead`/
`isParamArg`/`spineParamArgs`/`ownLevels`/`noNonUniformOcc`/`checkUniformIndOccs` against
`uioNArgs`/`uioFn`/`uioIsParamArg`/`uioArgsOk`/`uioOwnLevels`/`uioOk`/`uioCheck`) so that this
file stays a *specification* rather than becoming a second copy of the code.

That only helps if the two are provably the same function, which is what this subsection does, one
`=` per definition and `uio_impl_eq` for the whole check.  Everything downstream then transfers:
`uioOk_iff` becomes the exactness lemma **of the installed check**, `uio_ok_of_occ` its
no-false-rejection lemma, and `uio_naive_too_strong` says that *the installed check's* pruning is
not optional.  §5 and §6's `#eval` guards are stated with `Lean4Lean.noNonUniformOcc` — the real
one — for the same reason: a table that agreed with its own twin would measure nothing.

These are pointwise equalities of two structurally identical recursions, so each is the same case
split twice; none of them uses an axiom (§9). -/

theorem uio_impl_nargs : ∀ e : Expr, uioNArgs e = _root_.Lean4Lean.spineNArgs e
  | .app f _ => by rw [uioNArgs, _root_.Lean4Lean.spineNArgs, uio_impl_nargs f]
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _
  | .mdata _ _ | .proj _ _ _ | .lam .. | .forallE .. | .letE .. => rfl

theorem uio_impl_head : ∀ e : Expr, uioFn e = _root_.Lean4Lean.spineHead e
  | .app f _ => by rw [uioFn, _root_.Lean4Lean.spineHead, uio_impl_head f]
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _
  | .mdata _ _ | .proj _ _ _ | .lam .. | .forallE .. | .letE .. => rfl

theorem uio_impl_isParamArg (d i : Nat) : ∀ a : Expr,
    uioIsParamArg d i a = _root_.Lean4Lean.isParamArg d i a
  | .bvar _ => rfl
  | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ | .app _ _
  | .mdata _ _ | .proj _ _ _ | .lam .. | .forallE .. | .letE .. => rfl

theorem uio_impl_argsOk (d : Nat) : ∀ e : Expr,
    uioArgsOk d e = _root_.Lean4Lean.spineParamArgs d e
  | .app f a => by
    rw [uioArgsOk, _root_.Lean4Lean.spineParamArgs, uio_impl_argsOk d f, uio_impl_isParamArg,
      uio_impl_nargs]
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _
  | .mdata _ _ | .proj _ _ _ | .lam .. | .forallE .. | .letE .. => rfl

theorem uio_impl_ownLevels : ∀ (lps : List Name) (us : List Level),
    uioOwnLevels lps us = _root_.Lean4Lean.ownLevels lps us
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, .param q :: us => by
    rw [uioOwnLevels, _root_.Lean4Lean.ownLevels, uio_impl_ownLevels ps us]
  | _ :: _, .zero :: _ | _ :: _, .succ _ :: _
  | _ :: _, .max _ _ :: _ | _ :: _, .imax _ _ :: _ | _ :: _, .mvar _ :: _ => rfl

/-- **The specification and the installed check are the same function.**  So `uioOk_iff` is the
exactness lemma of `Lean4Lean.noNonUniformOcc` itself, and every other result in §3 is about the
real check. -/
theorem uio_impl_eq (names lps : List Name) (np : Nat) : ∀ (d : Nat) (e : Expr),
    uioOk names lps np d e = _root_.Lean4Lean.noNonUniformOcc names lps np d e
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .lit _ => rfl
  | _, .const c us => by
    rw [uioOk, _root_.Lean4Lean.noNonUniformOcc, uio_impl_ownLevels]
  | d, .mdata _ e => by
    rw [uioOk, _root_.Lean4Lean.noNonUniformOcc, uio_impl_eq names lps np d e]
  | d, .proj _ _ e => by
    rw [uioOk, _root_.Lean4Lean.noNonUniformOcc, uio_impl_eq names lps np d e]
  | d, .lam _ t b _ => by
    rw [uioOk, _root_.Lean4Lean.noNonUniformOcc, uio_impl_eq names lps np d t,
      uio_impl_eq names lps np (d+1) b]
  | d, .forallE _ t b _ => by
    rw [uioOk, _root_.Lean4Lean.noNonUniformOcc, uio_impl_eq names lps np d t,
      uio_impl_eq names lps np (d+1) b]
  | d, .letE _ t v b _ => by
    rw [uioOk, _root_.Lean4Lean.noNonUniformOcc, uio_impl_eq names lps np d t,
      uio_impl_eq names lps np d v, uio_impl_eq names lps np (d+1) b]
  | d, .app f a => by
    rw [uioOk, _root_.Lean4Lean.noNonUniformOcc, uio_impl_head (.app f a)]
    cases _root_.Lean4Lean.spineHead (.app f a) with
    | const c us =>
      simp only []
      rw [uio_impl_nargs (.app f a), uio_impl_argsOk, uio_impl_ownLevels,
        uio_impl_eq names lps np d f, uio_impl_eq names lps np d a]
    | _ =>
      simp only []
      rw [uio_impl_eq names lps np d f, uio_impl_eq names lps np d a]

/-- The wrappers too — so the `Except`-level statement transfers, not merely the `Bool` one. -/
theorem uio_impl_check_eq (names lps : List Name) (np : Nat) (n : Name) (e : Expr) :
    uioCheck names lps np n e = _root_.Lean4Lean.checkUniformIndOccs names lps np n e := by
  rw [uioCheck, _root_.Lean4Lean.checkUniformIndOccs, uio_impl_eq]

theorem uioArgs_length : ∀ e : Expr, (uioArgs e).length = uioNArgs e
  | .app f _ => by rw [uioArgs, uioNArgs, List.length_append, uioArgs_length f]; rfl
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _
  | .mdata _ _ | .proj _ _ _ | .lam .. | .forallE .. | .letE .. => rfl

/-- `a` is the `i`-th parameter bound variable as seen from depth `d`. -/
def UIOParamArg (d i : Nat) (a : Expr) : Prop := ∃ j, a = .bvar j ∧ j + 1 + i = d

def UIOArgsSpec (d : Nat) (as : List Expr) : Prop :=
  ∀ i a, as[i]? = some a → UIOParamArg d i a

theorem uioIsParamArg_iff {d i : Nat} {a : Expr} :
    uioIsParamArg d i a = true ↔ UIOParamArg d i a := by
  unfold UIOParamArg
  cases a with
  | bvar j => simp [uioIsParamArg]
  | _ => simp [uioIsParamArg]

theorem uioArgsSpec_append {d : Nat} {as : List Expr} {a : Expr} :
    UIOArgsSpec d (as ++ [a]) ↔ UIOArgsSpec d as ∧ UIOParamArg d as.length a := by
  unfold UIOArgsSpec
  constructor
  · intro h
    refine ⟨fun i b hb => h i b ?_, h as.length a ?_⟩
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hb).1]; exact hb
    · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  · intro ⟨h1, h2⟩ i b hb
    have hlen : i < as.length + 1 := by
      have h := (List.getElem?_eq_some_iff.1 hb).1
      simpa using h
    rcases Nat.lt_or_ge i as.length with hi | hi
    · exact h1 i b (by rwa [List.getElem?_append_left hi] at hb)
    · have hie : i = as.length := by omega
      subst hie
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hb
      simp at hb
      subst hb
      exact h2

theorem uioArgsOk_iff : ∀ (d : Nat) (e : Expr),
    uioArgsOk d e = true ↔ UIOArgsSpec d (uioArgs e)
  | d, .app f a => by
    rw [uioArgs, uioArgsOk, Bool.and_eq_true, uioArgsOk_iff d f, uioIsParamArg_iff,
      uioArgsSpec_append, uioArgs_length]
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const _ _ | _, .lit _
  | _, .mdata _ _ | _, .proj _ _ _ | _, .lam .. | _, .forallE .. | _, .letE .. => by
    simp [uioArgsOk, uioArgs, UIOArgsSpec]

theorem uioOwnLevels_iff : ∀ (lps : List Name) (us : List Level),
    uioOwnLevels lps us = true ↔ us = lps.map .param
  | [], [] => by simp [uioOwnLevels]
  | [], _ :: _ => by simp [uioOwnLevels]
  | _ :: _, [] => by simp [uioOwnLevels]
  | p :: ps, .param q :: us => by
    rw [uioOwnLevels, Bool.and_eq_true, uioOwnLevels_iff ps us]
    simp only [List.map_cons, List.cons.injEq, Level.param.injEq, beq_iff_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩
  | _ :: _, .zero :: _ | _ :: _, .succ _ :: _
  | _ :: _, .max _ _ :: _ | _ :: _, .imax _ _ :: _
  | _ :: _, .mvar _ :: _ => by simp [uioOwnLevels]

/-! ### 3.0 The condition in `Prop` -/

/-- **C++'s requirement at one visited occurrence node**, in `Prop` with real equalities: the
occurrence is applied to exactly `np` arguments, at the block's own levels, and those arguments
are the parameter bound variables. -/
def UIOOccOk (lps : List Name) (np d : Nat) (us : List Level) (as : List Expr) : Prop :=
  as.length = np ∧ us = lps.map .param ∧ UIOArgsSpec d as

/-- **C++'s `offset >= nparams` conjunct is redundant.**  It is subsumed by the per-argument
`is_bvar(args[i], offset - 1 - i)` loop, whose `unsigned` arithmetic it exists to protect. -/
theorem uio_occOk_np_le_d {lps np d us as} (h : UIOOccOk lps np d us as) : np ≤ d := by
  obtain ⟨hlen, _, hargs⟩ := h
  match np, hlen with
  | 0, _ => exact Nat.zero_le _
  | np + 1, hlen =>
    have hlt : np < as.length := by omega
    obtain ⟨a, ha⟩ : ∃ a, as[np]? = some a := ⟨as[np], List.getElem?_eq_getElem hlt⟩
    obtain ⟨j, _, hj⟩ := hargs np a ha
    omega

/-- The `Prop`-side mirror of `uioOk`: the same recursion with `∈`/`=`/`∀` in place of
`contains`/`==`/`Bool`, and with **C++'s pruning built in** — at a saturated block occurrence the
children are not visited. -/
def UIOCond (names : List Name) (lps : List Name) (np : Nat) : Nat → Expr → Prop
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .lit _ => True
  | d, .const c us => c ∈ names → UIOOccOk lps np d us []
  | d, .mdata _ e => UIOCond names lps np d e
  | d, .proj _ _ e => UIOCond names lps np d e
  | d, .lam _ t b _ => UIOCond names lps np d t ∧ UIOCond names lps np (d + 1) b
  | d, .forallE _ t b _ => UIOCond names lps np d t ∧ UIOCond names lps np (d + 1) b
  | d, .letE _ t v b _ =>
    UIOCond names lps np d t ∧ UIOCond names lps np d v ∧ UIOCond names lps np (d + 1) b
  | d, .app f a =>
    match uioFn (.app f a) with
    | .const c us =>
      if c ∈ names ∧ uioNArgs (.app f a) ≤ np then
        UIOOccOk lps np d us (uioArgs (.app f a))
      else UIOCond names lps np d f ∧ UIOCond names lps np d a
    | _ => UIOCond names lps np d f ∧ UIOCond names lps np d a

/-- **The exactness lemma** — the analogue of `noLooseBVars_iff`.  Without it a check that
decides *more* than intended silently refuses legitimate declarations, and every other instrument
in this file would still pass. -/
theorem uioOk_iff (names lps : List Name) (np : Nat) : ∀ (d : Nat) (e : Expr),
    uioOk names lps np d e = true ↔ UIOCond names lps np d e
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .lit _ => by
    simp [uioOk, UIOCond]
  | d, .const c us => by
    simp only [uioOk, UIOCond, UIOOccOk, UIOArgsSpec, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, Bool.and_eq_true, List.length_nil, decide_eq_false_iff_not,
      List.contains_eq_mem, uioOwnLevels_iff]
    constructor
    · rintro (h | ⟨h1, h2⟩) hm
      · exact absurd hm h
      · exact ⟨h1.symm, h2, by simp⟩
    · intro h
      by_cases hm : c ∈ names
      · obtain ⟨h1, h2, _⟩ := h hm; exact Or.inr ⟨h1.symm, h2⟩
      · exact Or.inl hm
  | d, .mdata _ e => by rw [uioOk, UIOCond, uioOk_iff names lps np d e]
  | d, .proj _ _ e => by rw [uioOk, UIOCond, uioOk_iff names lps np d e]
  | d, .lam _ t b _ => by
    rw [uioOk, UIOCond, Bool.and_eq_true, uioOk_iff names lps np d t,
      uioOk_iff names lps np (d+1) b]
  | d, .forallE _ t b _ => by
    rw [uioOk, UIOCond, Bool.and_eq_true, uioOk_iff names lps np d t,
      uioOk_iff names lps np (d+1) b]
  | d, .letE _ t v b _ => by
    rw [uioOk, UIOCond, Bool.and_eq_true, Bool.and_eq_true, uioOk_iff names lps np d t,
      uioOk_iff names lps np d v, uioOk_iff names lps np (d+1) b, and_assoc]
  | d, .app f a => by
    rw [uioOk, UIOCond]
    cases hfn : uioFn (.app f a) with
    | const c us =>
      simp only []
      by_cases hm : c ∈ names
      · by_cases hn : uioNArgs (.app f a) ≤ np
        · rw [if_pos (show (names.contains c && !decide (np < uioNArgs (.app f a))) = true from
              by simp [hm, Nat.not_lt.2 hn]),
            if_pos (show c ∈ names ∧ uioNArgs (.app f a) ≤ np from ⟨hm, hn⟩),
            UIOOccOk, Bool.and_eq_true, Bool.and_eq_true, uioArgsOk_iff,
            uioOwnLevels_iff, beq_iff_eq, uioArgs_length]
          exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h3⟩, h2⟩⟩
        · rw [if_neg (show ¬(names.contains c && !decide (np < uioNArgs (.app f a))) = true from
              by simp [Nat.lt_of_not_le hn]),
            if_neg (show ¬(c ∈ names ∧ uioNArgs (.app f a) ≤ np) from fun h => hn h.2),
            Bool.and_eq_true, uioOk_iff names lps np d f, uioOk_iff names lps np d a]
      · rw [if_neg (show ¬(names.contains c && !decide (np < uioNArgs (.app f a))) = true from
              by simp [hm]),
          if_neg (show ¬(c ∈ names ∧ uioNArgs (.app f a) ≤ np) from fun h => hm h.1),
          Bool.and_eq_true, uioOk_iff names lps np d f, uioOk_iff names lps np d a]
    | _ =>
      simp only []
      rw [Bool.and_eq_true, uioOk_iff names lps np d f, uioOk_iff names lps np d a]

/-- **The exactness lemma of the installed check.**  `uioOk_iff` re-pointed at the installed check: `Lean4Lean.noNonUniformOcc` decides `UIOCond`
and nothing else. -/
theorem uio_impl_iff (names lps : List Name) (np d : Nat) (e : Expr) :
    _root_.Lean4Lean.noNonUniformOcc names lps np d e = true ↔ UIOCond names lps np d e := by
  rw [← uio_impl_eq]; exact uioOk_iff names lps np d e

/-! ### 3.1 The pruning is not optional

The naive reading — "every subterm whose head is a block constant applied to at most `np`
arguments is applied to exactly `np`" — is **not** the condition C++ decides, and is
unsatisfiable at every legitimate block with `np ≥ 1`.

This is the single most important thing to have checked about the port, because getting it wrong
would have installed a guard that rejects `List`, and every *rejection* statement about such a
guard would still have been provable.  Via `uio_impl_eq` this is a statement about the installed
`Lean4Lean.noNonUniformOcc`, and `uio_uioL_uniform` (§7) is the concrete dual at a `np = 1`
block. -/

def uioOkNaive (names : List Name) (lps : List Name) (np : Nat) : Nat → Expr → Bool
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .lit _ => true
  | _, .const c us => !names.contains c || (np == 0 && uioOwnLevels lps us)
  | d, .mdata _ e => uioOkNaive names lps np d e
  | d, .proj _ _ e => uioOkNaive names lps np d e
  | d, .lam _ t b _ => uioOkNaive names lps np d t && uioOkNaive names lps np (d + 1) b
  | d, .forallE _ t b _ => uioOkNaive names lps np d t && uioOkNaive names lps np (d + 1) b
  | d, .letE _ t v b _ =>
    uioOkNaive names lps np d t && uioOkNaive names lps np d v && uioOkNaive names lps np (d + 1) b
  | d, .app f a =>
    (match uioFn (.app f a) with
     | .const c us =>
       if names.contains c && !decide (np < uioNArgs (.app f a)) then
         uioNArgs (.app f a) == np && uioArgsOk d (.app f a) && uioOwnLevels lps us
       else true
     | _ => true)
    && uioOkNaive names lps np d f && uioOkNaive names lps np d a

@[simp] theorem uioFn_const {c : Name} {us : List Level} :
    uioFn (.const c us) = .const c us := rfl
@[simp] theorem uioArgs_const {c : Name} {us : List Level} : uioArgs (.const c us) = [] := rfl
@[simp] theorem uioNArgs_const {c : Name} {us : List Level} : uioNArgs (.const c us) = 0 := rfl

theorem uio_naive_too_strong {names lps : List Name} {np : Nat} {I : Name} {ls : List Level}
    (hI : names.contains I = true) (hnp : np ≠ 0) : ∀ (d : Nat) (e : Expr),
    uioFn e = .const I ls → uioOkNaive names lps np d e = false
  | d, .app f a, hf => by
    rw [uioOkNaive, uio_naive_too_strong hI hnp d f (by rwa [uioFn] at hf)]
    simp
  | _, .const c _, hf => by
    cases hf
    rw [uioOkNaive, hI, Bool.not_true, Bool.false_or, beq_eq_false_iff_ne.2 hnp,
      Bool.false_and]
  | _, .bvar _, hf | _, .fvar _, hf | _, .mvar _, hf | _, .sort _, hf | _, .lit _, hf
  | _, .mdata _ _, hf | _, .proj _ _ _, hf | _, .lam .., hf | _, .forallE .., hf
  | _, .letE .., hf => by simp [uioFn] at hf

/-! ### 3.2 Instrument 7's dual: nothing legitimate is refused -/

def uioMkApp (f : Expr) : List Expr → Expr
  | [] => f
  | a :: as => uioMkApp (.app f a) as

theorem uioFn_uioMkApp : ∀ (as : List Expr) (f : Expr), uioFn (uioMkApp f as) = uioFn f
  | [], _ => rfl
  | a :: as, f => by rw [uioMkApp, uioFn_uioMkApp as, uioFn]

theorem uioArgs_uioMkApp : ∀ (as : List Expr) (f : Expr),
    uioArgs (uioMkApp f as) = uioArgs f ++ as
  | [], _ => by rw [uioMkApp, List.append_nil]
  | a :: as, f => by
    rw [uioMkApp, uioArgs_uioMkApp as, uioArgs, List.append_assoc]; rfl

theorem uioNArgs_uioMkApp (as : List Expr) (f : Expr) :
    uioNArgs (uioMkApp f as) = uioNArgs f + as.length := by
  rw [← uioArgs_length, uioArgs_uioMkApp, List.length_append, uioArgs_length]

theorem uioMkApp_cons_isApp : ∀ (as : List Expr) (f a : Expr),
    ∃ g b, uioMkApp f (a :: as) = .app g b
  | [], f, a => ⟨f, a, rfl⟩
  | b :: bs, f, a => by rw [uioMkApp]; exact uioMkApp_cons_isApp bs (.app f a) b

/-- **No uniform occurrence is refused.**  `uioOk` accepts a block occurrence presented as the
block's own constant, at the block's own levels, applied to exactly `np` arguments that are the
parameter bound variables -- for every `np`, the `np = 0` (bare constant) case included.

This is instrument 7's dual for the candidate guard: a check that rejected everything would
satisfy every rejection statement about it, and this rules that out. -/
theorem uio_ok_of_occ {names lps : List Name} {np d : Nat} {I : Name} {as : List Expr}
    (hI : names.contains I = true) (hlen : as.length = np) (hargs : UIOArgsSpec d as) :
    uioOk names lps np d (uioMkApp (.const I (lps.map .param)) as) = true := by
  match as, hlen with
  | [], hlen =>
    have hnp : np = 0 := hlen.symm
    subst hnp
    rw [uioMkApp, uioOk, (uioOwnLevels_iff lps (lps.map .param)).2 rfl,
      show ((0 : Nat) == 0 && true) = true from rfl, Bool.or_true]
  | a :: as, hlen =>
    obtain ⟨g, b, hgb⟩ := uioMkApp_cons_isApp as (.const I (lps.map .param)) a
    have hfn : uioFn (.app g b) = .const I (lps.map .param) := by
      rw [← hgb, uioFn_uioMkApp, uioFn_const]
    have hn : uioNArgs (.app g b) = np := by
      rw [← hgb, uioNArgs_uioMkApp, uioNArgs_const, Nat.zero_add, hlen]
    have hargs' : uioArgs (.app g b) = a :: as := by
      rw [← hgb, uioArgs_uioMkApp, uioArgs_const, List.nil_append]
    rw [hgb, uioOk, hfn]
    simp only []
    rw [if_pos (show (names.contains I && !decide (np < uioNArgs (.app g b))) = true from
      by simp [hn, show I ∈ names from by simpa using hI])]
    rw [hn, Bool.and_eq_true, Bool.and_eq_true, uioArgsOk_iff, hargs', uioOwnLevels_iff]
    exact ⟨⟨beq_self_eq_true _, hargs⟩, rfl⟩

/-- `uio_ok_of_occ` at the **installed** check, spelled out rather than left to `uio_impl_eq`:
`Lean4Lean.noNonUniformOcc` accepts a block occurrence presented as the block's own constant, at
the block's own levels, applied to exactly `np` parameter bound variables.

This is the fact that must hold for `Lean4Lean.rejectsNonUniform` to be worth anything: a check
that rejected everything would satisfy every rejection statement about it. -/
theorem uio_impl_ok_of_occ {names lps : List Name} {np d : Nat} {I : Name} {as : List Expr}
    (hI : names.contains I = true) (hlen : as.length = np) (hargs : UIOArgsSpec d as) :
    _root_.Lean4Lean.noNonUniformOcc names lps np d
      (uioMkApp (.const I (lps.map .param)) as) = true := by
  rw [← uio_impl_eq]; exact uio_ok_of_occ hI hlen hargs

/-! ### 3.3 Instrument 7: the degenerate instance

`np = 0` is the degenerate instance, and it is **not** vacuous for this check: C++ still demands
the block's own levels at a bare constant occurrence (table cases T7/T8).  Three facts, so that
none of §3's statements is reported as a win without being instantiated there:

* `uio_ok_of_occ`'s hypotheses are satisfiable at `np = 0` (`uio_deg_ok`);
* `uio_uniformOcc_iff`'s two sides are both *inhabited* at `D.np = 0` — the trigger fires on a
  bare block constant at the block's own levels (`uio_deg_uniformOcc`);
* `uio_naive_too_strong` is **empty** at `np = 0`, and correctly so: at `np = 0` the pruning
  changes nothing, because `uioOk` never prunes there either (`uio_naive_eq_at_np_zero`).  So the
  `np ≠ 0` premise is forced rather than convenient. -/

theorem uio_deg_ok (I : Name) : uioOk [I] [] 0 0 (uioMkApp (.const I []) []) = true :=
  uio_ok_of_occ (by simp) rfl (fun i a h => absurd h nofun)

theorem uio_naive_eq_at_np_zero (names lps : List Name) : ∀ (d : Nat) (e : Expr),
    uioOkNaive names lps 0 d e = uioOk names lps 0 d e
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .lit _ | _, .const _ _ => rfl
  | d, .mdata _ e => by
    rw [uioOkNaive, uioOk, uio_naive_eq_at_np_zero names lps d e]
  | d, .proj _ _ e => by
    rw [uioOkNaive, uioOk, uio_naive_eq_at_np_zero names lps d e]
  | d, .lam _ t b _ => by
    rw [uioOkNaive, uioOk, uio_naive_eq_at_np_zero names lps d t,
      uio_naive_eq_at_np_zero names lps (d+1) b]
  | d, .forallE _ t b _ => by
    rw [uioOkNaive, uioOk, uio_naive_eq_at_np_zero names lps d t,
      uio_naive_eq_at_np_zero names lps (d+1) b]
  | d, .letE _ t v b _ => by
    rw [uioOkNaive, uioOk, uio_naive_eq_at_np_zero names lps d t,
      uio_naive_eq_at_np_zero names lps d v, uio_naive_eq_at_np_zero names lps (d+1) b]
  | d, .app f a => by
    have hn : uioNArgs (.app f a) = uioNArgs f + 1 := rfl
    rw [uioOkNaive, uioOk, uio_naive_eq_at_np_zero names lps d f,
      uio_naive_eq_at_np_zero names lps d a]
    cases hfn : uioFn (.app f a) with
    | const c us =>
      simp only []
      have hcond : ¬((names.contains c && !decide (0 < uioNArgs (.app f a))) = true) := by
        simp [hn]
      simp only [if_neg hcond, Bool.true_and]
    | _ => simp only []; rw [Bool.true_and]

/-! ## 4. Does it coincide with `VInductDecl'.uniformOcc?`

`Theory/Inductive/Restore.lean`'s `VInductDecl'.uniformOcc? D k e` fires when `e.spineFn` is a
block member at `D.ownLvls` and `e.spineArgs.take D.np = bvars k D.np`, returning the residual
`e.spineArgs.drop D.np`.  Its `k` is the number of binders **above the block's parameter
telescope**, so C++'s `offset` is `k + D.np` and `VExpr.bvars k D.np = [#(k+np-1), …, #k]` is
exactly C++'s `#(offset-1) … #(offset-nparams)`: C++'s `offset >= nparams` conjunct is, on this
side, the mere existence of the `Nat` `k`.  (That is why `uniformOcc?` is parameterised on `k`
and not on the absolute depth: the side condition is baked into the parameterisation, and cannot
be violated by any of its call sites, all of which are inside the parameter telescope.)

The one *behavioural* difference is over-application: C++ descends through an over-applied node
and lands on its `np`-prefix, whereas `uniformOcc?` fires at the outermost node and carries the
excess as the residual `rest`.  That is not a difference in the condition, and
`uio_uniformOcc_iff_prefix` says so exactly. -/

theorem uio_spineFn_spineFn : ∀ e : VExpr, e.spineFn.spineFn = e.spineFn
  | .app f _ => uio_spineFn_spineFn f
  | .bvar _ | .sort _ | .const _ _ | .lam _ _ | .forallE _ _ => rfl

theorem uio_spineArgs_spineFn : ∀ e : VExpr, e.spineFn.spineArgs = []
  | .app f _ => uio_spineArgs_spineFn f
  | .bvar _ | .sort _ | .const _ _ | .lam _ _ | .forallE _ _ => rfl

/-- **C++'s condition at one visited node**, transcribed at `VExpr`: the spine head is a block
member, at the block's own levels, applied to *exactly* `D.np` arguments which are the parameter
bound variables as seen `k` binders above the parameter telescope (so C++'s `offset` is `k+D.np`
and its `offset >= nparams` conjunct is the existence of `k`). -/
def UIOVNode (D : VInductDecl') (k : Nat) (e : VExpr) : Prop :=
  ∃ (n : Lean.Name) (ls : List VLevel) (j : Nat), e.spineFn = .const n ls ∧
    D.memberIdx n = some j ∧ ls = D.ownLvls ∧ e.spineArgs = VExpr.bvars k D.np

/-- The `D.np`-prefix of a spine -- the node C++ actually checks when the occurrence is
over-applied (it descends through the over-applied node and checks this subterm). -/
def uioVPrefix (D : VInductDecl') (e : VExpr) : VExpr :=
  VExpr.mkApp e.spineFn (e.spineArgs.take D.np)

theorem uioVPrefix_spineFn (D : VInductDecl') (e : VExpr) :
    (uioVPrefix D e).spineFn = e.spineFn := by
  rw [uioVPrefix, VExpr.spineFn_mkApp, uio_spineFn_spineFn]

theorem uioVPrefix_spineArgs (D : VInductDecl') (e : VExpr) :
    (uioVPrefix D e).spineArgs = e.spineArgs.take D.np := by
  rw [uioVPrefix, VExpr.spineArgs_mkApp, uio_spineArgs_spineFn, List.nil_append]

/-- **The trigger of the restoration operator IS the C++ pre-pass's condition.**

`VInductDecl'.uniformOcc?` fires at `e` exactly when C++'s `check_uniform_ind_occs` would accept
the `D.np`-prefix of `e`'s spine -- which is the node C++ checks, whether `e` is saturated (then
the prefix is `e`) or over-applied (then C++ descends and reaches the prefix). -/
theorem uio_uniformOcc_iff_prefix (D : VInductDecl') (k : Nat) (e : VExpr) :
    (D.uniformOcc? k e).isSome = true ↔ UIOVNode D k (uioVPrefix D e) := by
  rw [UIOVNode, uioVPrefix_spineFn, uioVPrefix_spineArgs, VInductDecl'.uniformOcc?]
  cases hs : e.spineFn with
  | const n ls =>
    simp only []
    cases hm : D.memberIdx n with
    | none => simp [hm]
    | some j =>
      simp only []
      by_cases hc : ls = D.ownLvls ∧ e.spineArgs.take D.np = VExpr.bvars k D.np
      · rw [if_pos hc]; exact ⟨fun _ => ⟨n, ls, j, rfl, hm, hc.1, hc.2⟩, fun _ => rfl⟩
      · rw [if_neg hc]
        refine ⟨fun h => absurd h (by simp), fun h => absurd ?_ hc⟩
        obtain ⟨n', ls', j', he, _, h1, h2⟩ := h
        cases he; exact ⟨h1, h2⟩
  | _ => simp

/-- **On the nodes C++ actually checks -- at most `D.np` arguments -- the two are literally the
same predicate.**  This is the case that decides whether a declaration is accepted. -/
theorem uio_uniformOcc_iff (D : VInductDecl') (k : Nat) {e : VExpr}
    (h : e.spineArgs.length ≤ D.np) :
    (D.uniformOcc? k e).isSome = true ↔ UIOVNode D k e := by
  rw [uio_uniformOcc_iff_prefix, uioVPrefix, List.take_of_length_le h,
    VExpr.mkApp_spineFn_spineArgs]

/-- §3.3's instrument-7 instance for §4: at `D.np = 0` both sides of `uio_uniformOcc_iff` are
inhabited, so the equivalence is not an equivalence of two empty predicates. -/
theorem uio_deg_uniformOcc {D : VInductDecl'} {n : Lean.Name} {j : Nat} (hnp : D.np = 0)
    (hm : D.memberIdx n = some j) (k : Nat) :
    (D.uniformOcc? k (.const n D.ownLvls)).isSome = true := by
  have hsa : (VExpr.const n D.ownLvls).spineArgs = [] := rfl
  rw [uio_uniformOcc_iff D k (e := .const n D.ownLvls) (by rw [hsa]; simp)]
  exact ⟨n, D.ownLvls, j, rfl, hm, rfl, by rw [hsa, hnp]; rfl⟩

/-- **The proof-side dividend of installing the pre-pass, at one node.**  If the trigger does
*not* fire at `e`, the pre-pass rejects the `D.np`-prefix of `e` -- so on a constructor type the
pre-pass has accepted, `VIndRestore.restore`'s fallthrough branch is unreachable at every subterm
whose spine head is a block member.  (The whole-expression version of that -- that the pruning
walk and `restore`'s recursion visit the same nodes -- is *not* proved here; it needs the
`Lean.Expr`-to-`VExpr` bridge, and this file deliberately does not build one.) -/
theorem uio_restore_none_forces_reject {D : VInductDecl'} {k : Nat} {e : VExpr}
    (h : D.uniformOcc? k e = none) : ¬ UIOVNode D k (uioVPrefix D e) := by
  rw [← uio_uniformOcc_iff_prefix]; rw [h]; exact fun hc => absurd hc (by simp)

/-! ## 5. What lean4lean does — and what it did before 2026-09-02

### 5.1 A unit table for the transcription

Eighteen hand-computed cases, each with the verdict `check_uniform_ind_occs` gives.  They pin the
three behaviours the prose above claims and nothing else would catch: **over-application
descends** (T4/T5/T6), **`letE` bumps its body but not its type** (T10/T10b), **`mdata` hides the
spine head** (T11), **parameters must be in declaration order** (T14/T15), and **an occurrence in
a parameter's own type is always rejected** (T13).  The `#eval` **throws**, so a transcription
that drifts fails the build. -/

structure UIOCase where
  label : String
  names : List Name
  lps : List Name
  np : Nat
  expr : Expr
  want : Bool

private def uioS0 : Expr := .sort .zero
private def uioPi (b : Expr) : Expr := .forallE `a uioS0 b .default
private def uioPi2 (b : Expr) : Expr := .forallE `a uioS0 (.forallE `b uioS0 b .default) .default
private def uioIc (us : List Level := []) : Expr := .const `uioI us

def uioCases : List UIOCase :=
  [ { label := "T1 saturated, in order", names := [`uioI], lps := [], np := 1
      expr := uioPi (.app (uioIc) (.bvar 0)), want := true }
  , { label := "T2 saturated, argument not the parameter", names := [`uioI], lps := [], np := 1
      expr := uioPi (.app (uioIc) uioS0), want := false }
  , { label := "T3 under-applied (bare constant at np=1)", names := [`uioI], lps := [], np := 1
      expr := uioPi (uioIc), want := false }
  , { label := "T4 over-applied, good prefix, clean index", names := [`uioI], lps := [], np := 1
      expr := uioPi (.app (.app (uioIc) (.bvar 0)) (.bvar 0)), want := true }
  , { label := "T5 over-applied, BAD prefix", names := [`uioI], lps := [], np := 1
      expr := uioPi (.app (.app (uioIc) uioS0) (.bvar 0)), want := false }
  , { label := "T6 over-applied, bad occurrence in an index", names := [`uioI], lps := [], np := 1
      expr := uioPi (.app (.app (uioIc) (.bvar 0)) (.app (uioIc) uioS0)), want := false }
  , { label := "T7 np=0, bare constant at own (empty) levels", names := [`uioI], lps := [], np := 0
      expr := uioIc, want := true }
  , { label := "T8 np=0, wrong levels", names := [`uioI], lps := [`u], np := 0
      expr := uioIc, want := false }
  , { label := "T9 saturated, wrong levels", names := [`uioI], lps := [`u], np := 1
      expr := uioPi (.app (uioIc) (.bvar 0)), want := false }
  , { label := "T9b saturated, own levels", names := [`uioI], lps := [`u], np := 1
      expr := uioPi (.app (uioIc [.param `u]) (.bvar 0)), want := true }
  , { label := "T10 letE bumps its body", names := [`uioI], lps := [], np := 1
      expr := .letE `x uioS0 uioS0 (.app (uioIc) (.bvar 0)) true, want := true }
  , { label := "T10b letE does not bump its type", names := [`uioI], lps := [], np := 1
      expr := .letE `x (.app (uioIc) (.bvar 0)) uioS0 uioS0 true, want := false }
  , { label := "T11 mdata hides the spine head", names := [`uioI], lps := [], np := 1
      expr := uioPi (.app (.mdata {} (uioIc)) (.bvar 0)), want := false }
  , { label := "T12 a constant outside the block", names := [`uioI], lps := [], np := 1
      expr := uioPi (.app (.const `uioJ []) uioS0), want := true }
  , { label := "T13 occurrence in a parameter's own type", names := [`uioI], lps := [], np := 1
      expr := .forallE `p (.app (uioIc) (.bvar 0)) uioS0 .default, want := false }
  , { label := "T14 np=2, parameters in order", names := [`uioI], lps := [], np := 2
      expr := uioPi2 (.app (.app (uioIc) (.bvar 1)) (.bvar 0)), want := true }
  , { label := "T15 np=2, parameters swapped", names := [`uioI], lps := [], np := 2
      expr := uioPi2 (.app (.app (uioIc) (.bvar 0)) (.bvar 1)), want := false }
  , { label := "T16 proj does not bump", names := [`uioI], lps := [], np := 1
      expr := uioPi (.proj `X 0 (.app (uioIc) (.bvar 0))), want := true } ]

#eval show Lean.CoreM Unit from do
  let mut bad : List String := []
  for c in uioCases do
    unless _root_.Lean4Lean.noNonUniformOcc c.names c.lps c.np 0 c.expr == c.want do
      bad := c.label :: bad
  unless bad.isEmpty do
    throwError "uio/table: the INSTALLED check (Lean4Lean.noNonUniformOcc) disagrees with the \
      transcribed check_uniform_ind_occs verdict on {bad.reverse}"
  -- The specification is not measured against its own twin: every case is run through the real
  -- check, and `uio_impl_eq` is what makes §3's exactness results apply to it.
  for c in uioCases do
    unless _root_.Lean4Lean.noNonUniformOcc c.names c.lps c.np 0 c.expr
        == uioOk c.names c.lps c.np 0 c.expr do
      throwError "uio/table: Lean4Lean.noNonUniformOcc and uioOk disagree on {c.label} -- \
        uio_impl_eq is FALSE and the port has drifted from the specification"
  -- §3.1 in action: the same T1 that the installed check accepts, the pruning-free reading
  -- refuses.
  let t1 := uioPi (.app (uioIc) (.bvar 0))
  unless _root_.Lean4Lean.noNonUniformOcc [`uioI] [] 1 0 t1 && !uioOkNaive [`uioI] [] 1 0 t1 do
    throwError "uio/table: the pruning-free reading no longer differs from the installed check -- \
      uio_naive_too_strong's premise has moved"
  logInfo s!"uio/table: {uioCases.length} cases, all agreeing with check_uniform_ind_occs and \
    with uioOk; the pruning-free reading refuses T1"

/-! ### 5.2 The gap, at a real declaration

`uioE`/`uioL` are the arena test `nested-nonuniform-param` (`tests/nested-nonuniform-param.lean`)
in kernel form: `uioL (α : Type)` is the nested vehicle, and

    uioE.mk : (w : Bool) → uioL (uioE Bool.false) → uioE w

has the nested occurrence `uioE Bool.false`, which supplies a *constant* where the parameter `w`
should be.  C++ throws at it (`args.size() == nparams` holds, `is_bvar(args[0], 0)` fails).
lean4lean **accepted** it until 2026-09-02; the arena outcome for that test is **`either`** and
lean4lean's recorded status was `accepted`
(`_results/lean4lean-local_nested-nonuniform-param.json`), which is why the suite reported 0 wrong
even while the gap was live.  **It now rejects**, and §7 proves that rather than observing it
(`uio_rejectsNonUniform_fires`); the `#eval` below throws if the acceptance ever comes back.

`uioUnusedCtorType` is the shape of the *other* test, `nested-unused-param` (outcome `reject`),
where the occurrence `uioE #0` **is** uniform and the payload is a malformed second nested
parameter.  `uioOk` returns `true` on it — the pre-pass is not what rejects it.  lean4lean does
reject it, by the `res.aux2nested.forM … checkType` in `Environment.addInductive` (the
lean4#14577 parameter check), with `(kernel) invalid projection w.1`.

Both `#eval`s **throw** when their verdict changes. -/

def uioLBlock : InductiveType :=
  { name := `uioL, type := .forallE `α (.sort 1) (.sort 1) .default
    ctors := [{ name := `uioL.mk
                type := .forallE `α (.sort 1) (.app (.const `uioL []) (.bvar 0)) .default }] }

def uioECtorType : Expr :=
  .forallE `w (.const `Bool [])
    (.forallE `l (.app (.const `uioL []) (.app (.const `uioE []) (.const `Bool.false [])))
      (.app (.const `uioE []) (.bvar 1)) .default) .default

def uioEBlock : InductiveType :=
  { name := `uioE, type := .forallE `w (.const `Bool []) (.sort 1) .default
    ctors := [{ name := `uioE.mk, type := uioECtorType }] }

/-- The `nested-unused-param` shape: the occurrence `uioE #0` IS uniform; the bad thing is the
second nested parameter, which the pre-pass says nothing about. -/
def uioUnusedCtorType : Expr :=
  .forallE `w (.const `Bool [])
    (.forallE `l (.app (.app (.const `uioL2 [])
        (.app (.const `uioE []) (.bvar 0))) (.proj `uioC 0 (.bvar 0)))
      (.app (.const `uioE []) (.bvar 1)) .default) .default

#eval show Lean.CoreM Unit from do
  let kenv := (← getEnv).toKernelEnv
  let env1 ← match Environment.addInductive kenv [] 1 [uioLBlock] false false with
    | .error e => throwError "uio/wit: the nested vehicle uioL was REJECTED \
        ({e.toMessageData {}}) -- the installed pre-pass refuses an ordinary uniform block, i.e. \
        the pruning is gone (see uio_naive_too_strong)"
    | .ok e => pure e
  match Environment.addInductive env1 [] 1 [uioEBlock] false false with
  | .error _ => pure ()
  | .ok _ =>
    throwError "uio/wit: lean4lean ACCEPTS the non-uniform block again -- row 116e's gap has \
      REOPENED; checkUniformIndOccs is no longer reached from Environment.addInductive"
  unless _root_.Lean4Lean.noNonUniformOcc [`uioE] [] 1 0 uioECtorType == false do
    throwError "uio/wit: the installed check no longer rejects the non-uniform constructor type"
  unless _root_.Lean4Lean.noNonUniformOcc [`uioE] [] 1 0 uioUnusedCtorType == true do
    throwError "uio/wit: the installed check now rejects the nested-unused-param shape, whose \
      occurrence is uniform -- it has stopped being a transcription of check_uniform_ind_occs"
  logInfo "uio/wit: row 116e's gap is CLOSED -- lean4lean REJECTS the non-uniform block (as C++ \
    does), still accepts the uniform nested vehicle uioL, and is silent on the \
    nested-unused-param shape, as C++ is"

/-! ### 5.3 The pre-pass does **not** subsume the gaps already priced

Ledger rows 113/116 turn on a **redex-headed** field, and 116e's finding is in the *opposite*
direction.  Three witnesses from `CanonGapMeasure.lean`, reproduced here as constructor types
only (this file does not import that one), all of which the pre-pass **accepts**:

* `uioRedexCtorType` — row 113's `cgmT.mk : ((fun x : Type => cgmT) Prop) → cgmT` at `np = 0`;
* `uioDepCtorType` / `uioJCtorType` — row 116's `cgmDep`/`cgmJ` pair, the one that refuted the
  canonicity guard at `Lean.Json`'s shape.

So the two gaps are independent: this one is not a repair of that one, and that one's refutation
does not carry over. The `#eval` **throws** if any of the three ever starts being rejected. -/

def uioRedexCtorType : Expr :=
  .forallE `a (.app (.lam `x (.sort (.succ .zero)) (.const `uioT []) .default) (.sort .zero))
    (.const `uioT []) .default

def uioDepCtorType : Expr :=
  .forallE `β (.forallE `x (.sort .zero) (.sort (.succ .zero)) .default)
    (.forallE `u (.sort .zero)
      (.forallE `h (.app (.bvar 1) (.bvar 0))
        (.app (.const `uioDep []) (.bvar 2)) .default) .default) .default

def uioJCtorType : Expr :=
  .forallE `h (.app (.const `uioDep []) (.lam `x (.sort .zero) (.const `uioJ []) .default))
    (.const `uioJ []) .default

#eval show Lean.CoreM Unit from do
  let mut bad : List String := []
  unless _root_.Lean4Lean.noNonUniformOcc [`uioT] [] 0 0 uioRedexCtorType do
    bad := "row 113 redex witness" :: bad
  unless _root_.Lean4Lean.noNonUniformOcc [`uioDep] [] 1 0 uioDepCtorType do
    bad := "row 116 cgmDep" :: bad
  unless _root_.Lean4Lean.noNonUniformOcc [`uioJ] [] 0 0 uioJCtorType do
    bad := "row 116 cgmJ" :: bad
  unless bad.isEmpty do
    throwError "uio/sep: the INSTALLED check now REJECTS {bad.reverse} -- rows 113/116 and 116e \
      are no longer independent, and the recommendation has to be re-derived"
  logInfo "uio/sep: the pre-pass accepts rows 113 and 116's witnesses -- every occurrence in them \
    is uniform, so 116e is a separate gap in the opposite direction"

/-! ## 6. Scans

Two populations, because row 116 was refuted by the second one after the first said 0:

* **`uio/scanA`** — every inductive block in the running environment (the `ConeJoin` closure), as
  **submitted**.  This is the population the check would actually see, since C++ runs it on `d`
  before `elim_nested_inductive_fn`.
* **`uio/scanB`** — the same blocks put through `ElimNestedInductive.run`, with the check re-run
  on the **auxiliary** constructor types.  C++ does *not* re-run the pre-pass there, so a
  violation here would not by itself refute the guard; it would refute any *specification* that
  assumed uniformity of the auxiliary block, which is what row 116's canonicity guard tried to do.

Both `#eval`s **throw** on a nonzero violation count. -/

#eval show Lean.CoreM Unit from do
  let env ← getEnv
  let mut blocks : Nat := 0; let mut ctors : Nat := 0; let mut viol : Nat := 0
  let mut ublocks : Nat := 0; let mut uctors : Nat := 0; let mut uviol : Nat := 0
  let mut violCtors : List Name := []
  let mut uviolCtors : List Name := []
  for (n, ci) in env.constants.toList do
    let .inductInfo v := ci | continue
    unless v.all.head? == some n do continue
    if v.isUnsafe then ublocks := ublocks + 1 else blocks := blocks + 1
    for m in v.all do
      let some (.inductInfo w) := env.find? m | continue
      for c in w.ctors do
        let some cci := env.find? c | continue
        let ok := _root_.Lean4Lean.noNonUniformOcc v.all v.levelParams v.numParams 0 cci.type
        if v.isUnsafe then
          uctors := uctors + 1
          unless ok do uviol := uviol + 1; uviolCtors := c :: uviolCtors
        else
          ctors := ctors + 1
          unless ok do viol := viol + 1; violCtors := c :: violCtors
  unless viol == 0 && uviol == 0 do
    throwError "uio/scanA: the INSTALLED check REJECTS stored declarations: {viol} safe \
      {violCtors.eraseDups.take 40}, {uviol} unsafe {uviolCtors.eraseDups.take 40} -- \
      installing it would break the arena"
  logInfo s!"uio/scanA: SUBMITTED FORM: SAFE {blocks} blocks / {ctors} ctors, violations {viol}; \
    UNSAFE {ublocks} blocks / {uctors} ctors, violations {uviol}"

#eval show Lean.CoreM Unit from do
  let lenv ← getEnv
  let kenv := lenv.toKernelEnv
  let mut tried : Nat := 0; let mut runFailed : List Name := []
  let mut auxCtors : Nat := 0; let mut auxViol : Nat := 0
  let mut badBlocks : List Name := []
  let mut nestedTried : Nat := 0
  for (n, ci) in lenv.constants.toList do
    let .inductInfo v := ci | continue
    unless v.all.head? == some n do continue
    if v.isUnsafe then continue
    let mut types : List InductiveType := []
    for m in v.all do
      let some (.inductInfo w) := lenv.find? m | continue
      let mut cs : List Constructor := []
      for c in w.ctors do
        let some cci := lenv.find? c | continue
        cs := cs ++ [{ name := c, type := cci.type }]
      types := types ++ [{ name := m, type := w.type, ctors := cs }]
    tried := tried + 1
    match (ElimNestedInductive.run 10000 v.numParams types kenv).run'
        { lvls := v.levelParams.map .param, newTypes := types.toArray } with
    | .error _ => runFailed := n :: runFailed
    | .ok res =>
      if res.aux2nested.length > 0 then nestedTried := nestedTried + 1
      let anames := res.types.map (·.name)
      let mut bad := false
      for t in res.types do
        for c in t.ctors do
          auxCtors := auxCtors + 1
          unless _root_.Lean4Lean.noNonUniformOcc anames v.levelParams v.numParams 0 c.type do
            auxViol := auxViol + 1; bad := true
      if bad then badBlocks := n :: badBlocks
  unless auxViol == 0 do
    throwError "uio/scanB: POST-ELIMINATION violations: {auxViol} auxiliary constructors in \
      {badBlocks.eraseDups.length} blocks {badBlocks.eraseDups.take 20} -- any specification \
      that assumes uniformity of the AUXILIARY block is refuted"
  unless runFailed.isEmpty do
    throwError "uio/scanB: ElimNestedInductive.run failed on {runFailed.length} blocks \
      {runFailed.take 10} -- the post-elimination population is no longer covered"
  logInfo s!"uio/scanB: POST-ELIMINATION: {tried} safe blocks through ElimNestedInductive.run \
    ({nestedTried} with a real nested occurrence), run failed on {runFailed.length}; \
    {auxCtors} auxiliary constructors, violations {auxViol}"


/-! ## 7. The installed check: `RejectsNonUniform` fires, and its hypothesis is inhabited

`Verify/Inductive/RunIdentity.lean` §6.2 proves `Lean4Lean.rejectsNonUniform`: if a block has a
constructor type the pre-pass refuses, `Environment.addInductive` refuses the block.  Its
hypothesis is a **negation**, so the statement is worth exactly as much as an inhabitant of that
negation, and no instrument in this repo inspects hypotheses.  Here is the inhabitant, and it is
the arena test that motivated the whole row: `nested-nonuniform-param`.

The dual — that the check is not identically `false`, i.e. that installing it does not reject
everything — is `uio_ok_of_occ` (nothing uniform is refused, via `uio_impl_eq` a statement about
the installed check), §6's two scans (0 violations in 7013 submitted and 7215 post-elimination
constructor types) and `uio_uioL_uniform` below (the nested *vehicle* still passes).  That dual is
not decoration: `uio_naive_too_strong` shows the pruning-free reading of C++'s condition **is**
identically `false` at every `np ≥ 1`, so "rejects everything" was a live failure mode of this
port rather than a hypothetical one. -/

/-- The arena's `nested-nonuniform-param` block violates `BlockUniformOccs` — the fourth conjunct
of the guard loop's postcondition.  **This is `RejectsNonUniform`'s hypothesis, inhabited.** -/
theorem uio_not_blockUniformOccs_uioE :
    ¬ _root_.Lean4Lean.BlockUniformOccs (List.map (·.name) [uioEBlock]) [] 1 [uioEBlock] := by
  intro h
  exact absurd (h _ (List.mem_singleton.2 rfl) _ (List.mem_singleton.2 rfl)) (by decide)

/-- **`rejectsNonUniform`, fired.**  `Environment.addInductive` rejects the arena's
`nested-nonuniform-param` block at every `env`, `ap` and `fuel` — a kernel proof, not an `#eval`:
the guard runs before `ElimNestedInductive.run`, so nothing `opaque` is in the way.  This is the
declaration lean4lean **accepted** until 2026-09-02 and C++ has always thrown on. -/
theorem uio_rejectsNonUniform_fires (env : Environment) (ap : Bool)
    (fuel : _root_.Lean4Lean.FuelConfig) (env' : Environment) :
    Environment.addInductive env [] 1 [uioEBlock] false ap fuel ≠ .ok env' :=
  _root_.Lean4Lean.rejectsNonUniform env [] 1 _ ap fuel uio_not_blockUniformOccs_uioE env'

/-- Instrument 7's **dual** at the same place: the nested *vehicle* `uioL` — an ordinary
`List`-shaped block with `np = 1` — still satisfies `BlockUniformOccs`, so the guard is not
"reject everything".  `uio_naive_too_strong` says the pruning-free reading fails exactly here. -/
theorem uio_uioL_uniform :
    _root_.Lean4Lean.BlockUniformOccs (List.map (·.name) [uioLBlock]) [] 1 [uioLBlock] := by
  intro t ht
  rw [List.mem_singleton] at ht; subst ht
  decide

/-! ## 8. The implementation, as installed

### Where it went — and it is exactly where this section recommended

One line in `Environment.addInductive`'s existing pre-`run` guard loop
(`Lean4Lean/Inductive/Add.lean`), in the **inner** loop only — C++ applies the pre-pass to
constructor types and not to member types:

```
      for ctor in indType.ctors do
        env.checkNoMVarNoFVar ctor.name ctor.type
        checkNoNestedAux ctor.name ctor.type
        checkNoLooseBVars ctor.name ctor.type
        checkUniformIndOccs (types.map (·.name)) lparams nparams ctor.name ctor.type   -- 2026-09-02
```

`types`, `lparams` and `nparams` are all in scope there.  The check sits **before**
`ElimNestedInductive.run`, which is where C++ puts it and where its purpose lies: it exists to
catch what later, `whnf`-using phases can no longer see.

### A pure structural check suffices, and needs no axiom

`uioOk` is an ordinary structural recursion on `Lean.Expr`.  It reads no cached header field, does
no `whnf`, and touches no `@[extern]` function except `Name.beq`, which the checker already uses
everywhere and whose `LawfulBEq` instance is provable (`[propext, Quot.sound]`) rather than
axiomatised.  In particular `uioOwnLevels` avoids `Lean.Level.beq`, whose lawfulness is the frozen
axiom `Lean.Level.instLawfulBEqLevel`; that is the same trade `checkNoLooseBVars` makes against
`Expr.looseBVarRange`/`Expr.mkData_eq`, and for the same reason — a frozen axiom's side condition
would otherwise appear in every consequence.  Guard 3 gains no entry.

Two adjustments this section flagged before installing:

1. **`Option Name` instead of `Bool`**, if C++'s exact message is wanted (see `uioCheck`).  **Not
   taken**: the port keeps the `Bool` and names the constructor rather than the offending
   datatype.  The arena grades accept/reject, not `stderr`, so this stays a wording note.  If it is
   ever wanted, the exactness lemma transfers by an `isNone` congruence over the same twelve cases.
2. **`guardLoop_*` lemmas** — row 112's sequencing error was exactly this: the guard loop's shape
   lemmas (`guardLoop_blockNoFVar` and friends in `Verify/Inductive/RunIdentity.lean`) must be
   re-proved against the new loop *before* the implementation edit lands, or the dependent proofs
   stop elaborating.  **Honoured**: the edit was held uncommitted while
   `guardLoop_ctors`/`guardLoop_blockNoFVar`/`guardLoop_ctors_closed`/`guardLoop_blockClosed` grew
   their fourth check and fourth conjunct (`BlockUniformOccs`), and the four dependent sites in
   `RunIdentity.lean` were repaired in the same round.

### Divergence entry: NOT needed for the check, needed for one side effect

Closing a *permissive* gap to match C++ is convergence, not divergence: after the change the two
kernels agree on exactly this input class, so there is nothing for `divergences.md` to record
about accept/reject behaviour.

What *would* need an entry is the **complexity**, on the same grounds as
`checkNoLooseBVars`'s: C++'s `for_each_offset_fn` memoises on `(pointer, offset)`, whereas
`Lean4Lean.noNonUniformOcc` is an uncached structural recursion, so on a heavily shared `Expr` DAG
it is exponential in the sharing where C++ is linear.  CLAUDE.md requires complexity blowups on inputs C++ handles
differently to be recorded, so a short entry belongs there — a paragraph in the existing
`checkNoLooseBVars` bullet's style, not a new accept/reject divergence.  **As of 2026-09-02
`divergences.md` has no such paragraph**; the check is installed and the entry is outstanding.
(Neither the implementation nor `divergences.md` is this file's stream to edit, so this is a flag,
not a fix.)
-/

/-! ## 9. Axiom guards

`#print axioms`, not the absence of a local `sorry`.  Everything here stays inside
`Verify/Guard.lean`'s three standard axioms; **no frozen axiom from `Verify/Axioms.lean`**, and
in particular not `Lean.Level.instLawfulBEqLevel`. -/

#print axioms Lean4Lean.UIOGuard.uioOwnLevels_iff
#print axioms Lean4Lean.UIOGuard.uioArgsOk_iff
#print axioms Lean4Lean.UIOGuard.uio_occOk_np_le_d
#print axioms Lean4Lean.UIOGuard.uioOk_iff
#print axioms Lean4Lean.UIOGuard.uio_naive_too_strong
#print axioms Lean4Lean.UIOGuard.uio_ok_of_occ
#print axioms Lean4Lean.UIOGuard.uio_uniformOcc_iff_prefix
#print axioms Lean4Lean.UIOGuard.uio_uniformOcc_iff
#print axioms Lean4Lean.UIOGuard.uio_deg_ok
#print axioms Lean4Lean.UIOGuard.uio_deg_uniformOcc
#print axioms Lean4Lean.UIOGuard.uio_naive_eq_at_np_zero
#print axioms Lean4Lean.UIOGuard.uio_restore_none_forces_reject
#print axioms Lean4Lean.UIOGuard.uio_impl_eq
#print axioms Lean4Lean.UIOGuard.uio_impl_check_eq
#print axioms Lean4Lean.UIOGuard.uio_impl_iff
#print axioms Lean4Lean.UIOGuard.uio_impl_ok_of_occ
#print axioms Lean4Lean.UIOGuard.uio_not_blockUniformOccs_uioE
#print axioms Lean4Lean.UIOGuard.uio_rejectsNonUniform_fires
#print axioms Lean4Lean.UIOGuard.uio_uioL_uniform

end UIOGuard
end Lean4Lean
