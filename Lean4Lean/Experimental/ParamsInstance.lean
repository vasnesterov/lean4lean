import Lean4Lean.Theory.Typing.PatternRules
import Lean4Lean.Experimental.SExpr

/-!
# The shape model's `Params`, instantiated

`Lean4Lean.Params` (`Experimental/SExpr.lean`) is the class `Experimental/Reflect/Capstone.lean`
consumes to prove `IsDefEqU.forallE_inv`.  This file builds an instance of it for **an
arbitrary environment with `VEnv.WF env`**, which is what `Theory/Typing/Injectivity.lean`'s
open statements need in order to stop being `Params`-relative.

## Why the file is here and not in `Theory/`

The two remaining fields — `classify` and `pat_wf` — mention `Classification` and
`Pattern.WF`, which are declared in `Experimental/SExpr.lean`.  Everything else they need
(`Pat`, `Pat.simple`, `Pat.uniq`, and the leaf-role machinery) is in
`Theory/Typing/PatternRules.lean`.  A module in `Theory/` importing `Experimental/` would
invert the layering; `Experimental/` already imports `Theory/`, so the combination belongs on
this side.  Neither of the two imports below imports the other.

## Which `Params` this is — the name collision

There are two classes called `Params` and they are **not** the same class:

* `Lean4Lean.Params` — this one.  Eight fields; its `pat_wf` is
  `Pat p r → Pattern.WF classify p`, a purely *syntactic* condition on the pattern's shape.
* `Lean4Lean.VEnv.Params` (`Theory/Typing/ChurchRosser.lean`) — the mainline class.  Its
  `pat_wf` is the semantic one, and *that* is what needs `forallE_inv`.

`Capstone.lean` sits in `namespace Lean4Lean` without `open VEnv`, so its bare `[Params]` is
the first.  That is why instantiating this class is not circular: `ChurchRosser.lean` is not
even in `Capstone.lean`'s import cone, so the mainline `pat_wf` is not nameable there.  See
`Theory/Typing/PatternRules.lean`'s closing section for the three checks that settle it.

## What this file does and does not close

It discharges **all eight fields**, so `paramsOfWF` below is a real instance.  It does *not*
give the shape-model route, because `Capstone.lean` also needs `SExpr.ParamsExtra`, whose
`extra_pat` is **unsatisfiable as stated** — it matches `Pattern.MatchesS` against the
*unpeeled* `df.lhs`, and every rule with parameters is λ-abstracted.  That is `PLAN.md`'s
original `extra_pat` finding: the mainline field was cured by λ-peeling, the copy in
`SExpr.lean` was not.  Fixing it is the shape-model stream's call; nothing here depends on
how.

## A note on the one design decision

`classify` reads each name's arity off its **stored constant**, not off the pattern that
names it.  Reading it off the pattern would require "two registered patterns with the same
constructor leaf agree on its arity", and the `Quot.mk`-versus-a-block-constructor instance of
that is not derivable: `env.constants` cannot see that `addQuot` and `addInduct'` are
different declaration steps.  Reading it off the constant makes the question disappear — two
patterns sharing a leaf share its constant, hence its Π-count, hence agree.  The obligation
becomes a consequence.

## A symptom worth recognising

An earlier draft of `paramsOfWF` was placed after `end Lean4Lean` by accident.  Auto-bound
implicits then turned `VEnv` and `Params` into fresh universe-polymorphic variables and the
file elaborated far enough to report `Invalid field notation … `e` has type `VEnv``, which
reads as a dot-notation problem and is in fact a namespace problem.  **A field-notation error
on a name that obviously has that field means the enclosing namespace is not what you think.**
-/

namespace Lean4Lean

open scoped Classical in
/-- **The classification of a name**, as the three-way cascade `Pattern.WF` asks for: a
recursor leaf is a `.symb`, a constructor leaf a `.ctor`, a δ-rule's head a `.symb 0`.

The arities come from `env.constants`, for the reason in the module docstring.  The cascade
is total and `Classical` supplies its decidability — that is the only place `Classical.choice`
enters this file. -/
noncomputable def VEnv.classify (env : VEnv) (c : Lean.Name) : Option Classification :=
  if ∃ n, Pat.IsRecLeaf env c n then
    some (.symb ((env.constants c).elim 0 (fun ci => ci.type.piArity)))
  else if ∃ n, Pat.IsCtorLeaf env c n then
    some (.ctor ((env.constants c).elim 0 (fun ci => ci.type.piArity)))
  else if Pat.IsDeltaHead env c then some (.symb 0)
  else none

/-- `Pattern.WF` through a `varN` chain: the chain's depth is added to the `extra` counter and
the condition lands on the constant at the bottom. -/
theorem Pattern.WF_varN (cl : Lean.Name → Option Classification) (c : Lean.Name) :
    ∀ (n : Nat) (top : Bool) (k : Nat),
      Pattern.WF cl ((Pattern.const c).varN n) top k
        ↔ cl c = some (if top then .symb (k + n) else .ctor (k + n))
  | 0, top, k => by simp [Pattern.varN, Pattern.WF]
  | n+1, top, k => by
    rw [Pattern.varN, Pattern.WF, Pattern.WF_varN cl c n top (k+1)]
    rw [show k + 1 + n = k + (n+1) from by omega]

/-- Cascade equation 1.  A recursor leaf takes the first branch; its arity is the Π-count of
its stored type, which is one more than the pattern's spine length (the major premise). -/
theorem VEnv.classify_recLeaf {env : VEnv} {R : Lean.Name} {M : Nat}
    (h : Pat.IsRecLeaf env R M) : env.classify R = some (.symb (M + 1)) := by
  obtain ⟨ci, hci, har⟩ := h.piArity
  rw [VEnv.classify, if_pos ⟨_, h⟩, hci, Option.elim, har]

/-- Cascade equation 2.  A constructor leaf is not a recursor leaf (`rec_ne_ctor`, restated as
`Pat.IsRecLeaf.not_ctorLeaf`), so the first branch is skipped. -/
theorem VEnv.classify_ctorLeaf {env : VEnv} {K : Lean.Name} {N : Nat}
    (h : Pat.IsCtorLeaf env K N) : env.classify K = some (.ctor N) := by
  obtain ⟨ci, hci, har⟩ := h.piArity
  rw [VEnv.classify, if_neg (fun ⟨_, hr⟩ => hr.not_ctorLeaf h), if_pos ⟨_, h⟩, hci,
    Option.elim, har]

/-- Cascade equation 3.  A δ-rule's head is neither leaf, so both earlier branches are
skipped.  This is the only one of the three that needs `env.WF`: the two exclusions are
`KeyHeadDelta` facts. -/
theorem VEnv.classify_deltaHead {env : VEnv} (henv : env.WF) {c : Lean.Name}
    (h : Pat.IsDeltaHead env c) : env.classify c = some (.symb 0) := by
  rw [VEnv.classify, if_neg (fun ⟨_, hr⟩ => h.not_recLeaf henv hr),
    if_neg (fun ⟨_, hk⟩ => h.not_ctorLeaf henv hk), if_pos h]

/-- **`Lean4Lean.Params.pat_wf`.**  `Pat.roles` splits a registered pattern into the δ shape
and the ι/quot shape; `Pattern.WF` then unfolds against the three cascade equations. -/
theorem VEnv.classify_pat_wf {env : VEnv} (henv : env.WF) {p : Pattern}
    {r : p.RHS × p.Check} (h : Pat env p r) : Pattern.WF env.classify p := by
  rcases h.roles with ⟨c, rfl, hd⟩ | ⟨R, M, K, N, rfl, hR, hK⟩
  · show env.classify c = _
    rw [env.classify_deltaHead henv hd]; rfl
  · refine ⟨?_, ?_⟩
    · rw [Pattern.WF_varN, env.classify_recLeaf hR]
      simp [Nat.add_comm]
    · rw [Pattern.WF_varN, env.classify_ctorLeaf hK]
      simp

/-- **The shape model's `Params`, for an arbitrary well-formed environment.**

Every field is discharged:

| field | from |
|---|---|
| `env`, `henv`, `univs` | the arguments |
| `Pat` | `Theory/Typing/PatternRules.lean`'s `Pat` |
| `classify` | `VEnv.classify` above |
| `pat_simple` | `Pat.simple` |
| `pat_wf` | `VEnv.classify_pat_wf` above |
| `pat_uniq` | `Pat.uniq` |

`U` is the ambient universe-parameter count; the class does not constrain it, and no field
above mentions it. -/
@[instance_reducible] noncomputable def paramsOfWF {e : VEnv} (henv : e.WF) (U : Nat) :
    Params :=
  Params.mk e henv.ordered U (Pat e) e.classify Pat.simple
    (e.classify_pat_wf henv) (Pat.uniq henv)


/-! ## B1–B4 blocker: `defeqsS` collapses the ι-rule's level clauses

`Pattern.MatchesS` records a **single** `List SLevel` for a whole match — its `app` rule keeps
the function side's list and discards the argument side's — where the `VExpr`-side
`Pattern.Matches` records one list *per leaf* (`m1 : p.LPath → List VLevel`).  `MatchesS`'s
docstring calls that deliberate and prices the cost as `applyS` ignoring an `RHS.fixed`'s
`LPath`.  That is not the only cost.

`Pattern.Check.defeqsS` also drops the two `LPath`s of a `Check.level x i y j` clause and
reads **both** indices out of the one list.  On the `VExpr` side that clause is
`(m1 x).getD i ≈ (m1 y).getD j` — the *recursor* leaf's list against the *constructor* leaf's,
which is what makes `iotaLevelPairs`' `(i+1, i)` true: `selfLvls` is the block's parameters
shifted by one when `isLE` prepends a fresh elimination universe, so both sides are
`ls.getD (i+1)`.  Read out of one list it becomes `ls.getD (i+1) = ls.getD i`, relating the
elimination universe to a block parameter.

`extra_pat` quantifies over *every* `ls` with `ls.length = df.uvars`, and satisfying its `dfs`
obligation at a level clause forces the two sorts equal (`SExpr.sort_inv`).  So for a block
with `isLE = true` and `uvars ≥ 1` — `List`, `Prod`, any large eliminator with a universe
parameter — the obligation below is false.

The lemma is the half that can be checked while `ShapeLogRel.lean` is red: it shows the
obligation really is emitted.  The other half is `SExpr.sort_inv`, which is proved but lives
in `ShapeLogRelAdequacy.lean`, downstream of the red file. -/

theorem Pattern.Check.mem_defeqsS_append {p : Pattern} {m1 m2} {x} :
    ∀ c d : p.Check, x ∈ d.defeqsS m1 m2 → x ∈ (c.append d).defeqsS m1 m2
  | .true, _, h => h
  | .defeq .., d, h => List.mem_cons_of_mem _ (mem_defeqsS_append _ d h)
  | .level .., d, h => List.mem_cons_of_mem _ (mem_defeqsS_append _ d h)

theorem Pattern.Check.mem_defeqsS_ofLevels {p : Pattern} {m1 m2} :
    ∀ (l : List (p.LPath × Nat × p.LPath × Nat)) {t}, t ∈ l →
      (SExpr.sort (m1.getD t.2.1 .zero), SExpr.sort (m1.getD t.2.2.2 .zero))
        ∈ (Check.ofLevels l).defeqsS m1 m2
  | (_, _, _, _) :: l, t, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_defeqsS_ofLevels l h)

/-- **The obligation is emitted.**  For a large-eliminating block, `defeqsS` asks for a defeq
between `sort (ls.getD (k+1))` and `sort (ls.getD k)` — two entries of the *same* `ls`. -/
theorem iota_defeqsS_emits_level {D : VInductDecl'} {T : VIndType} {C : VIndCtor}
    (h : ∀ a ∈ C.args, (VExpr.mkLams (C.params ++ C.fields.map (·.type)) a).Closed)
    (ls : List SLevel) (m2 : (D.iotaPat T C).Path → SExpr) {k : Nat}
    (hk : k < D.uvars) (hLE : D.isLE = true) :
    (SExpr.sort (ls.getD (k+1) .zero), SExpr.sort (ls.getD k .zero))
      ∈ (D.iotaCheckOf T C h).defeqsS ls m2 := by
  refine Pattern.Check.mem_defeqsS_append _ _ (Pattern.Check.mem_defeqsS_append _ _ ?_)
  refine Pattern.Check.mem_defeqsS_ofLevels (m1 := ls) (m2 := m2) _
    (t := (Pattern.LPath.head _, k + 1, iotaLeafCtor _ _ _ _, k)) ?_
  exact List.mem_map.2 ⟨(k + 1, k), List.mem_map.2 ⟨k, List.mem_range.2 hk, by simp [hLE]⟩, rfl⟩
