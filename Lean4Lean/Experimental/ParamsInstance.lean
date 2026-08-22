import Lean4Lean.Theory.Typing.PatternRules
import Lean4Lean.Experimental.SExpr
import Lean4Lean.Experimental.Bridge

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


/-! ## The `defeqsS` level-clause blocker — fixed upstream, recorded here

This file briefly carried a lemma (`iota_defeqsS_emits_level`) witnessing a defect one layer
under the `extra_pat` λ-peel: `Pattern.MatchesS` recorded a **single** `List SLevel` for a whole
match, its `app` rule keeping the function side's list and discarding the argument side's,
and `Pattern.Check.defeqsS` then read *both* indices of a `Check.level x i y j` clause out of
that one list.  On the `VExpr` side the clause is `(m1 x).getD i ≈ (m1 y).getD j` — the
recursor leaf's list against the constructor leaf's — which is what makes `iotaLevelPairs`'
`(i+1, i)` true when `isLE` prepends a fresh elimination universe.  Collapsed to one list it
became `ls.getD (i+1) = ls.getD i`, relating the elimination universe to a block parameter,
and `extra_pat` quantifies over every `ls` — so `ParamsExtra` was still unsatisfiable after the
peel, for `List`, `Prod`, and every large eliminator with a universe parameter.

`MatchesS` now carries `p.LPath → List SLevel` and its `app` rule keeps **both** sides, and
`defeqsS` reads `(m1 x)` and `(m1 y)` from the two leaves.  The witness lemma is deleted rather
than left to rot: it no longer typechecks, and a record that reads as a live constraint is
worse than none — the same failure this stream flagged twice in `SExpr.lean`'s own docstrings.

What the episode is worth keeping for: the deferral note that hid it was *documented and
complete-looking*.  It named one consequence of the single-list design (`applyS` ignoring an
`RHS.fixed`'s `LPath`, "the pre-`LPath` semantics, unchanged") and not the other, and a partial
cost estimate reads exactly like a complete one.  That is a distinct failure from a stale
docstring, and harder to catch: a stale note can be checked against the code, while a complete
-looking partial note gives a reader no signal that anything is missing. -/

/-! ## B1–B4: `SExpr.ParamsExtra.extra_pat`, by transport

The peel was shaped clause-for-clause against `Theory/Typing/PatternRules.lean`'s `Pat.extra`,
so this is a transport rather than a proof.  Two facts make it one:

* **`SExpr.mk` is surjective.**  `SExpr` mirrors `VExpr` with `SLevel` for `VLevel`, and every
  `SLevel` *is* `SLevel.mk` of some `VLevel` — that is its subtype property.  So the arbitrary
  `Γ : List SExpr` and `ls : List SLevel` of `extra_pat` both have `VExpr`/`VLevel` preimages,
  and `Pat.extra` can simply be instantiated at them.  Without this the check clauses would
  need an `SExpr`-side right-weakening (`Γ` is arbitrary while `Pat.extra`'s judgements live in
  `Δ.reverse`), and `Ctx.Lift'` cannot express appending on the right — it grows a context at
  the front, which shifts indices.
* **`extra_pat` asks nothing about level well-formedness**, while `Pat.extra` needs it.  Any
  single `VLevel` mentions finitely many parameters, so a large enough `U` makes a whole list
  well-formed at once, and `Pat.extra`'s `U` is universally quantified. -/

theorem VLevel.wf_mono : ∀ {l : VLevel} {m n : Nat}, m ≤ n → l.WF m → l.WF n
  | .zero, _, _, _, _ => trivial
  | .succ l, _, _, h, hl => VLevel.wf_mono (l := l) h hl
  | .max _ _, _, _, h, hl => ⟨VLevel.wf_mono h hl.1, VLevel.wf_mono h hl.2⟩
  | .imax _ _, _, _, h, hl => ⟨VLevel.wf_mono h hl.1, VLevel.wf_mono h hl.2⟩
  | .param i, _, _, h, hl => Nat.lt_of_lt_of_le hl h

theorem VLevel.exists_wf : ∀ l : VLevel, ∃ n, l.WF n
  | .zero => ⟨0, trivial⟩
  | .succ l => let ⟨n, h⟩ := VLevel.exists_wf l; ⟨n, h⟩
  | .max l₁ l₂ | .imax l₁ l₂ =>
    let ⟨n₁, h₁⟩ := VLevel.exists_wf l₁; let ⟨n₂, h₂⟩ := VLevel.exists_wf l₂
    ⟨Nat.max n₁ n₂, VLevel.wf_mono (Nat.le_max_left ..) h₁,
      VLevel.wf_mono (Nat.le_max_right ..) h₂⟩
  | .param i => ⟨i + 1, Nat.lt_succ_self i⟩

theorem VLevel.exists_wf_list : ∀ ls : List VLevel, ∃ n, ∀ l ∈ ls, l.WF n
  | [] => ⟨0, by simp⟩
  | l :: ls => by
    obtain ⟨n₁, h₁⟩ := VLevel.exists_wf l
    obtain ⟨n₂, h₂⟩ := VLevel.exists_wf_list ls
    refine ⟨Nat.max n₁ n₂, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact VLevel.wf_mono (Nat.le_max_left ..) h₁
    · exact VLevel.wf_mono (Nat.le_max_right ..) (h₂ x hx)

/-- Every `SLevel` is `SLevel.mk` of a `VLevel` — its defining property, as a surjection. -/
theorem SLevel.mk_surj (s : SLevel) : ∃ l : VLevel, SLevel.mk l = s :=
  let ⟨l, h⟩ := s.2; ⟨l, Subtype.ext h⟩

theorem SLevel.mk_surj_list : ∀ ls : List SLevel, ∃ vs : List VLevel, vs.map SLevel.mk = ls
  | [] => ⟨[], rfl⟩
  | s :: ls =>
    let ⟨l, hl⟩ := SLevel.mk_surj s
    let ⟨vs, hvs⟩ := SLevel.mk_surj_list ls
    ⟨l :: vs, by rw [List.map_cons, hl, hvs]⟩

/-- …and hence `SExpr.mk` is surjective: `SExpr` is `VExpr` with `SLevel` in place of
`VLevel`, node for node. -/
theorem SExpr.mk_surj : ∀ e : SExpr, ∃ v : VExpr, SExpr.mk v = e
  | .bvar i => ⟨.bvar i, rfl⟩
  | .sort u => let ⟨l, hl⟩ := SLevel.mk_surj u; ⟨.sort l, by rw [← hl]; rfl⟩
  | .const c ls => let ⟨vs, hvs⟩ := SLevel.mk_surj_list ls; ⟨.const c vs, by rw [← hvs]; rfl⟩
  | .app f a =>
    let ⟨f', hf⟩ := SExpr.mk_surj f; let ⟨a', ha⟩ := SExpr.mk_surj a
    ⟨.app f' a', by rw [← hf, ← ha]; rfl⟩
  | .lam A e =>
    let ⟨A', hA⟩ := SExpr.mk_surj A; let ⟨e', he⟩ := SExpr.mk_surj e
    ⟨.lam A' e', by rw [← hA, ← he]; rfl⟩
  | .forallE A B =>
    let ⟨A', hA⟩ := SExpr.mk_surj A; let ⟨B', hB⟩ := SExpr.mk_surj B
    ⟨.forallE A' B', by rw [← hA, ← hB]; rfl⟩

theorem SExpr.mk_surj_list : ∀ es : List SExpr, ∃ vs : List VExpr, vs.map SExpr.mk = es
  | [] => ⟨[], rfl⟩
  | e :: es =>
    let ⟨v, hv⟩ := SExpr.mk_surj e
    let ⟨vs, hvs⟩ := SExpr.mk_surj_list es
    ⟨v :: vs, by rw [List.map_cons, hv, hvs]⟩

theorem SExpr.mk_mkLams : ∀ {As : List VExpr} {b : VExpr},
    SExpr.mk (VExpr.mkLams As b) = SExpr.mkLams (As.map SExpr.mk) (SExpr.mk b)
  | [], _ => rfl
  | _ :: As, b => by
    rw [VExpr.mkLams, show SExpr.mk (VExpr.lam _ _) = .lam (SExpr.mk _) (SExpr.mk _) from rfl,
      SExpr.mk_mkLams (As := As), List.map_cons, SExpr.mkLams]

/-- The level map of a `VExpr`-side match, pushed to `SExpr`. -/
abbrev Pattern.mkL {p : Pattern} (m1 : p.LPath → List VLevel) : p.LPath → List SLevel :=
  fun x => (m1 x).map SLevel.mk

/-- The argument map of a `VExpr`-side match, pushed to `SExpr`. -/
abbrev Pattern.mkP {p : Pattern} (m2 : p.Path → VExpr) : p.Path → SExpr :=
  fun y => SExpr.mk (m2 y)

/-- **`Matches` transports to `MatchesS`.**  The two are structurally identical — `const`,
`var`, `app` with the same maps — so this is one induction with `SExpr.mk` pushed through.

Stated with the two maps existential and pinned *pointwise*, because the constructors build
them from `Sum.elim`/`Option.elim` and rewriting under a binder to match `mkL`/`mkP` on the
nose is fragile; one `funext` at the use site is cheaper. -/
theorem Pattern.Matches.toS {p : Pattern} {e : VExpr} {m1 m2}
    (H : Pattern.Matches p e m1 m2) :
    ∃ n1 n2, p.MatchesS (SExpr.mk e) n1 n2 ∧
      (∀ x, n1 x = (m1 x).map SLevel.mk) ∧ (∀ y, n2 y = SExpr.mk (m2 y)) := by
  induction H with
  | const => exact ⟨_, _, .const, fun _ => rfl, fun x => x.elim⟩
  | var _ ih =>
    obtain ⟨n1, n2, hm, h1, h2⟩ := ih
    exact ⟨n1, _, .var hm, h1, fun y => by cases y with
      | none => rfl
      | some y => exact h2 y⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨n1, n2, hm, h1, h2⟩ := ih1
    obtain ⟨n1', n2', hm', h1', h2'⟩ := ih2
    exact ⟨_, _, .app hm hm', fun x => by cases x with
      | inl x => exact h1 x
      | inr x => exact h1' x, fun y => by cases y with
      | inl y => exact h2 y
      | inr y => exact h2' y⟩

/-- **`RHS.apply` transports to `applyS`.**  `mk_instL` handles the `fixed` leaf; the rest is
structural. -/
theorem Pattern.RHS.mk_apply [Params] {p : Pattern} {m1 m2} : ∀ r : p.RHS,
    SExpr.mk (r.apply m1 m2) = r.applyS (Pattern.mkL m1) (Pattern.mkP m2)
  | .fixed c lp _ => SExpr.mk_instL
  | .var _ => rfl
  | .app f a => by
    rw [Pattern.RHS.apply, Pattern.RHS.applyS,
      show SExpr.mk (VExpr.app _ _) = .app (SExpr.mk _) (SExpr.mk _) from rfl,
      Pattern.RHS.mk_apply f, Pattern.RHS.mk_apply a]

/-- `SLevel.zero` is `SLevel.mk VLevel.zero`, so `getD` commutes with `mk`. -/
theorem SLevel.getD_map (l : List VLevel) (i : Nat) :
    (l.map SLevel.mk).getD i .zero = SLevel.mk (l.getD i .zero) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

/-- **`Check.OK` transports to the `dfs` list.**  A `defeq` clause becomes its `IsDefEqU`
witness pushed through `VEnv.IsDefEq.toSExpr`; a `level` clause becomes a *reflexive* sort
judgement, because on the `SExpr` side `SLevel` is already quotiented by `≈`, so the two sides
of the clause are literally the same `SLevel` (`SLevel.mk_congr`) and `IsDefEq.sort` applies
with no well-formedness side condition. -/
theorem Pattern.Check.toDfs [Params] {p : Pattern} {m1 m2} {Γ : List VExpr} {U : Nat} :
    ∀ ck : p.Check, ck.OK (Params.env.IsDefEqU U Γ) m1 m2 →
      ∃ dfs : List (SExpr × SExpr × SExpr),
        dfs.map (·.2) = ck.defeqsS (Pattern.mkL m1) (Pattern.mkP m2) ∧
        ∀ a b A, (A, a, b) ∈ dfs → SExpr.IsDefEq (Γ.map SExpr.mk) a b A
  | .true, _ => ⟨[], rfl, by simp⟩
  | .defeq x y rest, h => by
    obtain ⟨dfs, hmap, hall⟩ := Pattern.Check.toDfs rest h.2
    obtain ⟨A, hA⟩ := h.1
    refine ⟨(SExpr.mk A, x.applyS (Pattern.mkL m1) (Pattern.mkP m2),
      y.applyS (Pattern.mkL m1) (Pattern.mkP m2)) :: dfs, by rw [List.map_cons, hmap]; rfl, ?_⟩
    intro a b B hb
    rcases List.mem_cons.1 hb with he | hb
    · cases he
      rw [← Pattern.RHS.mk_apply, ← Pattern.RHS.mk_apply]
      exact VEnv.IsDefEq.toSExpr hA
    · exact hall a b B hb
  | .level x i y j rest, h => by
    obtain ⟨dfs, hmap, hall⟩ := Pattern.Check.toDfs rest h.2
    refine ⟨(SExpr.sort (SLevel.succ (SLevel.mk ((m1 x).getD i .zero))),
      SExpr.sort ((Pattern.mkL m1 x).getD i .zero),
      SExpr.sort ((Pattern.mkL m1 y).getD j .zero)) :: dfs,
      by rw [List.map_cons, hmap]; rfl, ?_⟩
    intro a b B hb
    rcases List.mem_cons.1 hb with he | hb
    · cases he
      rw [SLevel.getD_map, SLevel.getD_map, SLevel.mk_congr h.1]
      exact .sort
    · exact hall a b B hb

/-- **`SExpr.ParamsExtra.extra_pat`, for `paramsOfWF`.**  The field's statement, discharged by
transporting `Theory/Typing/PatternRules.lean`'s `Pat.extra` across `SExpr.mk`.

The two preimages are what make it a transport: `ls` and `Γ` are arbitrary on the `SExpr`
side, and `SExpr.mk` is surjective, so `Pat.extra` is instantiated at their `VExpr` preimages
rather than weakened into place.  `U` is chosen to bound the preimage level list, which is the
only thing `Pat.extra` asks for that the field does not. -/
theorem extra_pat_paramsOfWF {e : VEnv} (henv : e.WF) (univs : Nat)
    (Γ : List SExpr) {df : VDefEq} {ls : List SLevel}
    (hdf : e.defeqs df) (hlen : ls.length = df.uvars) :
    letI : Params := paramsOfWF henv univs
    ∃ Δ L R p r m1 m2 dfs,
      SExpr.instL ls (SExpr.mk df.lhs) = SExpr.mkLams Δ L ∧
      SExpr.instL ls (SExpr.mk df.rhs) = SExpr.mkLams Δ R ∧
      Pat e p r ∧ p.MatchesS L m1 m2 ∧
      (dfs : List (SExpr × SExpr × SExpr)).map (·.2) = r.2.defeqsS m1 m2 ∧
      (∀ a b A, (A, a, b) ∈ dfs → SExpr.IsDefEq (Δ.reverse ++ Γ) a b A) ∧
      R = r.1.applyS m1 m2 := by
  letI inst : Params := paramsOfWF henv univs
  obtain ⟨vs, rfl⟩ := SLevel.mk_surj_list ls
  obtain ⟨ΓV, rfl⟩ := SExpr.mk_surj_list Γ
  obtain ⟨n, hn⟩ := VLevel.exists_wf_list vs
  have hlen' : vs.length = df.uvars := by rwa [List.length_map] at hlen
  obtain ⟨Δ, L, R, p, r, m1, m2, hL, hR, hpat, hm, hck, hRHS⟩ :=
    Pat.extra henv (Γ := ΓV) (U := n) hdf hn hlen'
  obtain ⟨n1, n2, hmS, e1, e2⟩ := hm.toS
  obtain ⟨dfs, hmap, hall⟩ :=
    Pattern.Check.toDfs (Γ := Δ.reverse ++ ΓV) (U := n) r.2 hck
  have he1 : n1 = Pattern.mkL m1 := funext e1
  have he2 : n2 = Pattern.mkP m2 := funext e2
  subst he1; subst he2
  refine ⟨Δ.map SExpr.mk, SExpr.mk L, SExpr.mk R, p, r, _, _, dfs, ?_, ?_, hpat, hmS,
    hmap, ?_, ?_⟩
  · rw [← SExpr.mk_instL, hL, SExpr.mk_mkLams]
  · rw [← SExpr.mk_instL, hR, SExpr.mk_mkLams]
  · intro a b A hmem
    have := hall a b A hmem
    rwa [List.map_append, List.map_reverse] at this
  · rw [hRHS, Pattern.RHS.mk_apply]

end Lean4Lean
