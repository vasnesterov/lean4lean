import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive.Lemmas

/-!
# Each constant name carries at most one δ-rule

`VEnv.Params.pat_uniq` concludes `r ≍ r'` whenever two registered patterns intersect.  For a
δ-rule that forces the rule's *value* to be determined by its head constant — and
`env.defeqs` alone does not give that, because it is a bare predicate with no memory of which
declaration produced a rule.  What does give it is `VEnv.WF`'s declaration history: `addConst`
rejects duplicates, so a second δ-rule for a name already carrying one is impossible.

This is a deliberately *minimal* slice of what a `VEnv.Sig` (design §7.7, ledger I1) would
provide.  It says nothing about inductive blocks and nothing about which declaration a rule
came from; only that a bare-`const`-headed rule is unique to its head.

## Why the invariant is a conjunction

The induction does not go through on uniqueness alone.  In the `.def` step the new rule's
head is `ci.name` and `env.addConst ci.name … = some env'` gives `env.constants ci.name =
none`; to contradict an *existing* rule with that head one needs to know that every rule's
head is already declared.  So the induction runs on

* `DefEqHeadsDeclared` — every bare-`const`-headed rule's head is a declared constant, and
* `DefEqHeadsUnique` — at most one such rule per head,

together.  Neither is provable without the other.

## Why "bare `const`" rather than "all rules"

Only `.def` and `.unsafeDef` contribute rules whose left-hand side is a bare constant.  A
`quot` rule is `fun α r β f c a => …`, a **lam**; an ι-rule is `mkLams Γ' (iotaLhs …)`, a lam
when `Γ'` is non-empty and otherwise an application, since `iotaLhs` always carries at least
the major premise.  Restricting the statement to bare-`const` heads is what keeps those two
cases to a shape computation instead of an argument about their contents.

## Note: `do`-notation blocks `Option.bind_eq_some_iff` — the remedy

`addConsts`, `addConstList`, `addQuot` and `addInduct'` are all written with `do` notation,
and `simp only [Option.bind_eq_some_iff]` does **not** fire on the elaborated term; adding
`Option.bind` to the simp set does not help either.  A turn was lost to this before the
remedy was found, so the pair is recorded together:

* for a `foldlM` (`addConsts`, `addConstList`) — `rw [VEnv.addConsts, List.foldlM_cons]` and
  then `cases hh : env.addConst …`, as in `addConsts_fresh` below;
* for a fixed `bind` chain (`addQuot`, `addInduct'`) — restate it as an explicit `.bind`
  chain inside `rw [show … from rfl, Option.bind_eq_some_iff]`, as in `addQuot_stages` below
  and in `VEnv.addInduct'_stages` (`Theory/Inductive/Lemmas.lean`).

Same remedy, same cause: the surprise is *reduction behaviour*, not mathematics.  It recurs —
`Pattern.inter` in `Theory/Typing/Pattern.lean` is written the same way and its inversion
lemmas (`PatternDecode.lean`) need the second form verbatim.
-/

namespace Lean4Lean
namespace VEnv

/-- `df` is a δ-rule with head `c`: its left-hand side is a bare constant. -/
def IsDeltaRule (df : VDefEq) (c : Lean.Name) : Prop := ∃ ls, df.lhs = .const c ls

theorem IsDeltaRule.const {c ls} : IsDeltaRule ⟨u, .const c ls, v, t⟩ c := ⟨ls, rfl⟩

/-- Every δ-rule's head is a declared constant. -/
def DefEqHeadsDeclared (env : VEnv) : Prop :=
  ∀ df c, env.defeqs df → IsDeltaRule df c → env.contains c

/-- At most one δ-rule per head. -/
def DefEqHeadsUnique (env : VEnv) : Prop :=
  ∀ df df' c, env.defeqs df → env.defeqs df' → IsDeltaRule df c → IsDeltaRule df' c → df = df'

/-! ## How the two primitive operations move the invariants -/

theorem addConst_defeqs {env env' : VEnv} {n ci} (h : env.addConst n ci = some env') :
    env'.defeqs = env.defeqs := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

theorem addConst_contains {env env' : VEnv} {n ci} (h : env.addConst n ci = some env')
    {c} (hc : env.contains c) : env'.contains c := by
  obtain ⟨ci', hci'⟩ := hc
  exact ⟨_, (addConst_le h).constants hci'⟩

@[simp] theorem addDefEq_constants (env : VEnv) (df : VDefEq) :
    (env.addDefEq df).constants = env.constants := rfl

theorem addDefEq_defeqs (env : VEnv) (df x : VDefEq) :
    (env.addDefEq df).defeqs x ↔ x = df ∨ env.defeqs x := Iff.rfl

/-- Adding a constant preserves both invariants: the rules are untouched and the constants
only grow. -/
theorem DefEqHeadsDeclared.addConst {env env' : VEnv} {n ci}
    (h : env.addConst n ci = some env') (H : env.DefEqHeadsDeclared) :
    env'.DefEqHeadsDeclared := by
  intro df c hdf hd
  rw [addConst_defeqs h] at hdf
  exact addConst_contains h (H df c hdf hd)

theorem DefEqHeadsUnique.addConst {env env' : VEnv} {n ci}
    (h : env.addConst n ci = some env') (H : env.DefEqHeadsUnique) :
    env'.DefEqHeadsUnique := by
  intro df df' c hdf hdf' hd hd'
  rw [addConst_defeqs h] at hdf hdf'
  exact H df df' c hdf hdf' hd hd'

/-- Adding a rule whose head is *not* a bare constant leaves both invariants alone.  This is
the `quot` and `induct` case. -/
theorem DefEqHeadsDeclared.addDefEq_notDelta {env : VEnv} {df : VDefEq}
    (H : env.DefEqHeadsDeclared) (hnd : ∀ c, ¬ IsDeltaRule df c) :
    (env.addDefEq df).DefEqHeadsDeclared := by
  rintro x c (rfl | hx) hd
  · exact absurd hd (hnd c)
  · exact H x c hx hd

theorem DefEqHeadsUnique.addDefEq_notDelta {env : VEnv} {df : VDefEq}
    (H : env.DefEqHeadsUnique) (hnd : ∀ c, ¬ IsDeltaRule df c) :
    (env.addDefEq df).DefEqHeadsUnique := by
  rintro x y c (rfl | hx) (rfl | hy) hd hd'
  · rfl
  · exact absurd hd (hnd c)
  · exact absurd hd' (hnd c)
  · exact H x y c hx hy hd hd'

/-! ### Relativising freshness

`.def` and `.unsafeDef` have different shapes.  `.def` does `addConst` and then `addDefEq` on
the *same* name, so at the moment the rule is added its head is fresh.  `.unsafeDef` declares
*all* of a block's constants and only then adds *all* of its rules, so by the time a rule is
added its head has been declared several steps back and freshness is no longer in hand.

A fact that stops holding as you move forward usually wants relativising rather than
re-proving.  The relativisation here is to state what is actually needed — *no existing rule
has this head* — instead of the proxy that happened to be available in the `.def` case, *this
head is undeclared*.  `NoRuleFor` is preserved by adding rules with other heads, which the
proxy is not, so it survives the second traversal; and it follows from the proxy via
`DefEqHeadsDeclared` whenever the proxy does hold.

This works because `addConsts` leaves `defeqs` untouched: declaredness can be taken against
the environment before the block's constants were added, while uniqueness is tracked against
the environment in hand. -/

/-- No rule of `env` is a δ-rule with head `c`. -/
def NoRuleFor (env : VEnv) (c : Lean.Name) : Prop :=
  ∀ df, env.defeqs df → ¬ IsDeltaRule df c

/-- The proxy implies the real condition: an undeclared head can carry no rule. -/
theorem noRuleFor_of_not_contains {env : VEnv} {c} (Hd : env.DefEqHeadsDeclared)
    (h : ¬ env.contains c) : env.NoRuleFor c :=
  fun df hdf hd => h (Hd df c hdf hd)

/-- `NoRuleFor` survives adding a rule with a different head — which the "undeclared"
proxy would not. -/
theorem NoRuleFor.addDefEq {env : VEnv} {c} {df : VDefEq}
    (H : env.NoRuleFor c) (hne : ¬ IsDeltaRule df c) : (env.addDefEq df).NoRuleFor c := by
  rintro x (rfl | hx) hd
  · exact hne hd
  · exact H x hx hd

/-- **The load-bearing step, in its relativised form.**  Adding a δ-rule none of whose heads
already carries a rule preserves uniqueness. -/
theorem DefEqHeadsUnique.addDefEq_noRule {env : VEnv} {df : VDefEq}
    (Hu : env.DefEqHeadsUnique) (hfresh : ∀ c, IsDeltaRule df c → env.NoRuleFor c) :
    (env.addDefEq df).DefEqHeadsUnique := by
  rintro x y c (rfl | hx) (rfl | hy) hd hd'
  · rfl
  · exact absurd hd' (hfresh c hd y hy)
  · exact absurd hd (hfresh c hd' x hx)
  · exact Hu x y c hx hy hd hd'

/-- **The load-bearing step.**  Adding a δ-rule whose head is *fresh* — not yet a declared
constant — preserves uniqueness, precisely because `DefEqHeadsDeclared` rules out an existing
rule with that head.  This is where the two invariants need each other. -/
theorem DefEqHeadsUnique.addDefEq_fresh {env : VEnv} {df : VDefEq}
    (Hd : env.DefEqHeadsDeclared) (Hu : env.DefEqHeadsUnique)
    (hfresh : ∀ c, IsDeltaRule df c → ¬ env.contains c) :
    (env.addDefEq df).DefEqHeadsUnique :=
  Hu.addDefEq_noRule fun c hd => noRuleFor_of_not_contains Hd (hfresh c hd)

/-- …and preserves declaredness, provided the head has just been declared. -/
theorem DefEqHeadsDeclared.addDefEq_declared {env : VEnv} {df : VDefEq}
    (H : env.DefEqHeadsDeclared) (hnew : ∀ c, IsDeltaRule df c → env.contains c) :
    (env.addDefEq df).DefEqHeadsDeclared := by
  rintro x c (rfl | hx) hd
  · exact hnew c hd
  · exact H x c hx hd

/-- `NoRuleFor` transfers along `addConst`, since declaring a constant does not touch the
rules.  This is what the `.def` case needs: by the time the rule is added its head *is*
declared, so the proxy is unavailable there too — but the real condition was established one
step earlier and simply carries over. -/
theorem NoRuleFor.addConst {env env' : VEnv} {n ci c} (h : env.addConst n ci = some env')
    (H : env.NoRuleFor c) : env'.NoRuleFor c := by
  rw [NoRuleFor, addConst_defeqs h]; exact H

theorem NoRuleFor.addConsts {env env' : VEnv} {cis c} :
    env.addConsts cis = some env' → env.NoRuleFor c → env'.NoRuleFor c := by
  induction cis generalizing env with
  | nil => intro h H; cases h; exact H
  | cons ci cis ih =>
    intro h H
    rw [VEnv.addConsts, List.foldlM_cons] at h
    cases hh : env.addConst ci.name ci.toVConstant with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e => rw [hh] at h; exact ih h (H.addConst hh)

/-! ## What `addConsts` succeeding tells you

`addConst` rejects duplicates, so a successful `addConsts` says both that every name was
fresh against the environment *before* the block and that the names are pairwise distinct.
Neither exists in the tree for `List VDefVal`; `Inductive/Lemmas.lean`'s
`addConstList_fresh` is the analogue for `List (Name × VConstant)` and does not transfer. -/

/-- `addConst` succeeding means the name was free.  Stated here because the copy in
`Theory/Inductive/Lemmas.lean` is not in this file's import closure — see note 1b. -/
theorem addConst_constants_eq_none {env env' : VEnv} {name ci}
    (h : env.addConst name ci = some env') : env.constants name = none := by
  unfold VEnv.addConst at h; split at h <;> simp_all

theorem addConsts_fresh : ∀ {cis : List VDefVal} {env env' : VEnv},
    env.addConsts cis = some env' → ∀ ci ∈ cis, ¬ env.contains ci.name
  | [], _, _, _ => by simp
  | ci :: cis, env, env', h => by
    rw [VEnv.addConsts, List.foldlM_cons] at h
    cases hh : env.addConst ci.name ci.toVConstant with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e =>
      rw [hh] at h
      intro ci' hci'
      rcases List.mem_cons.1 hci' with rfl | hci'
      · rintro ⟨x, hx⟩; rw [addConst_constants_eq_none hh] at hx; exact absurd hx (by simp)
      · exact fun hc => addConsts_fresh h ci' hci'
          ⟨_, (addConst_le hh).constants hc.choose_spec⟩

theorem addConsts_nodup : ∀ {cis : List VDefVal} {env env' : VEnv},
    env.addConsts cis = some env' → cis.Pairwise (fun a b => a.name ≠ b.name)
  | [], _, _, _ => .nil
  | ci :: cis, env, env', h => by
    rw [VEnv.addConsts, List.foldlM_cons] at h
    cases hh : env.addConst ci.name ci.toVConstant with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e =>
      rw [hh] at h
      refine .cons (fun b hb hne => ?_) (addConsts_nodup h)
      exact addConsts_fresh h b hb ⟨_, hne ▸ addConst_self hh⟩

/-- Both invariants lift along `addConsts`, since declaring constants leaves the rules alone. -/
theorem DefEqHeadsDeclared.addConsts {env env' : VEnv} {cis} :
    env.addConsts cis = some env' → env.DefEqHeadsDeclared → env'.DefEqHeadsDeclared := by
  induction cis generalizing env with
  | nil => intro h H; cases h; exact H
  | cons ci cis ih =>
    intro h H
    rw [VEnv.addConsts, List.foldlM_cons] at h
    cases hh : env.addConst ci.name ci.toVConstant with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e => rw [hh] at h; exact ih h (H.addConst hh)

theorem DefEqHeadsUnique.addConsts {env env' : VEnv} {cis} :
    env.addConsts cis = some env' → env.DefEqHeadsUnique → env'.DefEqHeadsUnique := by
  induction cis generalizing env with
  | nil => intro h H; cases h; exact H
  | cons ci cis ih =>
    intro h H
    rw [VEnv.addConsts, List.foldlM_cons] at h
    cases hh : env.addConst ci.name ci.toVConstant with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e => rw [hh] at h; exact ih h (H.addConst hh)

/-- Every name of the block carries no rule in the post-`addConsts` environment: freshness
against the *pre*-block environment, transported forward.  This is the hypothesis
`addDefEqs_unique` consumes. -/
theorem addConsts_le : ∀ {cis : List VDefVal} {env env' : VEnv},
    env.addConsts cis = some env' → env ≤ env'
  | [], _, _, h => by cases h; exact VEnv.LE.rfl
  | ci :: cis, env, env', h => by
    rw [VEnv.addConsts, List.foldlM_cons] at h
    cases hh : env.addConst ci.name ci.toVConstant with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e => rw [hh] at h; exact (addConst_le hh).trans (addConsts_le h)

theorem addConsts_contains {env env' : VEnv} {cis} :
    env.addConsts cis = some env' → ∀ ci ∈ cis, env'.contains ci.name := by
  induction cis generalizing env with
  | nil => simp
  | cons ci cis ih =>
    intro h
    rw [VEnv.addConsts, List.foldlM_cons] at h
    cases hh : env.addConst ci.name ci.toVConstant with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e =>
      rw [hh] at h
      intro ci' hci'
      rcases List.mem_cons.1 hci' with rfl | hci'
      · exact ⟨_, (addConsts_le h).constants (addConst_self hh)⟩
      · exact ih h ci' hci'

theorem noRuleFor_addConsts {env env' : VEnv} {cis} (h : env.addConsts cis = some env')
    (Hd : env.DefEqHeadsDeclared) : ∀ ci ∈ cis, env'.NoRuleFor ci.name :=
  fun ci hci => (noRuleFor_of_not_contains Hd (addConsts_fresh h ci hci)).addConsts h

/-! ## The `.unsafeDef` fold

`addConsts` declares the whole block, then `addDefEqs` adds the whole block's rules.  Both are
folds over the same list, and freshness has to survive both — which it does, in the
`NoRuleFor` form, because each step only adds a rule with a *different* head. -/

theorem toDefEq_isDeltaRule {ci : VDefVal} {c : Lean.Name} :
    IsDeltaRule ci.toDefEq c ↔ c = ci.name := by
  constructor
  · rintro ⟨ls, h⟩; exact (VExpr.const.injEq .. ▸ h : _ ∧ _).1.symm
  · rintro rfl; exact ⟨_, rfl⟩

theorem addDefEqs_declared : ∀ {cis : List VDefVal} {env : VEnv},
    env.DefEqHeadsDeclared → (∀ ci ∈ cis, env.contains ci.name) →
    (env.addDefEqs cis).DefEqHeadsDeclared
  | [], _, H, _ => H
  | ci :: cis, env, H, hc => by
    refine addDefEqs_declared (cis := cis)
      (H.addDefEq_declared fun c hd => ?_) (fun ci' hci' => ?_)
    · rw [toDefEq_isDeltaRule.1 hd]; exact hc ci (.head _)
    · exact hc ci' (.tail _ hci')

theorem addDefEqs_unique : ∀ {cis : List VDefVal} {env : VEnv},
    env.DefEqHeadsUnique → (∀ ci ∈ cis, env.NoRuleFor ci.name) →
    cis.Pairwise (fun a b => a.name ≠ b.name) →
    (env.addDefEqs cis).DefEqHeadsUnique
  | [], _, H, _, _ => H
  | ci :: cis, env, H, hno, hp => by
    have hne := (List.pairwise_cons.1 hp).1
    refine addDefEqs_unique (cis := cis)
      (H.addDefEq_noRule fun c hd => ?_) (fun ci' hci' => ?_) (List.pairwise_cons.1 hp).2
    · rw [toDefEq_isDeltaRule.1 hd]; exact hno ci (.head _)
    · exact (hno ci' (.tail _ hci')).addDefEq fun hd =>
        hne ci' hci' (toDefEq_isDeltaRule.1 hd).symm

/-! ## The rule-fold for `quot` and `induct`

Neither contributes a bare-`const`-headed rule, so both reduce to folding
`addDefEq_notDelta`.  `addQuot` adds a single rule and `addIndRules` a `foldl` of them, so the
list version covers both. -/

theorem addDefEqList_notDelta : ∀ (dfs : List VDefEq) {env : VEnv},
    (∀ df ∈ dfs, ∀ c, ¬ IsDeltaRule df c) →
    env.DefEqHeadsDeclared → env.DefEqHeadsUnique →
    (dfs.foldl VEnv.addDefEq env).DefEqHeadsDeclared
      ∧ (dfs.foldl VEnv.addDefEq env).DefEqHeadsUnique
  | [], _, _, Hd, Hu => ⟨Hd, Hu⟩
  | df :: dfs, _env, hnd, Hd, Hu =>
    addDefEqList_notDelta dfs (fun x hx => hnd x (.tail _ hx))
      (Hd.addDefEq_notDelta (hnd df (.head _)))
      (Hu.addDefEq_notDelta (hnd df (.head _)))

/-! ### The two shape computations

A rule is excluded from the δ statement as soon as its left-hand side is *not* a bare
constant.  For `quot` and `induct` that is a computation on the shape, not an argument about
the contents. -/

/-- A `lam` is not a bare constant. -/
theorem not_isDeltaRule_of_lam {u : Nat} {A b v t : VExpr} :
    ∀ c, ¬ IsDeltaRule ⟨u, .lam A b, v, t⟩ c := by rintro c ⟨ls, ⟨⟩⟩

/-- Nor is an application. -/
theorem not_isDeltaRule_of_app {u : Nat} {f a v t : VExpr} :
    ∀ c, ¬ IsDeltaRule ⟨u, .app f a, v, t⟩ c := by rintro c ⟨ls, ⟨⟩⟩

/-- `mkLams` of a non-constant body is never a bare constant: either it binds something, and
is a `lam`, or it is the body itself. -/
theorem not_isDeltaRule_mkLams {u : Nat} {As : List VExpr} {b v t : VExpr}
    (hb : ∀ c ls, b ≠ .const c ls) : ∀ c, ¬ IsDeltaRule ⟨u, VExpr.mkLams As b, v, t⟩ c := by
  cases As with
  | nil => rintro c ⟨ls, h⟩; exact hb c ls h
  | cons A As => rintro c ⟨ls, ⟨⟩⟩

/-! ## `addConstList`: the `induct` stages

`addIndTypes`/`addIndCtors`/`addIndRecs` are all `addConstList`, a fold of `addConst` over
`List (Name × VConstant)`.  Note 1b: this is a *different* list type from `addConsts`, so the
lemmas above do not transfer and these are their own inductions. -/

theorem DefEqHeadsDeclared.addConstList {env env' : VEnv} {cs} :
    env.addConstList cs = some env' → env.DefEqHeadsDeclared → env'.DefEqHeadsDeclared := by
  induction cs generalizing env with
  | nil => intro h H; cases h; exact H
  | cons c cs ih =>
    intro h H
    rw [VEnv.addConstList, List.foldlM_cons] at h
    cases hh : env.addConst c.1 c.2 with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e => rw [hh] at h; exact ih h (H.addConst hh)

theorem DefEqHeadsUnique.addConstList {env env' : VEnv} {cs} :
    env.addConstList cs = some env' → env.DefEqHeadsUnique → env'.DefEqHeadsUnique := by
  induction cs generalizing env with
  | nil => intro h H; cases h; exact H
  | cons c cs ih =>
    intro h H
    rw [VEnv.addConstList, List.foldlM_cons] at h
    cases hh : env.addConst c.1 c.2 with
    | none => rw [hh] at h; exact absurd h (by simp)
    | some e => rw [hh] at h; exact ih h (H.addConst hh)

/-- An ι-rule's left-hand side is never a bare constant: `iotaLhs` is an application (it
always carries at least the major premise), so `mkLams` of it is a `lam` or that
application. -/
theorem not_isDeltaRule_iotaRule (D : VInductDecl') (j q : Nat) (C : VIndCtor) :
    ∀ c, ¬ IsDeltaRule (D.iotaRule j q C) c := by
  refine not_isDeltaRule_mkLams (fun c ls => ?_)
  rw [VInductDecl'.iotaLhs, VExpr.mkApp_concat]
  nofun

/-- `quotDefEq`'s left-hand side is `fun α r β f c a => …`, a `lam`. -/
theorem not_isDeltaRule_quotDefEq : ∀ c, ¬ IsDeltaRule quotDefEq c := by
  rintro c ⟨ls, h⟩; exact absurd h nofun

/-! ## Staging `addQuot`

`addQuot` and `addInduct'` are written with `do` notation, and `simp only
[Option.bind_eq_some_iff]` does *not* fire on the resulting term — the same mismatch that
`addConsts_fresh` above works around by `rw [VEnv.addConsts, List.foldlM_cons]` followed by
`cases hh : env.addConst …`.  What does work is naming the `bind` chain explicitly and
closing the identification by `rfl`, which is how `VEnv.addInduct'_stages`
(`Theory/Inductive/Lemmas.lean`) already handles the `induct` side; this is its `quot`
counterpart. -/

theorem addQuot_stages {env env' : VEnv} (h : env.addQuot = some env') :
    ∃ e1 e2 e3 e4, env.addConst ``Quot quotConst = some e1 ∧
      e1.addConst ``Quot.mk quotMkConst = some e2 ∧
      e2.addConst ``Quot.lift quotLiftConst = some e3 ∧
      e3.addConst ``Quot.ind quotIndConst = some e4 ∧ env' = e4.addDefEq quotDefEq := by
  rw [show env.addQuot
      = (env.addConst ``Quot quotConst).bind (fun e1 =>
        (e1.addConst ``Quot.mk quotMkConst).bind (fun e2 =>
        (e2.addConst ``Quot.lift quotLiftConst).bind (fun e3 =>
        (e3.addConst ``Quot.ind quotIndConst).bind (fun e4 =>
          some (e4.addDefEq quotDefEq))))) from rfl,
    Option.bind_eq_some_iff] at h
  obtain ⟨e1, h1, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨e2, h2, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨e3, h3, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨e4, h4, h5⟩ := h
  exact ⟨e1, e2, e3, e4, h1, h2, h3, h4, (Option.some_inj.1 h5).symm⟩

/-- No ι-rule of a block is a δ-rule: `iotaRules` is a `map` of `iotaRule`. -/
theorem not_isDeltaRule_iotaRules {D : VInductDecl'} :
    ∀ df ∈ D.iotaRules, ∀ c, ¬ IsDeltaRule df c := by
  intro df hdf
  rw [VInductDecl'.iotaRules, List.mem_map] at hdf
  obtain ⟨⟨⟨j, C⟩, q⟩, _, rfl⟩ := hdf
  exact fun c => not_isDeltaRule_iotaRule D j q C c

/-! ## The `WF'` assembly

Seven `cases` arms, each a single application of the lemmas above:

* `axiom`, `opaque` — `addConst` lifting;  `example` — nothing changes;
* `def` — `addConst` lifting, then `addDefEq_declared` and `addDefEq_noRule`, with freshness
  taken on the pre-`addConst` environment and carried by `NoRuleFor.addConst`;
* `unsafeDef` — `addConsts` lifting, then `addDefEqs_declared`/`addDefEqs_unique` fed by
  `addConsts_contains`, `noRuleFor_addConsts` and `addConsts_nodup`;
* `quot` — `addConst` lifting ×4, then `addDefEq_notDelta` with `not_isDeltaRule_quotDefEq`;
* `induct` — `addConstList` lifting ×3, then `addDefEqList_notDelta` with
  `not_isDeltaRule_iotaRule`.
-/

/-- **Both invariants hold in every well-formed environment.**  They are proved together
because neither step is available on its own; see the module docstring. -/
theorem WF'.defEqHeads {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    env.DefEqHeadsDeclared ∧ env.DefEqHeadsUnique := by
  induction H with
  | empty => exact ⟨fun _ _ h _ => h.elim, fun _ _ _ h _ _ _ => h.elim⟩
  | @decl env d env' ds hd _ ih =>
    obtain ⟨Hd, Hu⟩ := ih
    cases hd with
    | «axiom» _ h | «opaque» _ h => exact ⟨Hd.addConst h, Hu.addConst h⟩
    | «example» _ => exact ⟨Hd, Hu⟩
    | «def» _ h =>
      refine ⟨(Hd.addConst h).addDefEq_declared fun c hdr => ?_,
        (Hu.addConst h).addDefEq_noRule fun c hdr => ?_⟩
      · rw [toDefEq_isDeltaRule.1 hdr]; exact ⟨_, addConst_self h⟩
      · rw [toDefEq_isDeltaRule.1 hdr]
        exact NoRuleFor.addConst h (noRuleFor_of_not_contains Hd
          (by rintro ⟨_, hx⟩; rw [addConst_constants_eq_none h] at hx; exact absurd hx nofun))
    | unsafeDef _ h _ =>
      exact ⟨addDefEqs_declared (Hd.addConsts h) (addConsts_contains h),
        addDefEqs_unique (Hu.addConsts h) (noRuleFor_addConsts h Hd) (addConsts_nodup h)⟩
    | quot _ h =>
      obtain ⟨e1, e2, e3, e4, h1, h2, h3, h4, rfl⟩ := addQuot_stages h
      exact ⟨(((Hd.addConst h1).addConst h2).addConst h3).addConst h4
          |>.addDefEq_notDelta not_isDeltaRule_quotDefEq,
        (((Hu.addConst h1).addConst h2).addConst h3).addConst h4
          |>.addDefEq_notDelta not_isDeltaRule_quotDefEq⟩
    | induct _ h =>
      obtain ⟨e1, e2, e3, h1, h2, h3, rfl⟩ := addInduct'_stages h
      exact addDefEqList_notDelta _ not_isDeltaRule_iotaRules
        ((Hd.addConstList h1).addConstList h2 |>.addConstList h3)
        ((Hu.addConstList h1).addConstList h2 |>.addConstList h3)

theorem WF.defEqHeadsDeclared {env : VEnv} (h : env.WF) : env.DefEqHeadsDeclared :=
  (WF'.defEqHeads h.choose_spec).1

theorem WF.defEqHeadsUnique {env : VEnv} (h : env.WF) : env.DefEqHeadsUnique :=
  (WF'.defEqHeads h.choose_spec).2

/-- **The consumer.**  A δ-rule is determined by its head constant: universe count, level
arguments, value and type all agree.  This is what `Params.pat_uniq` needs on the δ side,
where `p₁ = p₂ = p₃ = .const c` forces the datum to be a function of the pattern. -/
theorem WF.delta_uniq {env : VEnv} (H : env.WF) {c ls ls'} {u u' : Nat} {v v' t t' : VExpr}
    (h : env.defeqs ⟨u, .const c ls, v, t⟩) (h' : env.defeqs ⟨u', .const c ls', v', t'⟩) :
    u = u' ∧ ls = ls' ∧ v = v' ∧ t = t' := by
  have := H.defEqHeadsUnique _ _ c h h' ⟨ls, rfl⟩ ⟨ls', rfl⟩
  injection this with e1 e2 e3 e4
  injection e2 with _ e2
  exact ⟨e1, e2, e3, e4⟩


end VEnv
end Lean4Lean
