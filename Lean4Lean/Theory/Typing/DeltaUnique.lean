import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Typing.PatternDecode
import Lean4Lean.Theory.Typing.EnvLemmas

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

/-! # Part II: the key-based provenance invariants

`DefEqHeadsDeclared`/`DefEqHeadsUnique` above are the bare-`const` case of a general fact,
and `Params.pat_uniq` needs the general one.  Give every rule a **key** (`VDefEq.key`): the
constant heading its λ-peeled left-hand side, then the constant heading that spine's last
argument.  Then the three invariants below are exactly the previous two, generalised from
δ-rules to all rules, plus the one that indexes ι-rules.

Together they replace what design §7.7 / ledger I1 calls a `VEnv.Sig`, for every use
`Params` makes of it.  What a `Sig` adds beyond them — a `kind : Name → Option ObjKind`,
`KindMatches`, `sound`, `coherent` — all answers "what kind of object is this name?"; these
never ask that, only "which rule owns this name?".  In particular **G4 (a name belongs to at
most one block) is not needed**: `KeyMajorUnique` recovers the *rule*, and an ι-rule's own
syntax already contains every component of the ι-datum. -/

end VEnv

/-- **The rule's key**: the constant heading its λ-peeled left-hand side, followed by the
constant heading that spine's *last* argument — the major premise, for an ι-rule.  A δ-rule
contributes just its head, `quotDefEq` contributes `[Quot.lift, Quot.mk]`, and an ι-rule
contributes `[I_j.rec, C.name]`.

Two design points, both load-bearing:

* **Names only, no arity.**  `VInductDecl'.iotaPat` reports the recursor arity as
  `np + nm + nmin + T.indices.length` while the rule's spine actually carries `|C.args|`
  index arguments; the equation between them is a `VInductDecl'.WF` fact that `Pat.iota` does
  not carry.  Keying on names alone sidesteps that entirely.
* **Head *and* last, not just the head.**  A δ-rule must be excluded from another rule's
  *recursor* leaf (the head) and from its *constructor* leaf (the last); and the ι-rules of a
  multi-constructor block share their head, so only the last can index them. -/
def VDefEq.key (df : VDefEq) : List Name :=
  let b := (VExpr.peelLams df.lhs).2
  (VExpr.headName b).toList ++ (((VExpr.spine b).2.getLast?).bind VExpr.headName).toList

namespace VEnv

/-- A δ-rule's key is its head, alone: the left-hand side is a bare constant, so there is no
spine and no major premise. -/
theorem key_of_isDeltaRule {df : VDefEq} {c} (h : IsDeltaRule df c) : df.key = [c] := by
  obtain ⟨ls, hl⟩ := h
  show ((VExpr.peelLams df.lhs).2 |> fun b =>
    (VExpr.headName b).toList ++ ((VExpr.spine b).2.getLast?.bind VExpr.headName).toList) = _
  rw [hl]; rfl

/-- The quotient rule's key.  Computed, not assumed. -/
theorem key_quotDefEq : quotDefEq.key = [``Quot.lift, ``Quot.mk] := rfl

/-- Every key name of every rule is a declared constant.  Generalises `DefEqHeadsDeclared`. -/
def KeysDeclared (env : VEnv) : Prop := ∀ df, env.defeqs df → ∀ n ∈ df.key, env.contains n

/-- A δ-rule's head occurs in no other rule's key.  Generalises `DefEqHeadsUnique`, and is
what excludes a δ-rule for a recursor or constructor name. -/
def KeyHeadDelta (env : VEnv) : Prop :=
  ∀ df df' c, env.defeqs df → env.defeqs df' → IsDeltaRule df c → c ∈ df'.key → df = df'

/-- **A rule is determined by the head of its major premise.**  Stated with an explicit `n`
rather than as `df.key.getLast? = df'.key.getLast?` so that the `none` case — a rule whose
left-hand side is not a constant spine, which no declaration produces — never has to be
excluded by a fourth invariant. -/
def KeyMajorUnique (env : VEnv) : Prop :=
  ∀ df df' n, env.defeqs df → env.defeqs df' →
    df.key.getLast? = some n → df'.key.getLast? = some n → df = df'

/-! ## Moving the three invariants

All three mention only `defeqs` and `contains`, so a step that leaves the rules alone lifts
all three at once — one `keys_mono` in place of six lemmas. -/

theorem keys_mono {env env' : VEnv} (hd : env'.defeqs = env.defeqs) (hle : env ≤ env')
    (H : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyMajorUnique) :
    env'.KeysDeclared ∧ env'.KeyHeadDelta ∧ env'.KeyMajorUnique := by
  obtain ⟨H1, H2, H3⟩ := H
  refine ⟨fun df hdf n hn => ?_, fun df df' c hdf hdf' => ?_, fun df df' n hdf hdf' => ?_⟩
  · obtain ⟨ci, hci⟩ := H1 df (hd ▸ hdf) n hn; exact ⟨ci, hle.constants hci⟩
  · exact H2 df df' c (hd ▸ hdf) (hd ▸ hdf')
  · exact H3 df df' n (hd ▸ hdf) (hd ▸ hdf')

/-- **The step for a δ-rule.**  Its key is a singleton, so demanding that no existing rule's
key mentions it settles all three at once. -/
theorem keys_addDefEq {env : VEnv} {df : VDefEq}
    (H1 : env.KeysDeclared) (H2 : env.KeyHeadDelta) (H3 : env.KeyMajorUnique)
    (hdecl : ∀ n ∈ df.key, env.contains n)
    (hnew : ∀ df', env.defeqs df' → ∀ n ∈ df.key, n ∉ df'.key) :
    (env.addDefEq df).KeysDeclared ∧ (env.addDefEq df).KeyHeadDelta ∧
      (env.addDefEq df).KeyMajorUnique := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x (rfl | hx) n hn
    · exact hdecl n hn
    · exact H1 x hx n hn
  · rintro x y c (rfl | hx) (rfl | hy) hd hc
    · rfl
    · exact absurd hc (hnew y hy c (key_of_isDeltaRule hd ▸ List.mem_singleton_self c))
    · exact absurd (key_of_isDeltaRule hd ▸ List.mem_singleton_self c)
        (fun h => hnew x hx c hc h)
    · exact H2 x y c hx hy hd hc
  · rintro x y n (rfl | hx) (rfl | hy) hn hn'
    · rfl
    · exact absurd (List.mem_of_getLast? hn') (hnew y hy n (List.mem_of_getLast? hn))
    · exact absurd (List.mem_of_getLast? hn) (hnew x hx n (List.mem_of_getLast? hn'))
    · exact H3 x y n hx hy hn hn'

/-- **The step for a non-δ rule.**  Its key may share its *head* with rules already present —
the two ι-rules of a two-constructor block share their recursor — so only the last name has
to be new.  Getting this right is the whole reason the key has two positions. -/
theorem keys_addDefEq_notDelta {env : VEnv} {df : VDefEq}
    (H : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyMajorUnique)
    (hnd : ∀ c, ¬ IsDeltaRule df c)
    (hdecl : ∀ n ∈ df.key, env.contains n)
    (hδ : ∀ df' c, env.defeqs df' → IsDeltaRule df' c → c ∉ df.key)
    (hmaj : ∀ df' n, env.defeqs df' → df.key.getLast? = some n →
      df'.key.getLast? = some n → False) :
    (env.addDefEq df).KeysDeclared ∧ (env.addDefEq df).KeyHeadDelta ∧
      (env.addDefEq df).KeyMajorUnique := by
  obtain ⟨H1, H2, H3⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · rintro x (rfl | hx) n hn
    · exact hdecl n hn
    · exact H1 x hx n hn
  · rintro x y c (rfl | hx) (rfl | hy) hd hc
    · rfl
    · exact absurd hd (hnd c)
    · exact absurd hc (hδ x c hx hd)
    · exact H2 x y c hx hy hd hc
  · rintro x y n (rfl | hx) (rfl | hy) hn hn'
    · rfl
    · exact absurd hn' (fun h => hmaj y n hy hn h)
    · exact absurd hn (fun h => hmaj x n hx hn' h)
    · exact H3 x y n hx hy hn hn'

/-- The δ-fold: `.unsafeDef`'s block of rules, all δ-rules with pairwise distinct heads. -/
theorem keys_addDefEqs : ∀ {cis : List VDefVal} {env : VEnv},
    (env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyMajorUnique) →
    (∀ ci ∈ cis, env.contains ci.name) →
    (∀ ci ∈ cis, ∀ df', env.defeqs df' → ci.name ∉ df'.key) →
    cis.Pairwise (fun a b => a.name ≠ b.name) →
    (env.addDefEqs cis).KeysDeclared ∧ (env.addDefEqs cis).KeyHeadDelta ∧
      (env.addDefEqs cis).KeyMajorUnique
  | [], _, H, _, _, _ => H
  | ci :: cis, env, H, hc, hn, hp => by
    have hkey : ci.toDefEq.key = [ci.name] := rfl
    have hne := (List.pairwise_cons.1 hp).1
    have step := keys_addDefEq H.1 H.2.1 H.2.2
      (by rw [hkey]; intro n hn2; cases List.mem_singleton.1 hn2; exact hc ci (.head _))
      (by
        intro df' hdf' n hn2
        rw [hkey] at hn2; cases List.mem_singleton.1 hn2
        exact hn ci (.head _) df' hdf')
    refine keys_addDefEqs (cis := cis) step (fun ci' hci' => hc ci' (.tail _ hci')) ?_
      (List.pairwise_cons.1 hp).2
    intro ci' hci' df' hdf'
    have hor : df' = ci.toDefEq ∨ env.defeqs df' := hdf'
    rcases hor with rfl | hdf'
    · rw [hkey]; intro h; exact hne ci' hci' (List.mem_singleton.1 h).symm
    · exact hn ci' (.tail _ hci') df' hdf'

/-- The non-δ fold: `quot`'s single rule and `induct`'s block of ι-rules. -/
theorem keys_addDefEqList_notDelta : ∀ (dfs : List VDefEq) {env : VEnv},
    (env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyMajorUnique) →
    (∀ df ∈ dfs, ∀ c, ¬ IsDeltaRule df c) →
    (∀ df ∈ dfs, ∀ n ∈ df.key, env.contains n) →
    (∀ df ∈ dfs, ∀ df' c, env.defeqs df' → IsDeltaRule df' c → c ∉ df.key) →
    (∀ df ∈ dfs, ∀ df' n, env.defeqs df' → df.key.getLast? = some n →
      df'.key.getLast? = some n → False) →
    dfs.Pairwise (fun a b => ∀ n, a.key.getLast? = some n → b.key.getLast? ≠ some n) →
    (dfs.foldl VEnv.addDefEq env).KeysDeclared ∧
      (dfs.foldl VEnv.addDefEq env).KeyHeadDelta ∧
      (dfs.foldl VEnv.addDefEq env).KeyMajorUnique
  | [], _, H, _, _, _, _, _ => H
  | df :: dfs, env, H, hnd, hdecl, hδ, hmaj, hp => by
    have hpc := List.pairwise_cons.1 hp
    have step := keys_addDefEq_notDelta H (hnd df (.head _)) (hdecl df (.head _))
      (hδ df (.head _)) (hmaj df (.head _))
    refine keys_addDefEqList_notDelta dfs step
      (fun x hx => hnd x (.tail _ hx)) (fun x hx => hdecl x (.tail _ hx)) ?_ ?_ hpc.2
    · intro x hx df' c hdf'
      have hor : df' = df ∨ env.defeqs df' := hdf'
      rcases hor with rfl | hdf'
      · exact fun hd => absurd hd (hnd df' (.head _) c)
      · exact hδ x (.tail _ hx) df' c hdf'
    · intro x hx df' n hdf' hn hn'
      have hor : df' = df ∨ env.defeqs df' := hdf'
      rcases hor with rfl | hdf'
      · exact hpc.1 x hx n hn' hn
      · exact hmaj x (.tail _ hx) df' n hdf' hn hn'

end VEnv

/-! ## The keys of the three rule shapes -/

theorem VInductDecl'.headName_ctorApp' (D : VInductDecl') (C : VIndCtor) (k : Nat)
    (args : List VExpr) : VExpr.headName (D.ctorApp' C k args) = some C.name := by
  rw [VInductDecl'.ctorApp', VExpr.headName_mkApp]

/-- An ι-rule's key: the recursor of its own type, then its constructor.  `iotaLhs` is
`I_j.rec … (c params b)`, so the head is the recursor and the last argument is the major
premise, whose own head is the constructor. -/
theorem VInductDecl'.key_iotaRule (D : VInductDecl') (j q : Nat) (C : VIndCtor) :
    (D.iotaRule j q C).key
      = [Lean.mkRecName (D.types.getD j default).name, C.name] := by
  show ((VExpr.peelLams (VExpr.mkLams (D.iotaCtx C) (D.iotaLhs j C))).2 |> fun b =>
    (VExpr.headName b).toList ++ ((VExpr.spine b).2.getLast?.bind VExpr.headName).toList) = _
  rw [VExpr.peelLams_mkLams]
  rw [show (VExpr.peelLams (D.iotaLhs j C)).2 = D.iotaLhs j C from by
    rw [VInductDecl'.iotaLhs, VExpr.mkApp_concat]; rfl]
  simp only [VInductDecl'.iotaLhs, VExpr.headName_mkApp,
    VExpr.spine_mkApp (e := VExpr.const (Lean.mkRecName (D.types.getD j default).name)
      (VLevel.params D.recUvars)) (by nofun)]
  simp [List.getLast?_append, VInductDecl'.headName_ctorApp']

theorem VInductDecl'.mem_key_iotaRules {D : VInductDecl'} {df : VDefEq} (h : df ∈ D.iotaRules) :
    ∃ j C, (j, C) ∈ D.ctorsAll ∧
      df.key = [Lean.mkRecName (D.types.getD j default).name, C.name] := by
  rw [VInductDecl'.iotaRules, List.mem_map] at h
  obtain ⟨⟨⟨j, C⟩, q⟩, hm, rfl⟩ := h
  exact ⟨j, C, List.zipIdx_map_fst 0 D.ctorsAll ▸ List.mem_map_of_mem hm,
    D.key_iotaRule j q C⟩

/-- The block's ι-rules have pairwise distinct major-premise heads, because
`addConstList D.ctorConsts` succeeding makes the constructor names pairwise distinct. -/
theorem VInductDecl'.iotaRules_pairwise_major (D : VInductDecl')
    (hnd : (D.ctorConsts.map (·.1)).Nodup) :
    D.iotaRules.Pairwise
      (fun a b => ∀ n, a.key.getLast? = some n → b.key.getLast? ≠ some n) := by
  have h1 : D.ctorsAll.Pairwise (fun a b => a.2.name ≠ b.2.name) := by
    rw [VInductDecl'.ctorConsts, List.map_map] at hnd
    exact List.pairwise_map.1 hnd
  have h2 : D.ctorsAll.zipIdx.Pairwise (fun a b => a.1.2.name ≠ b.1.2.name) := by
    rw [← List.zipIdx_map_fst 0 D.ctorsAll] at h1
    exact (List.pairwise_map (f := Prod.fst)).1 h1
  rw [VInductDecl'.iotaRules]
  refine List.pairwise_map.2 (h2.imp ?_)
  rintro ⟨⟨j, C⟩, q⟩ ⟨⟨j', C'⟩, q'⟩ h n hn hn'
  rw [VInductDecl'.key_iotaRule] at hn
  rw [VInductDecl'.key_iotaRule] at hn'
  simp at hn hn'
  exact h (hn ▸ hn' ▸ rfl)

namespace VEnv


/-! ## Which rules a step adds

`extra_pat` must produce a `Pat` from `env.defeqs df` alone, so it needs to know that `df` is
one of the three shapes a declaration can contribute.  These three lemmas invert the two
rule-folds and the single `addDefEq`; `RuleShape` (`Theory/Typing/PatternRules.lean`) is what
they feed. -/

theorem addDefEqList_mem : ∀ (dfs : List VDefEq) {env : VEnv} {df},
    (dfs.foldl VEnv.addDefEq env).defeqs df → df ∈ dfs ∨ env.defeqs df
  | [], _, _, h => .inr h
  | df' :: dfs, env, df, h => by
    rcases addDefEqList_mem dfs h with h | h
    · exact .inl (.tail _ h)
    · rcases (h : df = df' ∨ env.defeqs df) with rfl | h
      · exact .inl (.head _)
      · exact .inr h

end VEnv

/-- Each ι-rule of a block, with the `ctorsAll` index its minor premise sits at — which is
what `iotaLam_hasType` needs. -/
theorem VInductDecl'.mem_iotaRules {D : VInductDecl'} {df : VDefEq} (h : df ∈ D.iotaRules) :
    ∃ j q C, D.ctorsAll[q]? = some (j, C) ∧ df = D.iotaRule j q C := by
  rw [VInductDecl'.iotaRules, List.mem_map] at h
  obtain ⟨⟨⟨j, C⟩, q⟩, hm, rfl⟩ := h
  exact ⟨j, q, C, List.mk_mem_zipIdx_iff_getElem?.1 hm, rfl⟩

namespace VEnv

/-! ## The `WF'` induction for the key invariants

Same seven arms as `WF'.defEqHeads`, and the same evidence in each: `addConst` rejects
duplicates, so every name a step introduces was undeclared beforehand, while `KeysDeclared`
says every name an *existing* rule's key mentions is declared.  Those two facts are what
separate the new rules' keys from the old ones' in every arm.

The four substantial arms are separate lemmas rather than `cases` branches, so that
unification fixes each step's data instead of the proof depending on the order in which
`VDecl.WF`'s auto-bound implicits happen to be generalised. -/

theorem keys_def {env env' : VEnv} {ci : VDefVal}
    (h : env.addConst ci.name ci.toVConstant = some env')
    (ih : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyMajorUnique) :
    (env'.addDefEq ci.toDefEq).KeysDeclared ∧ (env'.addDefEq ci.toDefEq).KeyHeadDelta ∧
      (env'.addDefEq ci.toDefEq).KeyMajorUnique := by
  have hfresh : ¬ env.contains ci.name := by
    rintro ⟨x, hx⟩; rw [addConst_constants_eq_none h] at hx; exact absurd hx nofun
  have H₁ := keys_mono (addConst_defeqs h) (addConst_le h) ih
  refine keys_addDefEq H₁.1 H₁.2.1 H₁.2.2 ?_ ?_
  · intro n hn
    cases List.mem_singleton.1 (show n ∈ [ci.name] from hn)
    exact ⟨_, addConst_self h⟩
  · intro df' hdf' n hn hmem
    cases List.mem_singleton.1 (show n ∈ [ci.name] from hn)
    rw [addConst_defeqs h] at hdf'
    exact hfresh (ih.1 df' hdf' _ hmem)

theorem keys_unsafeDef {env env' : VEnv} {cis : List VDefVal} (h : env.addConsts cis = some env')
    (ih : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyMajorUnique) :
    (env'.addDefEqs cis).KeysDeclared ∧ (env'.addDefEqs cis).KeyHeadDelta ∧
      (env'.addDefEqs cis).KeyMajorUnique := by
  refine keys_addDefEqs (keys_mono (addConsts_defeqs h) (addConsts_le h) ih)
    (addConsts_contains h) ?_ (addConsts_nodup h)
  intro ci hci df' hdf' hmem
  rw [addConsts_defeqs h] at hdf'
  exact addConsts_fresh h ci hci (ih.1 df' hdf' _ hmem)

theorem keys_quot {env env' : VEnv} (h : env.addQuot = some env')
    (ih : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyMajorUnique) :
    env'.KeysDeclared ∧ env'.KeyHeadDelta ∧ env'.KeyMajorUnique := by
  obtain ⟨e1, e2, e3, e4, h1, h2, h3, h4, rfl⟩ := addQuot_stages h
  have hdefeqs : e4.defeqs = env.defeqs := by
    rw [addConst_defeqs h4, addConst_defeqs h3, addConst_defeqs h2, addConst_defeqs h1]
  have hmk : ¬ env.contains ``Quot.mk := by
    rintro ⟨x, hx⟩
    have := (addConst_le h1).constants hx
    rw [addConst_constants_eq_none h2] at this; exact absurd this nofun
  have hlift : ¬ env.contains ``Quot.lift := by
    rintro ⟨x, hx⟩
    have := (addConst_le h2).constants ((addConst_le h1).constants hx)
    rw [addConst_constants_eq_none h3] at this; exact absurd this nofun
  have hkey : quotDefEq.key = [``Quot.lift, ``Quot.mk] := rfl
  have H₄ := keys_mono (addConst_defeqs h4) (addConst_le h4)
    (keys_mono (addConst_defeqs h3) (addConst_le h3)
      (keys_mono (addConst_defeqs h2) (addConst_le h2)
        (keys_mono (addConst_defeqs h1) (addConst_le h1) ih)))
  refine keys_addDefEqList_notDelta [quotDefEq] H₄ ?_ ?_ ?_ ?_ (by simp)
  · intro df hdf; cases List.mem_singleton.1 hdf; exact not_isDeltaRule_quotDefEq
  · intro df hdf n hn
    cases List.mem_singleton.1 hdf
    rw [hkey] at hn
    rcases List.mem_cons.1 hn with rfl | hn
    · exact ⟨_, (addConst_le h4).constants (addConst_self h3)⟩
    · cases List.mem_singleton.1 hn
      exact ⟨_, (addConst_le h4).constants ((addConst_le h3).constants (addConst_self h2))⟩
  · intro df hdf df' c hdf' hδ hmem
    cases List.mem_singleton.1 hdf
    rw [hdefeqs] at hdf'
    have hc := ih.1 df' hdf' c (key_of_isDeltaRule hδ ▸ List.mem_singleton_self c)
    rw [hkey] at hmem
    rcases List.mem_cons.1 hmem with rfl | hmem
    · exact hlift hc
    · cases List.mem_singleton.1 hmem; exact hmk hc
  · intro df hdf df' n hdf' hn hn'
    cases List.mem_singleton.1 hdf
    rw [hdefeqs] at hdf'
    rw [hkey] at hn
    cases (show some ``Quot.mk = some n from hn)
    exact hmk (ih.1 df' hdf' _ (List.mem_of_getLast? hn'))

theorem keys_induct {env env' : VEnv} {D : VInductDecl'} (h : env.addInduct' D = some env')
    (ih : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyMajorUnique) :
    env'.KeysDeclared ∧ env'.KeyHeadDelta ∧ env'.KeyMajorUnique := by
  obtain ⟨e1, e2, e3, h1, h2, h3, rfl⟩ := addInduct'_stages h
  have hdefeqs : e3.defeqs = env.defeqs := by
    rw [addConstList_defeqs h3, addConstList_defeqs h2, addConstList_defeqs h1]
  have hctorfresh : ∀ n ∈ D.ctorConsts.map (·.1), ¬ env.contains n := by
    rintro n hn ⟨x, hx⟩
    have := (addConstList_le h1).constants hx
    rw [(addConstList_fresh h2).1 n hn] at this; exact absurd this nofun
  have hrecfresh : ∀ n ∈ D.recConsts.map (·.1), ¬ env.contains n := by
    rintro n hn ⟨x, hx⟩
    have := (addConstList_le h2).constants ((addConstList_le h1).constants hx)
    rw [(addConstList_fresh h3).1 n hn] at this; exact absurd this nofun
  have hkey : ∀ df ∈ D.iotaRules, ∀ n ∈ df.key,
      n ∈ D.ctorConsts.map (·.1) ∨ n ∈ D.recConsts.map (·.1) := by
    intro df hdf n hn
    obtain ⟨j, C, hjC, hk⟩ := VInductDecl'.mem_key_iotaRules hdf
    obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hjC
    rw [hk] at hn
    rcases List.mem_cons.1 hn with rfl | hn
    · refine .inr (List.mem_map.2 ⟨_, List.mem_map.2 ⟨(T, j), ?_, rfl⟩, ?_⟩)
      · exact List.mk_mem_zipIdx_iff_getElem?.2 hT
      · rw [D.getD_types hT]
    · cases List.mem_singleton.1 hn
      exact .inl (List.mem_map.2 ⟨_, List.mem_map.2 ⟨(j, C), hjC, rfl⟩, rfl⟩)
  have hfresh : ∀ df ∈ D.iotaRules, ∀ n ∈ df.key, ¬ env.contains n := by
    intro df hdf n hn
    rcases hkey df hdf n hn with hm | hm
    · exact hctorfresh n hm
    · exact hrecfresh n hm
  have H₃ := keys_mono (addConstList_defeqs h3) (addConstList_le h3)
    (keys_mono (addConstList_defeqs h2) (addConstList_le h2)
      (keys_mono (addConstList_defeqs h1) (addConstList_le h1) ih))
  refine keys_addDefEqList_notDelta D.iotaRules H₃ not_isDeltaRule_iotaRules ?_ ?_ ?_
    (D.iotaRules_pairwise_major (addConstList_fresh h2).2)
  · intro df hdf n hn
    rcases hkey df hdf n hn with hm | hm
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
      exact ⟨_, (addConstList_le h3).constants (addConstList_constants h2 c hc)⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
      exact ⟨_, addConstList_constants h3 c hc⟩
  · intro df hdf df' c hdf' hδ hmem
    rw [hdefeqs] at hdf'
    exact hfresh df hdf c hmem
      (ih.1 df' hdf' c (key_of_isDeltaRule hδ ▸ List.mem_singleton_self c))
  · intro df hdf df' n hdf' hn hn'
    rw [hdefeqs] at hdf'
    exact hfresh df hdf n (List.mem_of_getLast? hn)
      (ih.1 df' hdf' n (List.mem_of_getLast? hn'))

theorem WF'.keys {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyMajorUnique := by
  induction H with
  | empty => exact ⟨fun _ h => h.elim, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
  | @decl env d env' ds hd _ ih =>
    cases hd with
    | «axiom» _ h | «opaque» _ h => exact keys_mono (addConst_defeqs h) (addConst_le h) ih
    | «example» _ => exact ih
    | «def» _ h => exact keys_def h ih
    | unsafeDef _ h _ => exact keys_unsafeDef h ih
    | quot _ h => exact keys_quot h ih
    | induct _ h => exact keys_induct h ih

theorem WF.keysDeclared {env : VEnv} (h : env.WF) : env.KeysDeclared :=
  (WF'.keys h.choose_spec).1

theorem WF.keyHeadDelta {env : VEnv} (h : env.WF) : env.KeyHeadDelta :=
  (WF'.keys h.choose_spec).2.1

theorem WF.keyMajorUnique {env : VEnv} (h : env.WF) : env.KeyMajorUnique :=
  (WF'.keys h.choose_spec).2.2

end VEnv

/-! # Part III: an inductive type's name is not a rule key

`Params`' `classify` must report `.indTy` for a block type's name, and its cascade tests the
recursor-leaf, constructor-leaf and δ-head roles first.  So it needs: **`T.name` plays none of
those roles.**

The first formulation of that asked *"what kind of object is this name?"* — three separate
negations, which is the `kind`/`KindMatches` content Part II's header says these invariants
deliberately do not provide, and which would have needed a `VEnv.Sig`.  It reformulates,
because `VDefEq.key` already names exactly the three things to exclude: a recursor leaf **is**
a key's head, a constructor leaf **is** its last, a δ-head **is** the whole key
(`key_of_isDeltaRule`), and `Quot.lift`/`Quot.mk` **are** `quotDefEq.key` (`key_quotDefEq`).
All four collapse into `T.name ∉ df.key`, which is a *"which rule owns this name?"* question —
"no rule owns `T.name`" — and lands inside the frame after all.

**Why the syntactic route is unavailable, and this one is needed.**  Every other
name-disjointness fact here (`rec_ne_ctor`, `quotLift_ne_ctor`) works by distinguishing
*stored types*: a recursor's `piBodyHead` is a `.bvar`, a constructor's a `.const`.  For a
block type name that route is closed by **F1**: `VIndType.WF` gives only
`canon : IsDefEqType [] T.type (mkPi (params ++ indices) (.sort lvl))`, so `T.type` is
*definitionally* a Π-telescope ending in a sort and **syntactically anything at all** — it
could be a `recType`.  Separating them semantically is Π/sort inversion, which is downstream
of the very `Params` instance this feeds.  Provenance is the only remaining route.

**A separate induction, deliberately.**  These two clauses could have been threaded through
Part II's triple, turning it into a quintuple in nine lemmas.  They are carried by their own
`WF'` induction instead, which *consumes* `WF'.keys` as a black box at the one arm that needs
it.  That costs one extra traversal and touches no existing proof. -/

namespace VEnv

/-- Every registered ι-rule's block type name is a declared constant.  The analogue of
`KeysDeclared`, and it exists for the same reason: it is what turns a freshness fact about a
newly declared name into a disequation. -/
def IotaTypeDeclared (env : VEnv) : Prop :=
  ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor),
    env.defeqs (D.iotaRule j q C) → env.contains (D.types.getD j default).name

/-- **No rule owns a block type's name.**  With `key_of_isDeltaRule`, `key_quotDefEq` and
`key_iotaRule`, this single clause says `T.name` is not a δ-rule's head, not `Quot.lift` or
`Quot.mk`, and not any registered ι-rule's recursor or constructor leaf. -/
def IotaTypeNotKey (env : VEnv) : Prop :=
  ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor),
    env.defeqs (D.iotaRule j q C) →
    ∀ df, env.defeqs df → (D.types.getD j default).name ∉ df.key

/-- Both clauses mention only `defeqs` and `contains`, so a step that leaves the rules alone
lifts both at once. -/
theorem iotaTypes_mono {env env' : VEnv} (hd : env'.defeqs = env.defeqs) (hle : env ≤ env')
    (H : env.IotaTypeDeclared ∧ env.IotaTypeNotKey) :
    env'.IotaTypeDeclared ∧ env'.IotaTypeNotKey := by
  refine ⟨fun D j q C hdf => ?_, fun D j q C hdf df hdf' => ?_⟩
  · obtain ⟨ci, hci⟩ := H.1 D j q C (hd ▸ hdf); exact ⟨ci, hle.constants hci⟩
  · exact H.2 D j q C (hd ▸ hdf) df (hd ▸ hdf')

/-- **The step for a rule that is not an ι-rule** — `def`, `unsafeDef` and `quot`.

`hne` is the *relativised* form of "the new rule's key names are fresh": by the time the rule
is added its key names are declared (`.unsafeDef` and `quot` declare everything first), so the
freshness proxy is gone, exactly as `NoRuleFor` relativises `DefEqHeadsDeclared`.  What is
actually needed — no registered ι-rule's type name is among them — survives the intervening
`addConst`s because they do not touch `defeqs`. -/
theorem iotaTypes_addDefEq {env : VEnv} {df : VDefEq}
    (H : env.IotaTypeDeclared ∧ env.IotaTypeNotKey)
    (hnotiota : ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), df ≠ D.iotaRule j q C)
    (hne : ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), env.defeqs (D.iotaRule j q C) →
      (D.types.getD j default).name ∉ df.key) :
    (env.addDefEq df).IotaTypeDeclared ∧ (env.addDefEq df).IotaTypeNotKey := by
  refine ⟨fun D j q C hdf => ?_, fun D j q C hdf x hx => ?_⟩
  · rcases (hdf : _ ∨ _) with rfl | hdf
    · exact absurd rfl (hnotiota D j q C)
    · exact H.1 D j q C hdf
  · rcases (hdf : _ ∨ _) with rfl | hdf
    · exact absurd rfl (hnotiota D j q C)
    · rcases (hx : _ ∨ _) with rfl | hx
      · exact hne D j q C hdf
      · exact H.2 D j q C hdf x hx

/-- The δ-fold, for `.unsafeDef`.  Each rule of the block is a δ-rule whose head was fresh
before the block's constants were declared. -/
theorem iotaTypes_addDefEqs : ∀ {cis : List VDefVal} {env : VEnv},
    (env.IotaTypeDeclared ∧ env.IotaTypeNotKey) →
    (∀ ci ∈ cis, ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor),
      env.defeqs (D.iotaRule j q C) → (D.types.getD j default).name ≠ ci.name) →
    (env.addDefEqs cis).IotaTypeDeclared ∧ (env.addDefEqs cis).IotaTypeNotKey
  | [], _, H, _ => H
  | ci :: cis, env, H, hne => by
    have hkey : ci.toDefEq.key = [ci.name] := rfl
    have hnd : ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor),
        D.iotaRule j q C ≠ ci.toDefEq := by
      intro D j q C h
      exact not_isDeltaRule_iotaRule D j q C ci.name
        (show IsDeltaRule (D.iotaRule j q C) ci.name by rw [h]; exact toDefEq_isDeltaRule.2 rfl)
    have step := iotaTypes_addDefEq H (fun D j q C h => (hnd D j q C) h.symm)
      (by
        intro D j q C hdf hmem
        rw [hkey] at hmem
        exact hne ci (.head _) D j q C hdf (List.mem_singleton.1 hmem))
    refine iotaTypes_addDefEqs (cis := cis) step ?_
    intro ci' hci' D j q C hdf
    rcases (hdf : _ ∨ _) with hdf | hdf
    · exact absurd hdf (hnd D j q C)
    · exact hne ci' (.tail _ hci') D j q C hdf

/-- **The step for an ι-rule** — only `induct` adds these.  Three obligations beyond the
previous step: the new rule's own type name must be declared, must miss its own key, and must
miss every existing key; and no existing ι-rule's type name may be in the new key. -/
theorem iotaTypes_addDefEq_iota {env : VEnv} {df : VDefEq}
    (H : env.IotaTypeDeclared ∧ env.IotaTypeNotKey)
    (hdecl : ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), df = D.iotaRule j q C →
      env.contains (D.types.getD j default).name)
    (hself : ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), df = D.iotaRule j q C →
      (D.types.getD j default).name ∉ df.key)
    (hnew : ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), df = D.iotaRule j q C →
      ∀ df', env.defeqs df' → (D.types.getD j default).name ∉ df'.key)
    (hold : ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), env.defeqs (D.iotaRule j q C) →
      (D.types.getD j default).name ∉ df.key) :
    (env.addDefEq df).IotaTypeDeclared ∧ (env.addDefEq df).IotaTypeNotKey := by
  refine ⟨fun D j q C hdf => ?_, fun D j q C hdf x hx => ?_⟩
  · rcases (hdf : _ ∨ _) with rfl | hdf
    · exact hdecl D j q C rfl
    · exact H.1 D j q C hdf
  · rcases (hdf : _ ∨ _) with rfl | hdf
    · rcases (hx : _ ∨ _) with rfl | hx
      · exact hself D j q C rfl
      · exact hnew D j q C rfl x hx
    · rcases (hx : _ ∨ _) with rfl | hx
      · exact hold D j q C hdf
      · exact H.2 D j q C hdf x hx

/-- The ι-fold, for `induct`. -/
theorem iotaTypes_addDefEqList_iota : ∀ (dfs : List VDefEq) {env : VEnv},
    (env.IotaTypeDeclared ∧ env.IotaTypeNotKey) →
    (∀ df ∈ dfs, ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), df = D.iotaRule j q C →
      env.contains (D.types.getD j default).name) →
    (∀ df ∈ dfs, ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), df = D.iotaRule j q C →
      ∀ df' ∈ dfs, (D.types.getD j default).name ∉ df'.key) →
    (∀ df ∈ dfs, ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), df = D.iotaRule j q C →
      ∀ df', env.defeqs df' → (D.types.getD j default).name ∉ df'.key) →
    (∀ df ∈ dfs, ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor),
      env.defeqs (D.iotaRule j q C) → (D.types.getD j default).name ∉ df.key) →
    ((dfs.foldl VEnv.addDefEq env).IotaTypeDeclared ∧
      (dfs.foldl VEnv.addDefEq env).IotaTypeNotKey)
  | [], _, H, _, _, _, _ => H
  | df :: dfs, env, H, hdecl, hblock, hnew, hold => by
    have step := iotaTypes_addDefEq_iota H (hdecl df (.head _))
      (fun D j q C hq => hblock df (.head _) D j q C hq df (.head _))
      (hnew df (.head _)) (hold df (.head _))
    refine iotaTypes_addDefEqList_iota dfs step
      (fun x hx D j q C hq => ⟨_, VEnv.LE.constants VEnv.addDefEq_le
        (hdecl x (.tail _ hx) D j q C hq).choose_spec⟩)
      (fun x hx D j q C hq y hy => hblock x (.tail _ hx) D j q C hq y (.tail _ hy)) ?_ ?_
    · intro x hx D j q C hq df' hdf'
      rcases (hdf' : _ ∨ _) with rfl | hdf'
      · exact hblock x (.tail _ hx) D j q C hq df' (.head _)
      · exact hnew x (.tail _ hx) D j q C hq df' hdf'
    · intro x hx D j q C hdf
      rcases (hdf : _ ∨ _) with hdf | hdf
      · exact hblock df (.head _) D j q C hdf.symm x (.tail _ hx)
      · exact hold x (.tail _ hx) D j q C hdf

/-! ## The four arms -/

theorem iotaTypes_def {env env' : VEnv} {ci : VDefVal}
    (h : env.addConst ci.name ci.toVConstant = some env')
    (ih : env.IotaTypeDeclared ∧ env.IotaTypeNotKey) :
    (env'.addDefEq ci.toDefEq).IotaTypeDeclared ∧
      (env'.addDefEq ci.toDefEq).IotaTypeNotKey := by
  have hfresh : ¬ env.contains ci.name := by
    rintro ⟨x, hx⟩; rw [addConst_constants_eq_none h] at hx; exact absurd hx nofun
  refine iotaTypes_addDefEq (iotaTypes_mono (addConst_defeqs h) (addConst_le h) ih)
    (fun D j q C hq => not_isDeltaRule_iotaRule D j q C ci.name
      (show IsDeltaRule (D.iotaRule j q C) ci.name by
        rw [← hq]; exact toDefEq_isDeltaRule.2 rfl))
    ?_
  intro D j q C hdf hmem
  rw [addConst_defeqs h] at hdf
  exact hfresh (List.mem_singleton.1
    (show (D.types.getD j default).name ∈ [ci.name] from hmem) ▸ ih.1 D j q C hdf)

theorem iotaTypes_unsafeDef {env env' : VEnv} {cis : List VDefVal}
    (h : env.addConsts cis = some env')
    (ih : env.IotaTypeDeclared ∧ env.IotaTypeNotKey) :
    (env'.addDefEqs cis).IotaTypeDeclared ∧ (env'.addDefEqs cis).IotaTypeNotKey := by
  refine iotaTypes_addDefEqs (iotaTypes_mono (addConsts_defeqs h) (addConsts_le h) ih) ?_
  intro ci hci D j q C hdf heq
  rw [addConsts_defeqs h] at hdf
  exact addConsts_fresh h ci hci (heq ▸ ih.1 D j q C hdf)

theorem iotaTypes_quot {env env' : VEnv} (h : env.addQuot = some env')
    (ih : env.IotaTypeDeclared ∧ env.IotaTypeNotKey) :
    env'.IotaTypeDeclared ∧ env'.IotaTypeNotKey := by
  obtain ⟨e1, e2, e3, e4, h1, h2, h3, h4, rfl⟩ := addQuot_stages h
  have hdefeqs : e4.defeqs = env.defeqs := by
    rw [addConst_defeqs h4, addConst_defeqs h3, addConst_defeqs h2, addConst_defeqs h1]
  have hmk : ¬ env.contains ``Quot.mk := by
    rintro ⟨x, hx⟩
    have := (addConst_le h1).constants hx
    rw [addConst_constants_eq_none h2] at this; exact absurd this nofun
  have hlift : ¬ env.contains ``Quot.lift := by
    rintro ⟨x, hx⟩
    have := (addConst_le h2).constants ((addConst_le h1).constants hx)
    rw [addConst_constants_eq_none h3] at this; exact absurd this nofun
  refine iotaTypes_addDefEq (iotaTypes_mono hdefeqs
      (((addConst_le h1).trans (addConst_le h2)).trans
        ((addConst_le h3).trans (addConst_le h4))) ih) ?_ ?_
  · intro D j q C hq
    have hk := congrArg VDefEq.key hq
    rw [key_quotDefEq, VInductDecl'.key_iotaRule] at hk
    have : (Lean.mkRecName (D.types.getD j default).name : Lean.Name) = ``Quot.lift :=
      (List.cons.injEq .. ▸ hk).1.symm
    simp [Lean.mkRecName] at this
  · intro D j q C hdf hmem
    rw [hdefeqs] at hdf
    rw [key_quotDefEq] at hmem
    rcases List.mem_cons.1 hmem with he | he
    · exact hlift (he ▸ ih.1 D j q C hdf)
    · exact hmk (List.mem_singleton.1 he ▸ ih.1 D j q C hdf)

theorem _root_.Lean4Lean.mkRecName_inj {m n : Lean.Name}
    (h : Lean.mkRecName m = Lean.mkRecName n) : m = n := by
  simpa [Lean.mkRecName] using h

/-- **The `induct` arm.**  The one place both clauses have content, and the only one needing
`KeysDeclared` — to know an existing key name is declared, hence distinct from the block's
freshly declared type names. -/
theorem iotaTypes_induct {env env' : VEnv} {D' : VInductDecl'}
    (h : env.addInduct' D' = some env') (hkeys : env.KeysDeclared)
    (ih : env.IotaTypeDeclared ∧ env.IotaTypeNotKey) :
    env'.IotaTypeDeclared ∧ env'.IotaTypeNotKey := by
  obtain ⟨e1, e2, e3, h1, h2, h3, rfl⟩ := addInduct'_stages h
  have hdefeqs : e3.defeqs = env.defeqs := by
    rw [addConstList_defeqs h3, addConstList_defeqs h2, addConstList_defeqs h1]
  have hle : env ≤ e3 :=
    ((addConstList_le h1).trans (addConstList_le h2)).trans (addConstList_le h3)
  have htyfresh : ∀ n ∈ D'.blockNames, ¬ env.contains n := by
    rintro n hn ⟨x, hx⟩
    rw [(addConstList_fresh h1).1 n (by rwa [VInductDecl'.typeConsts_names])] at hx
    exact absurd hx nofun
  have hctorfresh : ∀ n ∈ D'.ctorConsts.map (·.1), ¬ env.contains n := by
    rintro n hn ⟨x, hx⟩
    have := (addConstList_le h1).constants hx
    rw [(addConstList_fresh h2).1 n hn] at this; exact absurd this nofun
  have hrecfresh : ∀ n ∈ D'.recConsts.map (·.1), ¬ env.contains n := by
    rintro n hn ⟨x, hx⟩
    have := (addConstList_le h2).constants ((addConstList_le h1).constants hx)
    rw [(addConstList_fresh h3).1 n hn] at this; exact absurd this nofun
  have htydecl : ∀ n ∈ D'.blockNames, e1.contains n := by
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (by rwa [← VInductDecl'.typeConsts_names] at hn)
    exact ⟨_, addConstList_constants h1 c hc⟩
  have htyne : ∀ n ∈ D'.blockNames,
      n ∉ D'.ctorConsts.map (·.1) ∧ n ∉ D'.recConsts.map (·.1) := by
    intro n hn
    obtain ⟨x, hx⟩ := htydecl n hn
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [(addConstList_fresh h2).1 n hc] at hx; exact absurd hx nofun
    · have hx2 := (addConstList_le h2).constants hx
      rw [(addConstList_fresh h3).1 n hc] at hx2; exact absurd hx2 nofun
  have hkey : ∀ df ∈ D'.iotaRules, ∀ n ∈ df.key,
      n ∈ D'.ctorConsts.map (·.1) ∨ n ∈ D'.recConsts.map (·.1) := by
    intro df hdf n hn
    obtain ⟨j, C, hjC, hk⟩ := VInductDecl'.mem_key_iotaRules hdf
    obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hjC
    rw [hk] at hn
    rcases List.mem_cons.1 hn with rfl | hn
    · refine .inr (List.mem_map.2 ⟨_, List.mem_map.2 ⟨(T, j), ?_, rfl⟩, ?_⟩)
      · exact List.mk_mem_zipIdx_iff_getElem?.2 hT
      · rw [D'.getD_types hT]
    · cases List.mem_singleton.1 hn
      exact .inl (List.mem_map.2 ⟨_, List.mem_map.2 ⟨(j, C), hjC, rfl⟩, rfl⟩)
  have hfresh : ∀ df ∈ D'.iotaRules, ∀ n ∈ df.key, ¬ env.contains n := by
    intro df hdf n hn
    rcases hkey df hdf n hn with hm | hm
    · exact hctorfresh n hm
    · exact hrecfresh n hm
  have hname : ∀ df ∈ D'.iotaRules, ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor),
      df = D.iotaRule j q C → (D.types.getD j default).name ∈ D'.blockNames := by
    intro df hdf D j q C hq
    obtain ⟨j', q', C', hqC', rfl⟩ := VInductDecl'.mem_iotaRules hdf
    obtain ⟨T', hT', hC'⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hqC')
    have hk := congrArg VDefEq.key hq
    rw [VInductDecl'.key_iotaRule, VInductDecl'.key_iotaRule] at hk
    have he := mkRecName_inj (List.cons.injEq .. ▸ hk).1.symm
    rw [he, D'.getD_types hT']
    exact List.mem_map.2 ⟨T', List.mem_of_getElem? hT', rfl⟩
  refine iotaTypes_addDefEqList_iota D'.iotaRules
    (iotaTypes_mono hdefeqs hle ih) ?_ ?_ ?_ ?_
  · intro df hdf D j q C hq
    exact ⟨_, ((addConstList_le h2).trans (addConstList_le h3)).constants
      (htydecl _ (hname df hdf D j q C hq)).choose_spec⟩
  · intro df hdf D j q C hq df' hdf' hmem
    rcases hkey df' hdf' _ hmem with hm | hm
    · exact (htyne _ (hname df hdf D j q C hq)).1 hm
    · exact (htyne _ (hname df hdf D j q C hq)).2 hm
  · intro df hdf D j q C hq df' hdf' hmem
    rw [hdefeqs] at hdf'
    exact htyfresh _ (hname df hdf D j q C hq) (hkeys df' hdf' _ hmem)
  · intro df hdf D j q C hdf' hmem
    rw [hdefeqs] at hdf'
    exact hfresh df hdf _ hmem (ih.1 D j q C hdf')

/-- **Part III's induction.**  It consumes `WF'.keys` at the `induct` arm rather than being
threaded through it — one extra traversal, no existing proof touched. -/
theorem WF'.iotaTypes {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    env.IotaTypeDeclared ∧ env.IotaTypeNotKey := by
  induction H with
  | empty => exact ⟨fun _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩
  | @decl env d env' ds hd hds ih =>
    cases hd with
    | «axiom» _ h | «opaque» _ h =>
      exact iotaTypes_mono (addConst_defeqs h) (addConst_le h) ih
    | «example» _ => exact ih
    | «def» _ h => exact iotaTypes_def h ih
    | unsafeDef _ h _ => exact iotaTypes_unsafeDef h ih
    | quot _ h => exact iotaTypes_quot h ih
    | induct _ h => exact iotaTypes_induct h (WF'.keys hds).1 ih

theorem WF.iotaTypeDeclared {env : VEnv} (h : env.WF) : env.IotaTypeDeclared :=
  (WF'.iotaTypes h.choose_spec).1

/-- **The payoff.**  No rule of a well-formed environment has an inductive type's name in its
key — so a block type name is not a recursor leaf, not a constructor leaf, not `Quot.lift` or
`Quot.mk`, and heads no δ-rule. -/
theorem WF.iotaTypeNotKey {env : VEnv} (h : env.WF) : env.IotaTypeNotKey :=
  (WF'.iotaTypes h.choose_spec).2

end VEnv


/-! # Part IV: uniqueness by the **whole** key

Part II's `KeyMajorUnique` — *a rule is determined by the head of its major premise* — is
`Params.pat_uniq`'s ι/ι case, and it is **the invariant a nested declaration step destroys.**
Not the freshness argument that proves it; the statement.

The reason is `VInductDecl'.key_iotaRuleR`.  A nested step emits, for a *companion* member,
an ι-rule keyed `[R.recName I_j.rec, R.ctorName C.name]`, and the second component is the
constructor of a block the environment **already holds** — `PFn.mk`, `List.cons`.  That
block's own ι-rule is keyed `[PFn.rec, PFn.mk]`.  Two distinct rules, one major-premise head.
`Theory/Inductive/NestedKeys.lean` exhibits exactly that pair at the `NFn`/`PFn` witness
(`nfn_keyMajorUnique_false`), so this is a refutation, not a proof gap.

What survives is uniqueness by the **whole** key, `KeyUnique`: the two rules above differ in
their *head*, and the head of a rule a nested step emits is a constant that step declares
itself, hence fresh.  §5.3 of `docs/handoff-inductive-add.md` observed that head freshness is
the freshness a nested step actually has; `KeyUnique` is the invariant that only needs it.

`KeyUnique` is proved here for the *current* tree the cheap way — from `KeyMajorUnique` plus
`KeysNonempty`, since every rule a declaration produces has a two- or one-element key — so
nothing in Part II is disturbed and no existing proof is re-run.  When the nested rule lands,
`KeyMajorUnique` must be **dropped** from `WF'.keys` and `KeyUnique` proved directly; the
three arms that change and the one consumer that has to move are listed in
`Theory/Inductive/NestedKeys.lean`. -/

namespace VEnv

/-- Every registered rule's key is non-empty.  True because every rule a declaration
produces is headed by a constant: `[v.name]`, `[Quot.lift, Quot.mk]`, `[I_j.rec, C.name]`. -/
def KeysNonempty (env : VEnv) : Prop := ∀ df, env.defeqs df → df.key ≠ []

/-- **A rule is determined by its whole key.**

Weaker than `KeyMajorUnique` in the presence of `KeysNonempty` — and, unlike it, *true* of an
environment holding a nested block. -/
def KeyUnique (env : VEnv) : Prop :=
  ∀ df df', env.defeqs df → env.defeqs df' → df.key = df'.key → df = df'

theorem key_toDefEq (v : VDefVal) : v.toDefEq.key = [v.name] := rfl

/-- `KeyMajorUnique` implies `KeyUnique` when no key is empty.  The converse fails: the two
rules of `nfn_keyMajorUnique_false` have the same last name and different keys. -/
theorem keyUnique_of_major {env : VEnv} (hne : env.KeysNonempty) (h : env.KeyMajorUnique) :
    env.KeyUnique := by
  intro df df' hdf hdf' hk
  cases hh : df.key.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.1 hh) (hne df hdf)
  | some n => exact h df df' n hdf hdf' hh (hk ▸ hh)

theorem keysNonempty_mono {env env' : VEnv} (hd : env'.defeqs = env.defeqs)
    (H : env.KeysNonempty) : env'.KeysNonempty := fun df hdf => H df (hd ▸ hdf)

theorem keysNonempty_addDefEq {env : VEnv} {df : VDefEq} (H : env.KeysNonempty)
    (hk : df.key ≠ []) : (env.addDefEq df).KeysNonempty := by
  rintro x (rfl | hx)
  · exact hk
  · exact H x hx

theorem keysNonempty_addDefEqs : ∀ {cis : List VDefVal} {env : VEnv},
    env.KeysNonempty → (env.addDefEqs cis).KeysNonempty := by
  intro cis env H df hdf
  rcases VEnv.addDefEqs_defeqs hdf with ⟨ci, -, rfl⟩ | hdf
  · rw [key_toDefEq]; exact nofun
  · exact H df hdf

theorem keysNonempty_addDefEqList (dfs : List VDefEq) {env : VEnv} (H : env.KeysNonempty)
    (hk : ∀ df ∈ dfs, df.key ≠ []) : (dfs.foldl VEnv.addDefEq env).KeysNonempty := by
  intro df hdf
  rcases addDefEqList_mem dfs hdf with h | h
  · exact hk df h
  · exact H df h

theorem keysNonempty_induct {env env' : VEnv} {D : VInductDecl'}
    (h : env.addInduct' D = some env') (ih : env.KeysNonempty) : env'.KeysNonempty := by
  obtain ⟨e1, e2, e3, h1, h2, h3, rfl⟩ := addInduct'_stages h
  refine keysNonempty_addDefEqList D.iotaRules (keysNonempty_mono ?_ ih) ?_
  · rw [addConstList_defeqs h3, addConstList_defeqs h2, addConstList_defeqs h1]
  · intro df hdf
    obtain ⟨j, C, -, hk⟩ := VInductDecl'.mem_key_iotaRules hdf
    rw [hk]; exact nofun

theorem WF'.keysNonempty {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    env.KeysNonempty := by
  induction H with
  | empty => exact fun _ h => h.elim
  | @decl env d env' ds hd _ ih =>
    cases hd with
    | «axiom» _ h | «opaque» _ h => exact keysNonempty_mono (addConst_defeqs h) ih
    | «example» _ => exact ih
    | «def» v h =>
      exact keysNonempty_addDefEq (keysNonempty_mono (addConst_defeqs h) ih)
        (by rw [key_toDefEq]; exact nofun)
    | unsafeDef _ h _ =>
      exact keysNonempty_addDefEqs (keysNonempty_mono (addConsts_defeqs h) ih)
    | quot _ h =>
      obtain ⟨e1, e2, e3, e4, h1, h2, h3, h4, rfl⟩ := addQuot_stages h
      refine keysNonempty_addDefEq (keysNonempty_mono ?_ ih)
        (by rw [key_quotDefEq]; exact nofun)
      rw [addConst_defeqs h4, addConst_defeqs h3, addConst_defeqs h2, addConst_defeqs h1]
    | induct _ h => exact keysNonempty_induct h ih

theorem WF.keysNonempty {env : VEnv} (h : env.WF) : env.KeysNonempty :=
  WF'.keysNonempty h.choose_spec

/-! ## The `KeyUnique` step lemmas

The `KeyMajorUnique` versions above (`keys_addDefEq_notDelta`, `keys_addDefEqList_notDelta`)
ask that the new rule's *last* key name be new.  These ask instead that its *whole key* be
new, which is what a nested step can supply: its rules are headed by constants it declares
itself.  Everything else is unchanged, so the two families sit side by side and the
`KeyMajorUnique` proofs are untouched. -/

theorem keysU_mono {env env' : VEnv} (hd : env'.defeqs = env.defeqs) (hle : env ≤ env')
    (H : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyUnique) :
    env'.KeysDeclared ∧ env'.KeyHeadDelta ∧ env'.KeyUnique := by
  obtain ⟨H1, H2, H3⟩ := H
  refine ⟨fun df hdf n hn => ?_, fun df df' c hdf hdf' => ?_, fun df df' hdf hdf' => ?_⟩
  · obtain ⟨ci, hci⟩ := H1 df (hd ▸ hdf) n hn; exact ⟨ci, hle.constants hci⟩
  · exact H2 df df' c (hd ▸ hdf) (hd ▸ hdf')
  · exact H3 df df' (hd ▸ hdf) (hd ▸ hdf')

/-- **The step for a non-δ rule whose key is new as a whole.**  `hkey` replaces
`keys_addDefEq_notDelta`'s `hmaj`: the new rule's key differs from every registered rule's
key, rather than its last name being absent from every registered key. -/
theorem keysU_addDefEq_notDelta {env : VEnv} {df : VDefEq}
    (H : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyUnique)
    (hnd : ∀ c, ¬ IsDeltaRule df c)
    (hdecl : ∀ n ∈ df.key, env.contains n)
    (hδ : ∀ df' c, env.defeqs df' → IsDeltaRule df' c → c ∉ df.key)
    (hkey : ∀ df', env.defeqs df' → df.key ≠ df'.key) :
    (env.addDefEq df).KeysDeclared ∧ (env.addDefEq df).KeyHeadDelta ∧
      (env.addDefEq df).KeyUnique := by
  obtain ⟨H1, H2, H3⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · rintro x (rfl | hx) n hn
    · exact hdecl n hn
    · exact H1 x hx n hn
  · rintro x y c (rfl | hx) (rfl | hy) hd hc
    · rfl
    · exact absurd hd (hnd c)
    · exact absurd hc (hδ x c hx hd)
    · exact H2 x y c hx hy hd hc
  · rintro x y (rfl | hx) (rfl | hy) hk
    · rfl
    · exact absurd hk (hkey y hy)
    · exact absurd hk.symm (hkey x hx)
    · exact H3 x y hx hy hk

/-- The fold, for a block of non-δ rules with pairwise distinct keys. -/
theorem keysU_addDefEqList_notDelta : ∀ (dfs : List VDefEq) {env : VEnv},
    (env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyUnique) →
    (∀ df ∈ dfs, ∀ c, ¬ IsDeltaRule df c) →
    (∀ df ∈ dfs, ∀ n ∈ df.key, env.contains n) →
    (∀ df ∈ dfs, ∀ df' c, env.defeqs df' → IsDeltaRule df' c → c ∉ df.key) →
    (∀ df ∈ dfs, ∀ df', env.defeqs df' → df.key ≠ df'.key) →
    dfs.Pairwise (fun a b => a.key ≠ b.key) →
    (dfs.foldl VEnv.addDefEq env).KeysDeclared ∧
      (dfs.foldl VEnv.addDefEq env).KeyHeadDelta ∧
      (dfs.foldl VEnv.addDefEq env).KeyUnique
  | [], _, H, _, _, _, _, _ => H
  | df :: dfs, env, H, hnd, hdecl, hδ, hkey, hp => by
    have hpc := List.pairwise_cons.1 hp
    have step := keysU_addDefEq_notDelta H (hnd df (.head _)) (hdecl df (.head _))
      (hδ df (.head _)) (hkey df (.head _))
    refine keysU_addDefEqList_notDelta dfs step
      (fun x hx => hnd x (.tail _ hx))
      (fun x hx n hn => ⟨_, VEnv.LE.constants VEnv.addDefEq_le
        (hdecl x (.tail _ hx) n hn).choose_spec⟩) ?_ ?_ hpc.2
    · intro x hx df' c hdf'
      have hor : df' = df ∨ env.defeqs df' := hdf'
      rcases hor with rfl | hdf'
      · exact fun hd => absurd hd (hnd df' (.head _) c)
      · exact hδ x (.tail _ hx) df' c hdf'
    · intro x hx df' hdf'
      have hor : df' = df ∨ env.defeqs df' := hdf'
      rcases hor with rfl | hdf'
      · exact (hpc.1 x hx).symm
      · exact hkey x (.tail _ hx) df' hdf'

/-- **The invariant `Params.pat_uniq`'s ι/ι case should be reading.**  Equal to
`WF.keyMajorUnique` today; the two part company exactly at a nested step. -/
theorem WF.keyUnique {env : VEnv} (h : env.WF) : env.KeyUnique :=
  keyUnique_of_major h.keysNonempty h.keyMajorUnique

end VEnv

end Lean4Lean
