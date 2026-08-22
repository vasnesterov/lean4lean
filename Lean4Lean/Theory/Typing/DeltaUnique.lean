import Lean4Lean.Theory.Typing.Env

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

end VEnv
end Lean4Lean
