import Lean4Lean.Theory.Typing.Lemmas

/-!
# Substituting a constant by a term

`Theory/` has two ways to move a judgement from one environment to another, and until now
only two: `VEnv.IsDefEq.mono` (weaken along `env ≤ env'`) and `VEnv.IsDefEq.instL`
(instantiate the universe parameters).  Neither can **remove a constant**: `mono` only ever
adds, and `instL` does not touch the constant map at all.

This file adds the third: a judgement in `env₀` is transported to `env₁` along a *constant
substitution* `σ : CSubst`, a partial map from constant names to closed terms.  Every
constant in `σ`'s domain is replaced by its value; `env₁` need not declare it.

The motivating consumer is the nested-inductive step (`Theory/Inductive/NestedOrdered.lean`,
obligation **(A)**).  There a declared constructor's recursive field is *stored* against an
auxiliary constant (`∀ ξ, _nested.PFn_1 …`) in a staging environment that holds it, and
*restored* against the real one (`∀ ξ, PFn A …`) in a staging environment that does not.
`Theory/Typing/ConstSubstNested.lean` fires the theorem there.

## The statement, and why each hypothesis is there

`CSubst.WF σ env₀ env₁ U` has four fields, and each one is forced by exactly one rule of
`VEnv.IsDefEq`:

* `closed` — the values are closed.  Forced by every binder: without it `substC` captures,
  and it is what makes `substC` commute with `liftN` and `inst`.
* `const` — every constant of `env₀` **outside** `σ`'s domain survives in `env₁`, *with its
  own type substituted*.  Forced by `constDF`.  This is the clause that carries all the
  information: it constrains `env₁` at every constant `env₀` has.
* `defeq` — every definitional equation of `env₀` survives, substituted.  Forced by `extra`.
* `val` — for a constant `c` **in** `σ`'s domain, its value really does inhabit its declared
  type, at every level instantiation and in every context.  Forced by `constDF` again, in the
  other branch.

`val` is the one to read carefully.  It is *not* "σ c is well typed"; it is a **defeq**
between the value at two `≈`-equivalent level lists, because `constDF` relates
`.const c ls` to `.const c ls'` whenever `ls ≈ ls'`.  A version of `val` asking only for
`env₁.HasType U [] t ci.type` is strictly weaker and **does not suffice**: closing the gap
needs `t.instL ls ≡ t.instL ls'`, i.e. congruence of typing under `≈` of universe levels,
which is not available (see `CSubst.WF.val_of_uvars_zero` for the case where it is free).

The context quantifier in `val` is unrestricted on purpose.  `VEnv.IsDefEq` never demands a
well-formed context (`sortDF` and `constDF` have no premise about `Γ`), so no invariant on
`Γ` survives the induction; and for a closed value the quantifier is discharged once and for
all by `IsDefEq.weak0`.
-/

namespace Lean4Lean

open Lean (Name)

/-- A **constant substitution**: a partial map from constant names to (closed) terms. -/
abbrev CSubst := Name → Option VExpr

/-- The empty substitution. -/
def CSubst.id : CSubst := fun _ => none

/-- The one-point substitution `c ↦ t`. -/
def CSubst.one (c : Name) (t : VExpr) : CSubst := fun n => if n = c then some t else none

@[simp] theorem CSubst.one_self : CSubst.one c t c = some t := if_pos rfl

theorem CSubst.one_of_ne (h : n ≠ c) : CSubst.one c t n = none := if_neg h

namespace VExpr

/-- Replace every constant in `σ`'s domain by its value, instantiated at the universe
levels of the occurrence.  Nothing else moves; in particular the value is *not* shifted,
which is sound only because `CSubst.Closed` requires it to be closed. -/
def substC : VExpr → CSubst → VExpr
  | .bvar i, _ => .bvar i
  | .sort u, _ => .sort u
  | .const c ls, σ => match σ c with | some t => t.instL ls | none => .const c ls
  | .app f a, σ => .app (f.substC σ) (a.substC σ)
  | .lam A b, σ => .lam (A.substC σ) (b.substC σ)
  | .forallE A b, σ => .forallE (A.substC σ) (b.substC σ)

/-- Every value of `σ` is closed. -/
def _root_.Lean4Lean.CSubst.Closed (σ : CSubst) : Prop := ∀ {c t}, σ c = some t → t.ClosedN

variable {σ : CSubst}

@[simp] theorem substC_bvar : (VExpr.bvar i).substC σ = .bvar i := rfl
@[simp] theorem substC_sort : (VExpr.sort u).substC σ = .sort u := rfl
@[simp] theorem substC_app : (VExpr.app f a).substC σ = .app (f.substC σ) (a.substC σ) := rfl
@[simp] theorem substC_lam : (VExpr.lam A b).substC σ = .lam (A.substC σ) (b.substC σ) := rfl
@[simp] theorem substC_forallE :
    (VExpr.forallE A b).substC σ = .forallE (A.substC σ) (b.substC σ) := rfl

theorem substC_const_none (h : σ c = none) : (VExpr.const c ls).substC σ = .const c ls := by
  simp [substC, h]

theorem substC_const_some (h : σ c = some t) : (VExpr.const c ls).substC σ = t.instL ls := by
  simp [substC, h]

@[simp] theorem substC_id (e : VExpr) : e.substC CSubst.id = e := by
  induction e <;> simp [substC, CSubst.id, *]

/-- `substC` commutes with universe instantiation.  This is the equation that makes the
`constDF` case of the main theorem typecheck, and it needs no hypothesis: the value is
re-instantiated at the composite level list, which is `VExpr.instL_instL`. -/
theorem substC_instL {e : VExpr} : (e.instL ls).substC σ = (e.substC σ).instL ls := by
  induction e with
  | bvar => rfl
  | sort => rfl
  | const c us => cases h : σ c <;> simp [VExpr.instL, substC, h, instL_instL]
  | app _ _ ih1 ih2 => simp [VExpr.instL, ih1, ih2]
  | lam _ _ ih1 ih2 => simp [VExpr.instL, ih1, ih2]
  | forallE _ _ ih1 ih2 => simp [VExpr.instL, ih1, ih2]

/-- `substC` commutes with lifting — because the values are closed, so lifting cannot see
them.  Without `CSubst.Closed` this is false at the first binder. -/
theorem substC_liftN (hσ : σ.Closed) {e : VExpr} {n k : Nat} :
    (e.liftN n k).substC σ = (e.substC σ).liftN n k := by
  induction e generalizing k with
  | bvar => rfl
  | sort => rfl
  | const c us =>
    cases h : σ c
    · simp [VExpr.liftN, substC, h]
    · simp [VExpr.liftN, substC, h, ((hσ h).instL (ls := us)).liftN_eq (Nat.zero_le _)]
  | app _ _ ih1 ih2 => simp [VExpr.liftN, ih1, ih2]
  | lam _ _ ih1 ih2 => simp [VExpr.liftN, ih1, ih2]
  | forallE _ _ ih1 ih2 => simp [VExpr.liftN, ih1, ih2]

theorem substC_lift (hσ : σ.Closed) {e : VExpr} : e.lift.substC σ = (e.substC σ).lift :=
  substC_liftN hσ

/-- `substC` commutes with term instantiation. -/
theorem substC_inst (hσ : σ.Closed) {e a : VExpr} {k : Nat} :
    (e.inst a k).substC σ = (e.substC σ).inst (a.substC σ) k := by
  induction e generalizing k with
  | bvar i =>
    show (instVar i a k).substC σ = instVar i (a.substC σ) k
    simp only [instVar]
    split
    · rfl
    · split
      · exact substC_liftN hσ
      · rfl
  | sort => rfl
  | const c us =>
    cases h : σ c
    · simp [VExpr.inst, substC, h]
    · simp [VExpr.inst, substC, h, ((hσ h).instL (ls := us)).instN_eq (Nat.zero_le _)]
  | app _ _ ih1 ih2 => simp [VExpr.inst, ih1, ih2]
  | lam _ _ ih1 ih2 => simp [VExpr.inst, ih1, ih2]
  | forallE _ _ ih1 ih2 => simp [VExpr.inst, ih1, ih2]

end VExpr

/-- A definitional equation, substituted entrywise. -/
def VDefEq.substC (df : VDefEq) (σ : CSubst) : VDefEq :=
  { uvars := df.uvars, lhs := df.lhs.substC σ, rhs := df.rhs.substC σ, type := df.type.substC σ }

@[simp] theorem VDefEq.substC_uvars {df : VDefEq} {σ : CSubst} :
    (df.substC σ).uvars = df.uvars := rfl
@[simp] theorem VDefEq.substC_lhs {df : VDefEq} {σ : CSubst} :
    (df.substC σ).lhs = df.lhs.substC σ := rfl
@[simp] theorem VDefEq.substC_rhs {df : VDefEq} {σ : CSubst} :
    (df.substC σ).rhs = df.rhs.substC σ := rfl
@[simp] theorem VDefEq.substC_type {df : VDefEq} {σ : CSubst} :
    (df.substC σ).type = df.type.substC σ := rfl

theorem Lookup.substC {σ : CSubst} (hσ : σ.Closed) {Γ : List VExpr} {i : Nat} {A : VExpr}
    (H : Lookup Γ i A) : Lookup (Γ.map (VExpr.substC · σ)) i (A.substC σ) := by
  induction H with
  | @zero ty Γ => rw [VExpr.substC_lift hσ]; exact .zero
  | @succ Γ n ty A _ ih => rw [VExpr.substC_lift hσ]; exact .succ ih

/-- **What a constant substitution owes the two environments.**  See the module docstring
for why each field is forced. -/
structure CSubst.WF (σ : CSubst) (env₀ env₁ : VEnv) (U : Nat) : Prop where
  /-- Every value is closed. -/
  closed : σ.Closed
  /-- Constants outside `σ`'s domain survive, with their own types substituted. -/
  const : ∀ {c ci}, σ c = none → env₀.constants c = some ci →
    env₁.constants c = some ⟨ci.uvars, ci.type.substC σ⟩
  /-- Definitional equations survive, substituted. -/
  defeq : ∀ {df}, env₀.defeqs df → env₁.defeqs (df.substC σ)
  /-- A value inhabits the declared type of the constant it replaces — at every pair of
  `≈`-equivalent level instantiations, and in every context. -/
  val : ∀ {c t ci Γ ls ls'}, σ c = some t → env₀.constants c = some ci →
    (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
    ls.length = ci.uvars →
    env₁.IsDefEq U Γ (t.instL ls) (t.instL ls') ((ci.type.substC σ).instL ls)

namespace VEnv

variable {env₀ env₁ : VEnv} {σ : CSubst}

/-- The `constDF` case, factored out. -/
theorem IsDefEq.substC_constDF (hσ : σ.WF env₀ env₁ U)
    (h1 : env₀.constants c = some ci) (h2 : ∀ l ∈ ls, l.WF U) (h3 : ∀ l ∈ ls', l.WF U)
    (h4 : ls.length = ci.uvars) (h5 : List.Forall₂ (· ≈ ·) ls ls') :
    env₁.IsDefEq U Γ ((VExpr.const c ls).substC σ) ((VExpr.const c ls').substC σ)
      ((ci.type.instL ls).substC σ) := by
  rw [VExpr.substC_instL]
  cases h : σ c with
  | none =>
    rw [VExpr.substC_const_none h, VExpr.substC_const_none h]
    exact .constDF (hσ.const h h1) h2 h3 h4 h5
  | some t =>
    rw [VExpr.substC_const_some h, VExpr.substC_const_some h]
    exact hσ.val h h1 h2 h3 h5 h4

/-- The `extra` case, factored out. -/
theorem IsDefEq.substC_extra (hσ : σ.WF env₀ env₁ U)
    (h1 : env₀.defeqs df) (h2 : ∀ l ∈ ls, l.WF U) (h3 : ls.length = df.uvars) :
    env₁.IsDefEq U Γ ((df.lhs.instL ls).substC σ) ((df.rhs.instL ls).substC σ)
      ((df.type.instL ls).substC σ) := by
  simp only [VExpr.substC_instL]
  exact .extra (hσ.defeq h1) h2 h3

/-- **Substitution of constants by terms preserves typing.**

The third way to move a judgement between environments, and the only one that can *remove* a
constant: `env₁` need not declare anything in `σ`'s domain. -/
theorem IsDefEq.substC (hσ : σ.WF env₀ env₁ U) (H : env₀.IsDefEq U Γ e1 e2 A) :
    env₁.IsDefEq U (Γ.map (VExpr.substC · σ)) (e1.substC σ) (e2.substC σ) (A.substC σ) := by
  induction H with
  | bvar h => exact .bvar (h.substC hσ.closed)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact substC_constDF hσ h1 h2 h3 h4 h5
  | appDF _ _ ih1 ih2 =>
    rw [VExpr.substC_inst hσ.closed]; exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 =>
    rw [VExpr.substC_inst hσ.closed, VExpr.substC_inst hσ.closed]; exact .beta ih1 ih2
  | eta _ ih =>
    rw [VExpr.substC_lam, VExpr.substC_app, VExpr.substC_lift hσ.closed]
    exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact substC_extra hσ h1 h2 h3

theorem HasType.substC (hσ : σ.WF env₀ env₁ U) (H : env₀.HasType U Γ e A) :
    env₁.HasType U (Γ.map (VExpr.substC · σ)) (e.substC σ) (A.substC σ) :=
  IsDefEq.substC hσ H

theorem IsType.substC (hσ : σ.WF env₀ env₁ U) (H : env₀.IsType U Γ A) :
    env₁.IsType U (Γ.map (VExpr.substC · σ)) (A.substC σ) :=
  let ⟨_, h⟩ := H; ⟨_, h.substC hσ⟩

theorem IsDefEqU.substC (hσ : σ.WF env₀ env₁ U) (H : env₀.IsDefEqU U Γ e1 e2) :
    env₁.IsDefEqU U (Γ.map (VExpr.substC · σ)) (e1.substC σ) (e2.substC σ) :=
  let ⟨_, h⟩ := H; ⟨_, h.substC hσ⟩

end VEnv

/-- **The form the nested step wants**: a constant's declared type, substituted, is still a
type — in an environment that need not declare anything `σ` replaces. -/
theorem VConstant.WF.substC {env₀ env₁ : VEnv} {σ : CSubst} {ci : VConstant}
    (hσ : σ.WF env₀ env₁ ci.uvars) (H : ci.WF env₀) :
    VConstant.WF env₁ ⟨ci.uvars, ci.type.substC σ⟩ := by
  show env₁.IsType ci.uvars [] (ci.type.substC σ)
  simpa using VEnv.IsType.substC hσ H


/-- The same for a definitional equation: a rule of `env₀` is still a rule after
substitution.  Wanted for the nested step's ι-rule obligation. -/
theorem VDefEq.WF.substC {env₀ env₁ : VEnv} {σ : CSubst} {df : VDefEq}
    (hσ : σ.WF env₀ env₁ df.uvars) (H : df.WF env₀) : (df.substC σ).WF env₁ :=
  ⟨by simpa using VEnv.HasType.substC hσ H.1, by simpa using VEnv.HasType.substC hσ H.2⟩

/-! ## Discharging the hypotheses

`CSubst.WF`'s `const` and `defeq` clauses ask for the *substituted* type of every other
constant.  In the intended use `σ`'s domain is **fresh** in the environment the other
constants came from, so those types are untouched and the clauses reduce to plain
containment.  `VEnv.Ordered.noCSubst` is what makes that a theorem rather than a hypothesis:
a well-formed environment only ever mentions constants it declares. -/

namespace VExpr

/-- `e` mentions no constant in `σ`'s domain. -/
def NoCSubst (σ : CSubst) : VExpr → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const c _ => σ c = none
  | .app a b | .lam a b | .forallE a b => NoCSubst σ a ∧ NoCSubst σ b

variable {σ : CSubst}

theorem NoCSubst.substC_eq : ∀ {e : VExpr}, e.NoCSubst σ → e.substC σ = e
  | .bvar _, _ | .sort _, _ => rfl
  | .const .., h => substC_const_none h
  | .app .., h | .lam .., h | .forallE .., h => by
    simp [substC, h.1.substC_eq, h.2.substC_eq]

theorem NoCSubst.liftN : ∀ {e : VExpr} {n k}, e.NoCSubst σ → (e.liftN n k).NoCSubst σ
  | .bvar _, _, _, h | .sort _, _, _, h | .const .., _, _, h => h
  | .app .., _, _, h | .lam .., _, _, h | .forallE .., _, _, h => ⟨h.1.liftN, h.2.liftN⟩

theorem NoCSubst.instL : ∀ {e : VExpr} {ls}, e.NoCSubst σ → (e.instL ls).NoCSubst σ
  | .bvar _, _, h | .sort _, _, h | .const .., _, h => h
  | .app .., _, h | .lam .., _, h | .forallE .., _, h => ⟨h.1.instL, h.2.instL⟩

theorem NoCSubst.inst : ∀ {e a : VExpr} {k}, e.NoCSubst σ → a.NoCSubst σ →
    (e.inst a k).NoCSubst σ
  | .bvar i, _, k, _, ha => by
    show (VExpr.instVar i _ k).NoCSubst σ
    simp only [instVar]; split; · trivial
    split; · exact ha.liftN
    trivial
  | .sort _, _, _, h, _ | .const .., _, _, h, _ => h
  | .app .., _, _, h, ha | .lam .., _, _, h, ha | .forallE .., _, _, h, ha =>
    ⟨h.1.inst ha, h.2.inst ha⟩

end VExpr

/-- `σ`'s domain is disjoint from the constants `env` declares. -/
def CSubst.FreshIn (σ : CSubst) (env : VEnv) : Prop :=
  ∀ c ci, env.constants c = some ci → σ c = none

/-- A definitional equation mentioning no constant in `σ`'s domain. -/
def VDefEq.NoCSubst (df : VDefEq) (σ : CSubst) : Prop :=
  df.lhs.NoCSubst σ ∧ df.rhs.NoCSubst σ ∧ df.type.NoCSubst σ

theorem VDefEq.NoCSubst.substC_eq {df : VDefEq} {σ : CSubst} (h : df.NoCSubst σ) :
    df.substC σ = df := by
  obtain ⟨h1, h2, h3⟩ := h
  cases df; simp [VDefEq.substC, h1.substC_eq, h2.substC_eq, h3.substC_eq]

theorem Lookup.noCSubst {σ : CSubst} {Γ : List VExpr} (hΓ : ∀ B ∈ Γ, B.NoCSubst σ) :
    ∀ {i A}, Lookup Γ i A → A.NoCSubst σ
  | _, _, .zero => (hΓ _ List.mem_cons_self).liftN
  | _, _, .succ h => (Lookup.noCSubst (fun _ hB => hΓ _ (List.mem_cons_of_mem _ hB)) h).liftN

namespace VEnv

variable {env : VEnv} {σ : CSubst}

/-- **Nothing derivable in `env` mentions a constant `env` does not declare.**  The
analogue of `IsDefEq.closedN'` for constants; `Ordered.noCSubst` is its environment-level
consequence. -/
theorem IsDefEq.noCSubst'
    (henv : env.OnTypes fun _ e A => e.NoCSubst σ ∧ A.NoCSubst σ)
    (hfresh : σ.FreshIn env)
    (H : env.IsDefEq U Γ e1 e2 A) (hΓ : ∀ B ∈ Γ, B.NoCSubst σ) :
    e1.NoCSubst σ ∧ e2.NoCSubst σ ∧ A.NoCSubst σ := by
  induction H with
  | bvar h => exact ⟨trivial, trivial, h.noCSubst hΓ⟩
  | sortDF => exact ⟨trivial, trivial, trivial⟩
  | constDF h1 =>
    let ⟨_, h, _⟩ := henv.1 h1
    exact ⟨hfresh _ _ h1, hfresh _ _ h1, h.instL⟩
  | symm _ ih => let ⟨h1, h2, h3⟩ := ih hΓ; exact ⟨h2, h1, h3⟩
  | trans _ _ ih1 ih2 => exact ⟨(ih1 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.2⟩
  | appDF _ _ ih1 ih2 =>
    let ⟨hf, hf', _, hB⟩ := ih1 hΓ
    let ⟨ha, ha', _⟩ := ih2 hΓ
    exact ⟨⟨hf, ha⟩, ⟨hf', ha'⟩, hB.inst ha⟩
  | lamDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', hB⟩ := ih2 (List.forall_mem_cons.2 ⟨hA, hΓ⟩)
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, hA, hB⟩
  | forallEDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', _⟩ := ih2 (List.forall_mem_cons.2 ⟨hA, hΓ⟩)
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, trivial⟩
  | defeqDF _ _ ih1 ih2 => exact ⟨(ih2 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.1⟩
  | beta _ _ ih1 ih2 =>
    let ⟨he', _, hA⟩ := ih2 hΓ
    let ⟨he, _, hB⟩ := ih1 (List.forall_mem_cons.2 ⟨hA, hΓ⟩)
    exact ⟨⟨⟨hA, he⟩, he'⟩, he.inst he', hB.inst he'⟩
  | eta _ ih =>
    let ⟨he, _, hA, hB⟩ := ih hΓ
    exact ⟨⟨hA, he.liftN, trivial⟩, he, hA, hB⟩
  | proofIrrel _ _ _ _ ih2 ih3 =>
    let ⟨hh, _, _⟩ := ih2 hΓ
    let ⟨hh', _, hp⟩ := ih3 hΓ
    exact ⟨hh, hh', hp⟩
  | extra h1 _ _ =>
    let ⟨⟨hl, _⟩, ⟨hr, hA⟩⟩ := henv.2 h1
    exact ⟨hl.instL, hr.instL, hA.instL⟩

/-- **A well-formed environment is `σ`-free as soon as `σ`'s domain is fresh in it.** -/
theorem Ordered.noCSubst (H : env.Ordered) (hfresh : σ.FreshIn env) :
    env.OnTypes fun _ e A => e.NoCSubst σ ∧ A.NoCSubst σ := by
  have main := H.induction
    (motive := fun env _ e A => σ.FreshIn env → e.NoCSubst σ ∧ A.NoCSubst σ)
    (fun hle ih hf => ih fun _ _ h => hf _ _ (hle.1 h))
    (fun _ ih ht hf =>
      let ⟨h1, _, h3⟩ := IsDefEq.noCSubst'
        ⟨fun h => (ih.1 h).imp fun _ hh => hh hf, fun h => (ih.2 h).imp (· hf) (· hf)⟩
        hf ht nofun
      ⟨h1, h3⟩)
  exact ⟨fun h => (main.1 h).imp fun _ hh => hh hfresh,
    fun h => (main.2 h).imp (· hfresh) (· hfresh)⟩

theorem Ordered.noCSubstC (H : env.Ordered) (hfresh : σ.FreshIn env)
    (h : env.constants n = some ci) : ci.type.NoCSubst σ :=
  let ⟨_, h, _⟩ := (H.noCSubst hfresh).1 h; h

theorem Ordered.noCSubstD (H : env.Ordered) (hfresh : σ.FreshIn env)
    (h : env.defeqs df) : df.NoCSubst σ :=
  let ⟨⟨hl, hty⟩, hr, _⟩ := (H.noCSubst hfresh).2 h; ⟨hl, hr, hty⟩

end VEnv

/-! ## The universe-free case

`CSubst.WF.val` is a defeq between the value at two `≈`-equivalent level lists.  When the
replaced constant has **no** universe parameters both lists are empty, the two sides
coincide, and the clause follows from plain well-typedness.  This is the case the nested
witnesses are in, and it is stated separately because the general case is *not* free: it
needs congruence of typing under `≈`, which `Theory/` does not have. -/

theorem CSubst.val_zero' {env₁ : VEnv} {σ : CSubst} {t : VExpr} {ci : VConstant} {U : Nat}
    (henv₁ : env₁.Ordered) (hu : ci.uvars = 0)
    (ht1 : t.instL ([] : List VLevel) = t)
    (ht2 : (ci.type.substC σ).instL ([] : List VLevel) = ci.type.substC σ)
    (ht : env₁.HasType 0 [] t (ci.type.substC σ)) :
    ∀ {Γ : List VExpr} {ls ls' : List VLevel}, (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) →
      List.Forall₂ (· ≈ ·) ls ls' → ls.length = ci.uvars →
      env₁.IsDefEq U Γ (t.instL ls) (t.instL ls') ((ci.type.substC σ).instL ls) := by
  intro Γ ls ls' _ _ h5 h4
  rw [hu] at h4
  match ls, h4 with
  | [], _ =>
  cases h5
  have h : env₁.IsDefEq U Γ (t.instL ([] : List VLevel)) (t.instL ([] : List VLevel))
      ((ci.type.substC σ).instL ([] : List VLevel)) :=
    (VEnv.IsDefEq.instL (ls := []) (U' := U) nofun ht).weak0 henv₁
  rw [ht1, ht2] at h
  rw [ht1, ht2]
  exact h

theorem CSubst.val_zero {env₁ : VEnv} {σ : CSubst} {t : VExpr} {ci : VConstant} {U : Nat}
    (henv₁ : env₁.Ordered) (hu : ci.uvars = 0)
    (hlt : t.LevelWF 0) (hlty : (ci.type.substC σ).LevelWF 0)
    (ht : env₁.HasType 0 [] t (ci.type.substC σ)) :
    ∀ {Γ : List VExpr} {ls ls' : List VLevel}, (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) →
      List.Forall₂ (· ≈ ·) ls ls' → ls.length = ci.uvars →
      env₁.IsDefEq U Γ (t.instL ls) (t.instL ls') ((ci.type.substC σ).instL ls) := by
  intro Γ ls ls' _ _ h5 h4
  rw [hu] at h4
  match ls, h4 with
  | [], _ =>
  cases h5
  have ht1 : t.instL ([] : List VLevel) = t := hlt.instL_id
  have ht2 : (ci.type.substC σ).instL ([] : List VLevel) = ci.type.substC σ := hlty.instL_id
  have h : env₁.IsDefEq U Γ (t.instL ([] : List VLevel)) (t.instL ([] : List VLevel))
      ((ci.type.substC σ).instL ([] : List VLevel)) :=
    (VEnv.IsDefEq.instL (ls := []) (U' := U) nofun ht).weak0 henv₁
  rw [ht1, ht2] at h
  rw [ht1, ht2]
  exact h

/-- **The one-constant case, packaged.**  This is the shape the nested step is in: one
auxiliary constant, replaced by a closed term, in an environment that has every other
constant of the staging environment and nothing that mentions the auxiliary name.  The
`val` clause is left as a hypothesis; `CSubst.one_WF` discharges it when the replaced
constant has no universe parameters. -/
theorem CSubst.one_WF' {env₀ env₁ : VEnv} {c : Name} {t : VExpr} {ci : VConstant} {U : Nat}
    (hcl : t.ClosedN)
    (h₀ : env₀.constants c = some ci)
    (hcty : ci.type.NoCSubst (CSubst.one c t))
    (hval : ∀ {Γ : List VExpr} {ls ls' : List VLevel}, (∀ l ∈ ls, l.WF U) →
      (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' → ls.length = ci.uvars →
      env₁.IsDefEq U Γ (t.instL ls) (t.instL ls') (ci.type.instL ls))
    (hconst : ∀ c' ci', c' ≠ c → env₀.constants c' = some ci' →
      env₁.constants c' = some ci' ∧ ci'.type.NoCSubst (CSubst.one c t))
    (hdefeq : ∀ df, env₀.defeqs df → env₁.defeqs df ∧ df.NoCSubst (CSubst.one c t)) :
    (CSubst.one c t).WF env₀ env₁ U where
  closed {c' t'} h := by
    unfold CSubst.one at h; split at h
    · cases h; exact hcl
    · exact absurd h nofun
  const {c' ci'} hn h := by
    have hne : c' ≠ c := by rintro rfl; simp [CSubst.one] at hn
    obtain ⟨h1, h2⟩ := hconst _ _ hne h
    rw [h2.substC_eq, h1]
  defeq {df} h := by
    obtain ⟨h1, h2⟩ := hdefeq _ h
    rw [h2.substC_eq]; exact h1
  val {c' t' ci' Γ ls ls'} hσ hc := by
    have heq : ci.type.substC (CSubst.one c t) = ci.type := hcty.substC_eq
    unfold CSubst.one at hσ; split at hσ
    case isFalse => exact absurd hσ nofun
    case isTrue he =>
    subst he; cases hσ
    rw [h₀] at hc; cases hc
    rw [heq]
    exact hval

/-- **The one-constant, universe-free case.**  The witnesses of
`Theory/Typing/ConstSubstNested.lean` are in this case. -/
theorem CSubst.one_WF {env₀ env₁ : VEnv} {c : Name} {t : VExpr} {ci : VConstant} {U : Nat}
    (henv₁ : env₁.Ordered)
    (hcl : t.ClosedN) (hlt : t.LevelWF 0) (hlty : ci.type.LevelWF 0)
    (h₀ : env₀.constants c = some ci) (hu : ci.uvars = 0)
    (hcty : ci.type.NoCSubst (CSubst.one c t))
    (hty : env₁.HasType 0 [] t ci.type)
    (hconst : ∀ c' ci', c' ≠ c → env₀.constants c' = some ci' →
      env₁.constants c' = some ci' ∧ ci'.type.NoCSubst (CSubst.one c t))
    (hdefeq : ∀ df, env₀.defeqs df → env₁.defeqs df ∧ df.NoCSubst (CSubst.one c t)) :
    (CSubst.one c t).WF env₀ env₁ U :=
  CSubst.one_WF' (U := U) hcl h₀ hcty
    (by
      have heq : ci.type.substC (CSubst.one c t) = ci.type := hcty.substC_eq
      intro Γ ls ls' h1 h2 h3 h4
      have := CSubst.val_zero (σ := CSubst.one c t) (Γ := Γ) henv₁ hu hlt
        (by rw [heq]; exact hlty) (by rw [heq]; exact hty) h1 h2 h3 h4
      rwa [heq] at this)
    hconst hdefeq

end Lean4Lean
