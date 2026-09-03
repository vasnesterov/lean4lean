import Lean4Lean.Theory.Typing.Strengthen
import Lean4Lean.Theory.SetModel.Consts

/-!
# Strengthening, route 1: turn the stripped context entry into an environment axiom

`docs/handoff-weakn.md` §2.3 records two priced, unattempted reformulations of the open
forward direction of `VEnv.IsDefEqU.weakN_iff`.  This file builds the first one.

The idea.  §11–§12 of `Theory/Typing/Strengthen.lean` cut the target down to stripping a
**single** context entry, and §1 closes the case where that entry is *inhabited* by
substitution.  So the whole difficulty is an entry with no inhabitant.  Route 1 buys one:
Π-close the entry over the context below it, declare the closure as a fresh **axiom**, and
apply it to the context's own variables.  Over the enlarged environment the entry *is*
inhabited, §1 fires, and what is left is

    **conservativity of adding one axiom** — and, sharpened by §12 of `Strengthen.lean`, one
    whose type has **no inhabitant at all**.

Contents:

* §1 constants occurring in a term.  `Theory/SetModel/Consts.lean` already has all of this;
  only `ctxConstsIn_of_onCtx` is new.  It is what makes the residual's freshness hypotheses
  **constructible** at the point of use rather than merely stated.
* §2 `VEnv.mkForallCtx` — Π-closure of a term over a context, and its typing.
* §3 `VExpr.appCtx` — the closure applied back to the context's own variables.
* §4 fresh names: an `Ordered` environment declares only finitely many constants, so one can
  always be added.
* §5 the residual `AxiomConservativity`, and the reduction
  `AxiomConservativity → StrengtheningTarget`.
* §6 non-vacuity, the vacuity dual, and the collapse test.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr

/-! ## 1. Which constants a term mentions

**Prior art, found by the duplicate-name check rather than by reading.**  `VExpr.ConstsIn`,
`CtxConstsIn`, `IsDefEq.constsIn` and `Ordered.constsIn` already exist, in
`Theory/SetModel/Consts.lean`, whose own header says they "would be at home in
`Theory/Typing/Lemmas.lean`".  That file imports only `Theory/Typing/Lemmas.lean`, so it can
be imported here with no cycle.  Re-declaring them would have produced two modules that each
compile and cannot be imported together — the collision class `scripts/dup-names.lean` exists
to catch.  Only the one lemma that is genuinely missing is added here. -/

namespace VEnv

variable {env : VEnv} {U : Nat}

variable! (henv : Ordered env) in
/-- A well-formed context mentions only declared constants.  (`Consts.lean` has the
term-level statement but not this one.) -/
theorem ctxConstsIn_of_onCtx : ∀ {Γ : List VExpr},
    OnCtx Γ (env.IsType U) → CtxConstsIn env.contains Γ
  | [], _ => trivial
  | _::_, ⟨h1, _, h2⟩ =>
    have ih := ctxConstsIn_of_onCtx h1
    ⟨ih, (h2.constsIn henv.constsIn ih).1⟩

/-! ## 2. Π-closure of a term over a context -/

end VEnv

/-- `mkForallCtx Γ A`: the term `A`, Π-closed over its context `Γ`.  `Γ`'s head is the
innermost binder, so `mkForallCtx (B :: Γ) A = mkForallCtx Γ (∀ B, A)`. -/
def mkForallCtx : List VExpr → VExpr → VExpr
  | [], A => A
  | B :: Γ, A => mkForallCtx Γ (.forallE B A)

@[simp] theorem mkForallCtx_nil : mkForallCtx [] A = A := rfl
@[simp] theorem mkForallCtx_cons : mkForallCtx (B :: Γ) A = mkForallCtx Γ (.forallE B A) := rfl

namespace VEnv

variable {env : VEnv} {U : Nat}

/-- **The Π-closure of a well-formed context entry is a closed type.**  This is the lemma
`docs/handoff-weakn.md` §2.3 priced as "the whole cost" of route 1. -/
theorem isType_mkForallCtx : ∀ {Γ : List VExpr} {A : VExpr},
    OnCtx Γ (env.IsType U) → env.IsType U Γ A → env.IsType U [] (mkForallCtx Γ A)
  | [], _, _, h => h
  | B :: Γ, A, ⟨hΓ, _, hB⟩, ⟨_, hA⟩ =>
    isType_mkForallCtx (Γ := Γ) (A := .forallE B A) hΓ ⟨_, .forallEDF hB hA⟩

/-! ## 3. The closure applied back to the context's own variables -/

end VEnv

/-- `t.appCtx n`: `t` applied to `.bvar (n-1), …, .bvar 0`, i.e. to the variables of an
`n`-entry context, innermost last. -/
def VExpr.appCtx (t : VExpr) : Nat → VExpr
  | 0 => t
  | n+1 => .app (t.appCtx n).lift (.bvar 0)

namespace VEnv

variable {env : VEnv} {U : Nat}

variable! (henv : Ordered env) in
/-- **A closed inhabitant of the Π-closure gives an inhabitant of the entry itself.** -/
theorem hasType_appCtx {t : VExpr} : ∀ {Γ : List VExpr} {A : VExpr},
    env.HasType U [] t (mkForallCtx Γ A) → env.HasType U Γ (t.appCtx Γ.length) A
  | [], _, h => h
  | B :: Γ, A, h => by
    have ih : env.HasType U Γ (t.appCtx Γ.length) (.forallE B A) := hasType_appCtx h
    have hw := ih.weak (B := B) henv
    have := hw.appDF (A := B.lift) (.bvar .zero)
    rwa [VExpr.instN_bvar0] at this

/-! ## 4. Fresh names: an `Ordered` environment declares only finitely many constants -/

theorem Ordered.consts_finite : ∀ {env : VEnv}, Ordered env →
    ∃ l : List Name, ∀ c, env.contains c → c ∈ l := by
  intro env H
  induction H with
  | empty => exact ⟨[], fun _ ⟨_, h⟩ => nomatch h⟩
  | @const env nm ci env' _ _ h3 ih =>
    obtain ⟨l, hl⟩ := ih
    refine ⟨nm :: l, fun c ⟨ci', hc⟩ => ?_⟩
    rw [VEnv.addConst_constants_eq h3] at hc
    simp only at hc; split at hc
    · subst_vars; exact .head _
    · exact List.mem_cons_of_mem _ (hl _ ⟨_, hc⟩)
  | defeq _ _ ih => exact ih

private theorem le_foldr_max : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.foldr Nat.max 0
  | _::_, _, .head _ => Nat.le_max_left ..
  | _::_, _, .tail _ h => Nat.le_trans (le_foldr_max h) (Nat.le_max_right ..)

private def nameNums (l : List Name) : List Nat :=
  l.filterMap fun n => match n with | .num .anonymous i => some i | _ => none

/-- `Name` is infinite: no list exhausts it. -/
theorem exists_name_not_mem (l : List Name) : ∃ c : Name, c ∉ l := by
  refine ⟨.num .anonymous ((nameNums l).foldr Nat.max 0 + 1), fun h => ?_⟩
  have hmem : ((nameNums l).foldr Nat.max 0 + 1) ∈ nameNums l :=
    List.mem_filterMap.2 ⟨_, h, rfl⟩
  exact Nat.not_succ_le_self _ (le_foldr_max hmem)

/-- **An `Ordered` environment always admits one more axiom.** -/
theorem Ordered.exists_addConst (H : Ordered env) (ci : VConstant) :
    ∃ c env', env.addConst c ci = some env' := by
  obtain ⟨l, hl⟩ := H.consts_finite
  obtain ⟨c, hc⟩ := exists_name_not_mem l
  have : env.constants c = none := by
    cases h : env.constants c with
    | none => rfl
    | some ci' => exact absurd (hl _ ⟨_, h⟩) hc
  obtain ⟨env', h⟩ := VEnv.addConst_eq_none (ci := ci) this
  exact ⟨c, env', h⟩

/-! ## 5. The residual, and the reduction -/

/-- `Ctx.LiftN.exists_instN`, carrying the well-formedness of the stripped entry and of the
context below it.  The substituted term is quantified *inside*, because the smaller context
is `Γ` on the nose (the entries above the strip are lifts, and `inst_liftN` undoes them), so
`Γ₀` and `A₀` do not depend on it — which is what lets the inhabitant be built *from* `Γ₀`.

**No `Ordered env`.**  Until 2026-09-03 this carried `henv : Ordered env` under a
`variable! … in`, and `lake build` had been reporting it unused ("automatically included
section variable(s) unused in theorem") in every build.  The content is purely structural:
`Ctx.LiftN`/`Ctx.InstN` are relations on lists of `VExpr`, the induction only re-associates
the `OnCtx` conjuncts, and `VExpr.inst_liftN` is an identity of substitution.  Nothing
consults `env`'s constants, so the lemma holds at environments where `Ordered env` is
outright **false** — `Theory/Typing/LiftTrimWitness.lean` §1 instantiates it at one. -/
theorem _root_.Lean4Lean.Ctx.LiftN.exists_instN_typed : ∀ {k : Nat} {Γ Γ' : List VExpr},
    Ctx.LiftN 1 k Γ Γ' → OnCtx Γ' (env.IsType U) →
    ∃ Γ₀ A₀, (∀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ) ∧
      OnCtx Γ₀ (env.IsType U) ∧ env.IsType U Γ₀ A₀ := by
  intro k Γ Γ' W
  induction W with
  | @zero Γ As h =>
    match As, h with
    | [A], _ => exact fun hΓ' => ⟨Γ, A, fun _ => .zero, hΓ'.1, hΓ'.2⟩
  | @succ k Γ Γ' A W ih =>
    intro hΓ'
    obtain ⟨Γ₀, A₀, hI, h1, h2⟩ := ih hΓ'.1
    refine ⟨Γ₀, A₀, fun e₀ => ?_, h1, h2⟩
    have := (hI e₀).succ (A := A.liftN 1 k) (e₀ := e₀)
    rwa [VExpr.inst_liftN] at this

/-- **The residual of route 1: conservativity of adding one axiom.**

A judgement over `env` extended by a single fresh, well-formed constant `c`, whose context
and endpoints mention only constants `env` already declares, holds over `env` itself.  The
constant may still occur inside the *derivation* — in `trans`'s middle term, in `beta`'s
argument, in a `defeqDF` type — which is exactly the content. -/
def AxiomConservativity (env : VEnv) (U : Nat) : Prop :=
  ∀ {c : Name} {ci : VConstant} {env' : VEnv} {Γ : List VExpr} {e1 e2 : VExpr},
    env.addConst c ci = some env' → ci.WF env → ci.uvars = U →
    CtxConstsIn env.contains Γ → e1.ConstsIn env.contains → e2.ConstsIn env.contains →
    env'.IsDefEqU U Γ e1 e2 → env.IsDefEqU U Γ e1 e2

/-- **The sharpened residual.**  §12 of `Strengthen.lean` proves that the whole of the target
lives in context entries that are *uninhabited*; `hasType_appCtx` transports that to the
Π-closure, so the axiom this route declares may be assumed to have **no inhabitant at all**
over `env`.  An axiom that provably cannot be instantiated adds no conversions — that is the
crux of `docs/handoff-weakn.md` §2.1, stated over environments instead of contexts.

Adding a hypothesis to a statement in *positive* position weakens it, which is the safe
direction (working rule 3): this is a weaker obligation than `AxiomConservativity`, and
`AxiomConservativity.uninhab` records that. -/
def AxiomConservativityUninhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {c : Name} {ci : VConstant} {env' : VEnv} {Γ : List VExpr} {e1 e2 : VExpr},
    env.addConst c ci = some env' → ci.WF env → ci.uvars = U →
    (∀ t, ¬ env.HasType U [] t ci.type) →
    CtxConstsIn env.contains Γ → e1.ConstsIn env.contains → e2.ConstsIn env.contains →
    env'.IsDefEqU U Γ e1 e2 → env.IsDefEqU U Γ e1 e2

theorem AxiomConservativity.uninhab (H : AxiomConservativity env U) :
    AxiomConservativityUninhab env U :=
  fun h1 h2 h3 _ h5 h6 h7 h8 => H h1 h2 h3 h5 h6 h7 h8

variable! (henv : Ordered env) in
/-- **Route 1, assembled.**  Π-close the stripped entry, declare the closure as a fresh
axiom, apply it to the context's own variables — over the enlarged environment the entry is
inhabited, so `IsDefEqU.strengthen_of_instN` (§1 of `Strengthen.lean`) closes the
strengthening outright.  What is left is exactly `AxiomConservativityUninhab`. -/
theorem AxiomConservativityUninhab.strengthening1Uninhab
    (H : AxiomConservativityUninhab env U) : Strengthening1Uninhab env U := by
  intro k Γ Γ' e1 e2 W hΓ hΓ' hemp h
  obtain ⟨Γ₀, A₀, hI, hΓ₀, hA₀⟩ := W.exists_instN_typed hΓ'
  have hC : env.IsType U [] (mkForallCtx Γ₀ A₀) := isType_mkForallCtx hΓ₀ hA₀
  have hCemp : ∀ t, ¬ env.HasType U [] t (mkForallCtx Γ₀ A₀) :=
    fun t ht => hemp Γ₀ A₀ _ (hI _) (hasType_appCtx henv ht)
  obtain ⟨c, env', hadd⟩ := henv.exists_addConst ⟨U, mkForallCtx Γ₀ A₀⟩
  have hle : env ≤ env' := VEnv.addConst_le hadd
  have henv' : Ordered env' := .const (ci := ⟨U, mkForallCtx Γ₀ A₀⟩) henv hC hadd
  have hcty : env'.constants c = some ⟨U, mkForallCtx Γ₀ A₀⟩ := by
    rw [VEnv.addConst_constants_eq hadd]; simp
  have hlwf : (mkForallCtx Γ₀ A₀).LevelWF U := by
    obtain ⟨_, hC⟩ := hC; exact (IsDefEq.levelWF hC trivial).1
  have hconst : env'.HasType U [] (.const c (VLevel.params U)) (mkForallCtx Γ₀ A₀) := by
    have h := VEnv.IsDefEq.constDF (Γ := []) (uvars := U) (ls := VLevel.params U)
      (ls' := VLevel.params U) hcty VLevel.params_wf VLevel.params_wf
      (by simp) (List.Forall₂.rfl fun _ _ => rfl)
    rw [show (VConstant.mk U (mkForallCtx Γ₀ A₀)).type = mkForallCtx Γ₀ A₀ from rfl,
      hlwf.instL_id] at h
    exact h
  have h₀ := hasType_appCtx (t := .const c (VLevel.params U)) henv' hconst
  obtain ⟨A, hh⟩ := h
  have hΓc : CtxConstsIn env.contains Γ := ctxConstsIn_of_onCtx henv hΓ
  have hcs := hh.constsIn henv.constsIn (ctxConstsIn_of_onCtx henv hΓ')
  exact H hadd hC rfl hCemp hΓc (VExpr.ConstsIn.liftN.1 hcs.1) (VExpr.ConstsIn.liftN.1 hcs.2.1)
    (IsDefEqU.strengthen_of_instN henv' (hI _) h₀ ⟨_, hh.mono hle⟩)

variable! (henv : Ordered env) in
theorem AxiomConservativityUninhab.strengthening1
    (H : AxiomConservativityUninhab env U) : Strengthening1 env U :=
  Strengthening1Uninhab.strengthening1 henv (H.strengthening1Uninhab henv)

variable! (henv : Ordered env) in
theorem AxiomConservativity.strengthening1 (H : AxiomConservativity env U) :
    Strengthening1 env U :=
  AxiomConservativityUninhab.strengthening1 henv H.uninhab

variable! (henv : VEnv.WF env) in
/-- **The reduction.**  The sharpened residual implies the hole's own statement. -/
theorem AxiomConservativityUninhab.target (H : AxiomConservativityUninhab env U) :
    StrengtheningTarget env U :=
  Strengthening1.target henv (H.strengthening1 henv.ordered)

variable! (henv : VEnv.WF env) in
theorem AxiomConservativity.target (H : AxiomConservativity env U) :
    StrengtheningTarget env U :=
  AxiomConservativityUninhab.target henv H.uninhab

/-! ## 6. Non-vacuity, and the collapse test

**Collapse test** (working rule 5).  `AxiomConservativity`'s premises cannot be instantiated
so as to degenerate into `StrengtheningTarget`'s: the residual relates two judgements *in the
same context over two different environments*, the target two judgements *in the same
environment over two different contexts*, and the two environments are always distinct
(`VEnv.addConst_ne`, machine-checked below).  So the reduction is not a repackaging, and in
particular not the tautology that §8 of `Strengthen.lean` turned out to be.

**What the reduction does not show.**  The converse — `StrengtheningTarget →
AxiomConservativity` — is *not* proved here.  The obstacle found by building the route, and
absent from §2.3's sketch in `docs/handoff-weakn.md`, is the **universe-level quantifier**:
`ci.WF env` is `env.IsType ci.uvars [] ci.type`, so a constant whose type mentions the
ambient parameters must be declared with `ci.uvars = U`, and `constDF` then lets a derivation
use `.const c ls` at *every* level list `ls` of length `U`, each inhabiting a *different*
type `ci.type.instL ls`.  One context entry supplies one such instance, so
`AxiomConservativity` is an axiom **scheme** and is a priori *stronger* than the target.

**SUPERSEDED — see `Theory/Typing/ConstVar.lean`.**  The two paragraphs above were written
before the converse was built, and their verdict is now wrong.  `ConstVar.lean` builds the
`const`-to-variable transport and proves

    AxiomConservativityWF env U ↔ StrengtheningTarget env U

where `AxiomConservativityWF` is `AxiomConservativity` **plus `OnCtx Γ`** — a hypothesis every
use of the residual already has, including `strengthening1Uninhab` below.  So the residual is
*not* strictly stronger than the target: it **is** the target.

The universe-scheme argument above is sound but is not an obstruction: the transport puts one
context entry per `≈`-**class** of level list, and `VEnv.IsDefEq.instL_r`
(`Theory/Typing/Strong.lean`) makes that entry serve the whole class.  The "extraction of the
level lists" named above is **not expressible** — a derivation is a `Prop` — and is **not
needed**: the transport's induction produces the list and states its conclusion for every list
covering it.  The only link that remains one-directional is `AxiomConservativity` with an
*arbitrary* context, which the target cannot reach because `Γ ++ Ts` is not a well-formed
context unless `Γ` is.

**Non-vacuity** (working rule 4).  `AxiomConservativity` is fired below at a witness where
the derivation over `env'` genuinely goes through the new constant while both endpoints are
`c`-free — the only shape in which the residual has content.

For the **sharpened** residual `AxiomConservativityUninhab` no witness can be exhibited here,
for the same reason `Strengthening1Uninhab`'s cannot (`Strengthen.lean` §12): showing a
closed type has no inhabitant over a `VEnv.WF` environment is itself open in this tree.  What
*is* available is the vacuity dual, machine-checked as
`strengtheningTarget_of_allClosedInhabited`: if every closed well-formed type were inhabited,
the target would already be proved.  So the sharpened residual is vacuous **iff** the target
holds — and "no witness exhibited" is not evidence either way. -/

variable! (henv : VEnv.WF env) in
/-- **The vacuity dual of the sharpened residual.**  If every closed type over `env` is
inhabited then the target is already closed — by Π-closing each context entry and applying
the inhabitant back to the context's own variables.  This is `Strengthen.lean` §12's
`strengtheningTarget_of_allInhabited` moved from context entries to closed types, which is
where route 1 puts the difficulty. -/
theorem strengtheningTarget_of_allClosedInhabited
    (hinh : ∀ C, env.IsType U [] C → ∃ t, env.HasType U [] t C) : StrengtheningTarget env U := by
  refine strengtheningTarget_of_allInhabited henv fun {k Γ Γ'} W hΓ' => ?_
  obtain ⟨Γ₀, A₀, hI, hΓ₀, hA₀⟩ := W.exists_instN_typed hΓ'
  obtain ⟨t, ht⟩ := hinh _ (isType_mkForallCtx hΓ₀ hA₀)
  exact ⟨Γ₀, A₀, _, hI _, hasType_appCtx henv.ordered ht⟩

/-- The environment really does change: `addConst` succeeds only at an undeclared name, and
then declares it.  This is what stops the collapse test from having anything to collapse. -/
theorem _root_.Lean4Lean.VEnv.addConst_ne {env env' : VEnv} {c ci} (h : env.addConst c ci = some env') :
    env ≠ env' := by
  have h0 : env.constants c = none := by
    unfold VEnv.addConst at h; split at h <;> [exact absurd h nofun; assumption]
  have h1 : env'.constants c = some ci := by
    rw [VEnv.addConst_constants_eq h]; simp
  exact fun e => by rw [e, h1] at h0; exact nomatch h0

/-- **The residual fires non-degenerately.**  Over `VEnv.empty` extended by `c : Prop`, the
two `c`-free endpoints `Sort 0`, `Sort 0` are joined by a `trans` whose middle term `b` is
*not* `c`-free.  So `AxiomConservativity`'s premise is satisfiable at an instance where the
constant really occurs in the derivation. -/
theorem axiomConservativity_fires :
    ∃ (c : Name) (ci : VConstant) (env' : VEnv) (b : VExpr),
      VEnv.empty.addConst c ci = some env' ∧ VConstant.WF .empty ci ∧ ci.uvars = 0 ∧
      env'.IsDefEq 0 [] (.sort .zero) b (.sort (.succ .zero)) ∧
      env'.IsDefEq 0 [] b (.sort .zero) (.sort (.succ .zero)) ∧
      ¬ b.ConstsIn VEnv.empty.contains ∧
      (VExpr.sort .zero).ConstsIn VEnv.empty.contains := by
  obtain ⟨env', hadd⟩ := VEnv.addConst_eq_none (env := .empty) (name := .anonymous)
    (ci := ⟨0, .sort .zero⟩) rfl
  have hcty : env'.constants .anonymous = some ⟨0, .sort .zero⟩ := by
    rw [VEnv.addConst_constants_eq hadd]; simp
  have hc : env'.HasType 0 [] (.const .anonymous []) (.sort .zero) :=
    .constDF hcty nofun nofun rfl .nil
  have hbeta : env'.IsDefEq 0 []
      (.app (.lam (.sort .zero) (.sort .zero)) (.const .anonymous []))
      (.sort .zero) (.sort (.succ .zero)) :=
    .beta (.sortDF (l := .zero) (l' := .zero) trivial trivial rfl) hc
  refine ⟨_, _, env', _, hadd, ⟨_, .sortDF trivial trivial rfl⟩, rfl,
    hbeta.symm, hbeta, fun h => ?_, trivial⟩
  exact absurd h.2 nofun

/-- **The route's own construction fires.**  At `Γ₀ = [Prop]`, `A₀ = Prop`, the Π-closure is
a real `∀` and the inhabitant a real application: `hasType_appCtx` produces
`c (bvar 0) : Prop` in context `[Prop]`. -/
theorem appCtx_fires :
    ∃ (c : Name) (env' : VEnv),
      VEnv.empty.addConst c ⟨0, mkForallCtx [.sort .zero] (.sort .zero)⟩ = some env' ∧
      mkForallCtx [.sort .zero] (VExpr.sort .zero)
        = .forallE (.sort .zero) (.sort .zero) ∧
      (VExpr.const c []).appCtx [VExpr.sort .zero].length
        = .app (.const c []) (.bvar 0) ∧
      env'.HasType 0 [.sort .zero] (.app (.const c []) (.bvar 0)) (.sort .zero) := by
  have hCwf : VConstant.WF .empty ⟨0, mkForallCtx [.sort .zero] (.sort .zero)⟩ :=
    ⟨_, .forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl)⟩
  obtain ⟨env', hadd⟩ := VEnv.addConst_eq_none (env := .empty) (name := .anonymous)
    (ci := ⟨0, mkForallCtx [.sort .zero] (.sort .zero)⟩) rfl
  have hcty : env'.constants .anonymous
      = some ⟨0, mkForallCtx [.sort .zero] (.sort .zero)⟩ := by
    rw [VEnv.addConst_constants_eq hadd]; simp
  have hconst : env'.HasType 0 [] (.const .anonymous [])
      (mkForallCtx [.sort .zero] (.sort .zero)) := .constDF hcty nofun nofun rfl .nil
  exact ⟨_, env', hadd, rfl, rfl,
    hasType_appCtx (.const .empty hCwf hadd) hconst⟩

end VEnv
end Lean4Lean
