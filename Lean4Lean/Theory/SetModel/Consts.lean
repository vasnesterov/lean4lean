import Lean4Lean.Theory.Typing.Lemmas

/-!
# Which constants a term mentions

The `cnst` construction needs one fact that the syntax side did not yet have:
**an earlier declaration's type cannot mention a later declaration's constant.**

Without it the induction over the declaration list cannot take a step. Extending
`cnst` at a fresh name has to leave every already-interpreted term's denotation
alone, and `interp_cnst_congr` reduces that to `ConstsAgree`, which in turn needs
to know that the constants occurring in an earlier type are all already declared.

This is the exact analogue, for constants, of `Ordered.closed` /
`Ordered.closedC` (`Theory/Typing/Lemmas.lean`), which say the same thing for de
Bruijn indices, and it is proved the same way: a predicate on `VExpr`, its
stability under the substitution operations, an induction over `IsDefEq`, and
then `Ordered.induction` to tie the knot.

Nothing here is set-theoretic; it lives under `SetModel/` only because that is
where it is needed and because `Theory/Typing/` is owned elsewhere. It would be
at home in `Theory/Typing/Lemmas.lean` next to `Ordered.closed`.
-/

namespace Lean4Lean

namespace VExpr

/-- `e.ConstsIn P` : every constant occurring in `e` satisfies `P`.

The analogue of `VExpr.ClosedN` for constants rather than bound variables. Note
that the *level arguments* of a constant are ignored — `P` constrains names
only, which is what makes `ConstsIn` invariant under `instL`. -/
def ConstsIn : VExpr → (Name → Prop) → Prop
  | .bvar _, _ => True
  | .sort _, _ => True
  | .const c _, P => P c
  | .app fn arg, P => fn.ConstsIn P ∧ arg.ConstsIn P
  | .lam ty body, P => ty.ConstsIn P ∧ body.ConstsIn P
  | .forallE ty body, P => ty.ConstsIn P ∧ body.ConstsIn P

variable {P Q : Name → Prop}

@[simp] theorem ConstsIn.bvar {i : Nat} : (VExpr.bvar i).ConstsIn P := trivial
@[simp] theorem ConstsIn.sort {u} : (VExpr.sort u).ConstsIn P := trivial
@[simp] theorem ConstsIn.const_iff {c us} : (VExpr.const c us).ConstsIn P ↔ P c := .rfl

theorem ConstsIn.mono (H : ∀ n, P n → Q n) : ∀ {e : VExpr}, e.ConstsIn P → e.ConstsIn Q
  | .bvar _, _ | .sort _, _ => trivial
  | .const .., h => H _ h
  | .app .., ⟨h1, h2⟩ | .lam .., ⟨h1, h2⟩ | .forallE .., ⟨h1, h2⟩ =>
    ⟨h1.mono H, h2.mono H⟩

@[simp] theorem ConstsIn.instL {ls : List VLevel} :
    ∀ {e : VExpr}, (e.instL ls).ConstsIn P ↔ e.ConstsIn P
  | .bvar _ | .sort _ | .const .. => .rfl
  | .app .. | .lam .. | .forallE .. => and_congr instL instL

@[simp] theorem ConstsIn.liftN {n : Nat} :
    ∀ {e : VExpr} {k : Nat}, (e.liftN n k).ConstsIn P ↔ e.ConstsIn P
  | .bvar _, _ | .sort _, _ | .const .., _ => .rfl
  | .app .., _ | .lam .., _ | .forallE .., _ => and_congr liftN liftN

theorem ConstsIn.instVar {i k : Nat} {a : VExpr} (ha : a.ConstsIn P) :
    (VExpr.instVar i a k).ConstsIn P := by
  unfold VExpr.instVar
  split
  · trivial
  · split
    · exact liftN.2 ha
    · trivial

theorem ConstsIn.inst {a : VExpr} (ha : a.ConstsIn P) :
    ∀ {e : VExpr} {k : Nat}, e.ConstsIn P → (e.inst a k).ConstsIn P
  | .bvar _, _, _ => ha.instVar
  | .sort _, _, _ => trivial
  | .const .., _, h => h
  | .app .., _, ⟨h1, h2⟩ | .lam .., _, ⟨h1, h2⟩ | .forallE .., _, ⟨h1, h2⟩ =>
    ⟨ha.inst h1, ha.inst h2⟩

end VExpr

/-- Every type in the context mentions only constants satisfying `P`. -/
def CtxConstsIn (P : Name → Prop) : List VExpr → Prop :=
  (OnCtx · fun _ A => A.ConstsIn P)

theorem VEnv.LE.contains {env env' : VEnv} (h : env ≤ env') {n : Name}
    (hc : env.contains n) : env'.contains n := hc.imp fun _ => h.constants

theorem CtxConstsIn.lookup {P : Name → Prop} {Γ : List VExpr} {n : Nat} {A : VExpr}
    (h : CtxConstsIn P Γ) (hL : Lookup Γ n A) : A.ConstsIn P := by
  induction hL with
  | zero => exact VExpr.ConstsIn.liftN.2 h.2
  | succ _ ih => exact VExpr.ConstsIn.liftN.2 (ih h.1)

namespace VEnv

open VExpr

theorem IsDefEq.constsIn {env : VEnv}
    (henv : OnTypes env fun _ e A => e.ConstsIn env.contains ∧ A.ConstsIn env.contains)
    {U : Nat} {Γ : List VExpr} {e1 e2 A : VExpr} (H : env.IsDefEq U Γ e1 e2 A)
    (hΓ : CtxConstsIn env.contains Γ) :
    e1.ConstsIn env.contains ∧ e2.ConstsIn env.contains ∧ A.ConstsIn env.contains := by
  induction H with
  | bvar h => exact ⟨trivial, trivial, hΓ.lookup h⟩
  | constDF h1 =>
    let ⟨_, h, _⟩ := henv.1 h1
    exact ⟨⟨_, h1⟩, ⟨_, h1⟩, ConstsIn.instL.2 h⟩
  | sortDF => exact ⟨trivial, trivial, trivial⟩
  | symm _ ih => let ⟨h1, h2, h3⟩ := ih hΓ; exact ⟨h2, h1, h3⟩
  | trans _ _ ih1 ih2 => exact ⟨(ih1 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.2⟩
  | appDF _ _ ih1 ih2 =>
    let ⟨hf, hf', _, hB⟩ := ih1 hΓ
    let ⟨ha, ha', _⟩ := ih2 hΓ
    exact ⟨⟨hf, ha⟩, ⟨hf', ha'⟩, ha.inst hB⟩
  | lamDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', hB⟩ := ih2 ⟨hΓ, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, hA, hB⟩
  | forallEDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', _⟩ := ih2 ⟨hΓ, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, trivial⟩
  | defeqDF _ _ ih1 ih2 => exact ⟨(ih2 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.1⟩
  | beta _ _ ih1 ih2 =>
    let ⟨he', _, hA⟩ := ih2 hΓ
    let ⟨he, _, hB⟩ := ih1 ⟨hΓ, hA⟩
    exact ⟨⟨⟨hA, he⟩, he'⟩, he'.inst he, he'.inst hB⟩
  | eta _ ih =>
    let ⟨he, _, hA, hB⟩ := ih hΓ
    exact ⟨⟨hA, ConstsIn.liftN.2 he, trivial⟩, he, hA, hB⟩
  | proofIrrel _ _ _ _ ih2 ih3 =>
    let ⟨hh, _, _⟩ := ih2 hΓ
    let ⟨hh', _, hp⟩ := ih3 hΓ
    exact ⟨hh, hh', hp⟩
  | extra h1 _ _ =>
    let ⟨⟨hl, _⟩, ⟨hr, hA⟩⟩ := henv.2 h1
    exact ⟨ConstsIn.instL.2 hl, ConstsIn.instL.2 hr, ConstsIn.instL.2 hA⟩

/-- The constant-occurrence analogue of `Ordered.closed`: in a well-ordered
environment, every declared type and every defining equation mentions only
constants that are themselves declared. -/
theorem Ordered.constsIn {env : VEnv} (H : Ordered env) :
    env.OnTypes fun _ e A => e.ConstsIn env.contains ∧ A.ConstsIn env.contains :=
  H.induction _
    (fun hle h => ⟨h.1.mono fun _ => hle.contains, h.2.mono fun _ => hle.contains⟩)
    fun _ ih h => (IsDefEq.constsIn ih h trivial).2

/-- **The step lemma for the `cnst` induction.** A declared constant's type
mentions only constants that are already declared, so extending the environment
with a fresh name cannot change that type's denotation. -/
theorem Ordered.constsInC {env : VEnv} {n : Name} {ci : VConstant} (H : Ordered env)
    (h : env.constants n = some ci) : ci.type.ConstsIn env.contains :=
  let ⟨_, h⟩ := H.constsIn.1 h; h.1

/-- **The invariant the constant-assignment induction carries.**  Every declared
type, and every side of every defining equation, mentions only constants that
are themselves declared.

`Ordered` implies it, but `Ordered` is too strong for the *intermediate* stages
of a block: adding an inductive's constructors passes through environments in
which the block's types are declared but its recursors are not, and those are
not `Ordered` on their own.  This weaker invariant is preserved by each
individual `addConst`, which is what the list-extension step needs. -/
def ConstsClosed (env : VEnv) : Prop :=
  (∀ {n : Name} {ci : VConstant}, env.constants n = some ci →
    ci.type.ConstsIn env.contains) ∧
  (∀ {df : VDefEq}, env.defeqs df →
    df.lhs.ConstsIn env.contains ∧ df.rhs.ConstsIn env.contains ∧
      df.type.ConstsIn env.contains)

/-- Adding one fresh constant preserves it, provided the new type mentions only
constants already declared. -/
theorem ConstsClosed.addConst {env env' : VEnv} {n : Name} {ci : VConstant}
    (H : env.ConstsClosed) (hadd : env.addConst n ci = some env')
    (hci : ci.type.ConstsIn env.contains) : env'.ConstsClosed := by
  have hle : env ≤ env' := addConst_le hadd
  have hmono : ∀ {e : VExpr}, e.ConstsIn env.contains → e.ConstsIn env'.contains :=
    fun h ↦ h.mono fun _ ↦ hle.contains
  unfold VEnv.addConst at hadd
  split at hadd
  · exact absurd hadd nofun
  · subst_vars
    cases hadd
    refine ⟨fun {m cm} hm ↦ ?_, fun hd ↦ ?_⟩
    · simp only at hm
      split at hm
      · cases hm; exact hmono hci
      · exact hmono (H.1 hm)
    · exact ⟨hmono (H.2 hd).1, hmono (H.2 hd).2.1, hmono (H.2 hd).2.2⟩

/-- The same, for the two sides and the type of a defining equation. -/
theorem Ordered.constsInD {env : VEnv} {df : VDefEq} (H : Ordered env) (h : env.defeqs df) :
    df.lhs.ConstsIn env.contains ∧ df.rhs.ConstsIn env.contains ∧
      df.type.ConstsIn env.contains :=
  let ⟨h1, h2⟩ := H.constsIn.2 h; ⟨h1.1, h2.1, h2.2⟩

theorem Ordered.constsClosed {env : VEnv} (H : Ordered env) : env.ConstsClosed :=
  ⟨fun h ↦ H.constsInC h, fun h ↦ H.constsInD h⟩

end VEnv

end Lean4Lean
