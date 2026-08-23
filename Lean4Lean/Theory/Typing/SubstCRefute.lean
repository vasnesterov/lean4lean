import Lean4Lean.Theory.Typing.UniqueTypingN

/-!
# `SubstC` is false

`Theory/Typing/UniqueTypingN.lean` carries `VEnv.SubstC` — "`⊢ₙ` conversions are closed under
instantiation by `⊢ₙ`-typed terms" — as an explicit hypothesis, because `unique.tex:51` uses
it without proof and no proof was available.  **It is false.**  This file refutes it at
`n = 1` over the empty environment, so `thm:utype` as stated in `unique.tex` does not follow
from `thm:0dinv` and the reference's own definitions.

## The counterexample

Everything lives in `VEnv.empty` with one universe parameter `p := .param 0`, so there are no
constants and no `defeqs`, and the only conversions available are the structural ones.

    a  := .sort (max p p)              A := .sort (succ p)
    B  := .app (.lam A (.bvar 0)) (.bvar 0)          B' := .bvar 0

* `Γ ⊢₁ a : A` — `a`'s own type is `.sort (succ (max p p))`, and `succ (max p p) ≈ succ p`,
  so one `sortDF` conversion retypes it.  `a` is **not** `⊢₀`-typeable at `A`
  (`a_not_hasType0`): at index `0` conversion *is* syntactic equality, and
  `max p p ≠ p` as `VLevel`s.
* `[A] ⊢₁ B ≡ B'` — one `beta` step, whose two typing premises are `bvar` rules at index `0`.
* Instantiating: `B[a] = .app (.lam A (.bvar 0)) a` and `B'[a] = a`.

`SubstC` would give `[] ⊢₁ .app (.lam A (.bvar 0)) a ≡ a`.  It does not hold.

## Why it does not hold, and why the argument is short

`.app (.lam A (.bvar 0)) a` is not `⊢₀`-typeable **in any context** (`lhs_not_hasType0`),
because typing it needs `a` at the lam's *annotated* domain `A`, and `a`'s unique `⊢₀` type is
`.sort (succ (max p p))`.  That single fact kills every rule at once, which is what makes
`stuck` a fifteen-line induction rather than a confluence argument:

* every rule of `⊢₁` other than `rfl`/`symm`/`trans` and the four structural congruences
  either has the wrong shape, or carries a typing premise **at index 0** about one of its two
  sides — `appDF`, `beta`'s left side, `eta`'s right side, `proofIrrel` — and that premise is
  exactly what fails;
* `beta`'s *right* side is the one case where the term is not a direct premise, and it is
  closed by `Stratified.instN` at `m = 0`: beta's own premises instantiate to a `⊢₀` typing of
  the contractum, and the contractum is our term.

So `.app (.lam A (.bvar 0)) a` is related by `⊢₁` to nothing but itself, while `a` is a
different term.

Note the shape of the failure, since it says what a repair must handle: the obstruction is
**not** repairable by congruence.  `a`'s conversion is available at index `1`
(`.sort (succ (max p p)) ≡ .sort (succ p)`), and if the mismatch appeared only in a *binder
annotation* it could be pushed around by `lamDF`/`forallEDF`, which carry no typing premises —
that is why the first counterexample attempted here, an `eta` pair, was *not* a
counterexample.  Putting the mismatch under an application is what makes it stick: changing
an annotation inside an application requires `appDF`, and `appDF` needs the very `⊢₀` typing
that is missing.

## What this settles, stated narrowly

**Refuted, machine-checked:**

* the inference used at `unique.tex:51` — "`Γ,x:α ⊢ₙ β ≡ β'` and `Γ ⊢ₙ e₂ : α`, so
  `Γ ⊢ₙ β[e₂/x] ≡ β'[e₂/x]`" — at `n = 1` (`substC_false`).  So **the published proof of
  `thm:utype` is invalid**, and with it the induction `DefInv n → uniq n → DefInv (n+1)`:
  `SubstC 0` holds, so the induction reaches `DefInv 1`, and then stops.
* the strengthening of `DefInv`'s clause (2) to its instantiated form
  (`defInv_forallE_inst_false`) — the repair proposed before this refutation existed.  It is
  false for the same reason and by the same instance.

**Not refuted, and not claimed:**

* `thm:utype`'s *statement*.  Its application case has hypotheses this counterexample does not
  supply — a single term carrying both Π types, and an argument typed at both domains — so the
  theorem may still be true by a different argument.  What is gone is the proof.
* `DefInv` itself, in the reference's literal form (`unique.tex:33`, no instantiation).  This
  instance *satisfies* it: the body conversion here is exactly a `forallEDF` premise.
* the case `n = 0`, where `SubstC` is a theorem (`SubstC.zero`) and so `HasTypeN.uniq_zero` is
  unconditional.

**Still standing in `UniqueTypingN.lean`:** `IsDefEqU.sort_inv_of_defInv` and
`IsDefEqU.sort_forallE_inv_of_defInv`, which reduce `Injectivity.lean`'s two open sort goals
to `∀ n, DefInv env U n`.  They use neither `uniq` nor `SubstC`, so they are untouched.  What
the refutation removes is the reference's way of *reaching* `∀ n, DefInv`.
-/

namespace Lean4Lean
namespace VEnv
namespace SubstCRefute

open VExpr

/-- The single universe parameter. -/
def p : VLevel := .param 0

/-- The substituted term.  Its unique `⊢₀` type is `.sort (succ (max p p))`. -/
def a : VExpr := .sort (.max p p)

/-- The type `a` acquires by one `sortDF` conversion, and only by one. -/
def A : VExpr := .sort (.succ p)

/-- `B` instantiated at `a`: the term that is `⊢₁`-related to nothing but itself. -/
def lhs : VExpr := .app (.lam A (.bvar 0)) a

theorem p_wf : p.WF 1 := Nat.lt_succ_self 0

theorem succ_max_equiv : (VLevel.succ (.max p p)) ≈ VLevel.succ p := by
  simp [VLevel.equiv_def, VLevel.eval]

/-! ## `a` is `⊢₁`-typeable at `A`, and not `⊢₀`-typeable at `A` -/

theorem a_hasType1 {Γ : List VExpr} : (∅ : VEnv).HasTypeN 1 1 Γ a A :=
  .conv (.sortDF (by exact ⟨p_wf, p_wf⟩) (by exact p_wf) succ_max_equiv)
    (.sort (by exact ⟨p_wf, p_wf⟩))

theorem a_not_hasType0 {Γ : List VExpr} : ¬ (∅ : VEnv).HasTypeN 1 0 Γ a A := by
  intro H
  have h := IsDefEqN.zero_iff.1 (HasTypeN.sort_inv H).2
  injection h with h; injection h with h; injection h

/-! ## `lhs` is not `⊢₀`-typeable at any type in any context -/

theorem lhs_not_hasType0 {Γ : List VExpr} {T : VExpr} :
    ¬ (∅ : VEnv).HasTypeN 1 0 Γ lhs T := by
  intro H
  have ⟨C, _, hlam, hA, _⟩ := HasTypeN.app_inv H
  have ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hlam
  injection IsDefEqN.zero_iff.1 heq with hAC
  exact a_not_hasType0 (hAC ▸ hA)

/-! ## The two hypotheses of `SubstC` -/

/-- The conversion being instantiated: one `beta` step in context `[A]`. -/
theorem hBB' : (∅ : VEnv).IsDefEqN 1 1 [A]
    (.app (.lam A (.bvar 0)) (.bvar 0)) (.bvar 0) :=
  .beta (.bvar .zero) (.bvar .zero)

/-! ## `lhs` is stuck: `⊢₁` relates it to nothing but itself -/

theorem stuck {Γ X Y m b} (H : Stratified (∅ : VEnv) 1 m Γ X Y b)
    (hm : 1 = m) (hb : false = b) :
    (X = lhs → Y = lhs) ∧ (Y = lhs → X = lhs) := by
  induction H with cases hb
  | rfl => exact ⟨id, id⟩
  | symm _ ih => exact ((ih hm rfl).symm : _ ∧ _)
  | trans _ _ ih1 ih2 =>
    exact ⟨fun h => (ih2 hm rfl).1 ((ih1 hm rfl).1 h),
      fun h => (ih1 hm rfl).2 ((ih2 hm rfl).2 h)⟩
  | sortDF | constDF | lamDF | forallEDF =>
    constructor <;> (intro h; simp [lhs] at h)
  | appDF _ hf hf' _ ha ha' =>
    cases hm
    constructor
    · rintro ⟨⟩
      have ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hf
      injection IsDefEqN.zero_iff.1 heq with hAC
      exact absurd (hAC ▸ ha) a_not_hasType0
    · rintro ⟨⟩
      have ⟨_, _, _, _, heq⟩ := HasTypeN.lam_inv hf'
      injection IsDefEqN.zero_iff.1 heq with hAC
      exact absurd (hAC ▸ ha') a_not_hasType0
  | beta he he' =>
    cases hm
    refine ⟨?_, ?_⟩
    · rintro ⟨⟩; exact absurd he' a_not_hasType0
    · rintro h
      exact absurd (h ▸ Stratified.instN .empty he' .zero he) lhs_not_hasType0
  | eta he =>
    cases hm
    constructor
    · intro h; simp [lhs] at h
    · intro h; exact absurd (h ▸ he) lhs_not_hasType0
  | proofIrrel _ hh hh' =>
    cases hm
    exact ⟨fun h => absurd (h ▸ hh) lhs_not_hasType0,
      fun h => absurd (h ▸ hh') lhs_not_hasType0⟩
  | extra h => exact nomatch h

/-! ## The refutation -/

/-- **`SubstC` is false at `n = 1`.**  Hence `thm:utype` (`unique.tex:40`) does not follow
from the reference's stated hypotheses: its application case needs exactly this. -/
theorem substC_false : ¬ (∅ : VEnv).SubstC 1 1 := by
  intro hs
  have h : (∅ : VEnv).IsDefEqN 1 1 [] lhs a := hs a_hasType1 hBB'
  exact absurd ((stuck h rfl rfl).1 rfl) (by simp [a, lhs])

/-- **The obvious repair is false too.**

An earlier pass proposed strengthening `DefInv`'s clause (2) to conclude the *instantiated*
form — "if `Γ ⊢ₙ ∀x:α.β ≡ ∀x:α'.β'` and `Γ ⊢ₙ a : α` then `Γ ⊢ₙ β[a] ≡ β'[a]`" — which is
exactly what `thm:utype`'s application case consumes, and would have kept `DefInv` as the
single hypothesis.  It is refuted by the same instance, because `forallEDF` carries no typing
premises: the counterexample's body conversion lifts to a Π-conversion for free, and the
strengthened clause then hands back the very judgment `stuck` forbids.

Note precisely what this does **not** refute.  The reference's *literal* clause (2)
(`unique.tex:33`), which concludes `Γ,x:α ⊢ₙ β ≡ β'` with no instantiation, is untouched — it
is the premise of the `forallEDF` step used here, so this instance satisfies it.  `DefInv` as
transcribed in `UniqueTypingN.lean` stands. -/
theorem defInv_forallE_inst_false :
    ¬ ∀ {Γ : List VExpr} {A B A' B' a : VExpr},
        (∅ : VEnv).IsDefEqN 1 1 Γ (.forallE A B) (.forallE A' B') →
        (∅ : VEnv).HasTypeN 1 1 Γ a A →
        (∅ : VEnv).IsDefEqN 1 1 Γ (B.inst a) (B'.inst a) := by
  intro hs
  have hpi : (∅ : VEnv).IsDefEqN 1 1 []
      (.forallE A (.app (.lam A (.bvar 0)) (.bvar 0))) (.forallE A (.bvar 0)) :=
    .forallEDF .rfl hBB'
  have h : (∅ : VEnv).IsDefEqN 1 1 [] lhs a := hs hpi a_hasType1
  exact absurd ((stuck h rfl rfl).1 rfl) (by simp [a, lhs])

/-- The same statement in the form that names the guilty step: instantiation does not
preserve the alternation index, even for the smallest interesting index. -/
theorem inst_does_not_preserve_index :
    ∃ (env : VEnv) (Γ : List VExpr) (A B B' a : VExpr),
      env.HasTypeN 1 1 Γ a A ∧ env.IsDefEqN 1 1 (A :: Γ) B B' ∧
      ¬ env.IsDefEqN 1 1 Γ (B.inst a) (B'.inst a) :=
  ⟨∅, [], A, .app (.lam A (.bvar 0)) (.bvar 0), .bvar 0, a, a_hasType1, hBB', by
    intro h
    have h' : (∅ : VEnv).IsDefEqN 1 1 [] lhs a := h
    exact absurd ((stuck h' rfl rfl).1 rfl) (by simp [a, lhs])⟩

end SubstCRefute
end VEnv
end Lean4Lean
