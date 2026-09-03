import Lean4Lean.Theory.Typing.DescendRefute

/-!
# `NormalEq.descend`'s three `sorry`s, branch by branch

`Theory/Typing/DescendRefute.lean` refutes `ChurchRosser.lean`'s `NormalEq.descend` as a
*whole statement* (`not_descendStatement`, and the unconditional
`descend_uniq_sortUniq_not_all`).  What it leaves as **prose** is the attribution: its header
says "Tracing `descend` on witness A: `cases hne` takes the `appDF` branch, `cases hm` the
`app` branch, the function child's recursive call returns `.inl` … and the argument child's
returns `.inr`".  That trace is a claim about `descend`'s *proof*, not its statement, and
nothing checked it.  It matters, because a successor may reasonably ask "the statement is
false, but is *my* branch the false one?" and spend a round on the two branches the
refutation does not name.

This file answers that mechanically, for all three.  For each of the three `sorry`s it

1. states the branch's goal together with **every hypothesis in scope at the `sorry` except
   the induction hypothesis** (`DescendBranchLocal…`), and
2. refutes that statement at the corresponding witness — i.e. exhibits the branch's own data
   (`Df` at the right eta depth, `Da` at the right eta depth, or `esca`) and shows the
   conclusion still fails.

So **no branch is closable by a local argument**, and each witness is pinned to the branch
that the prose assigned it.

## What is deliberately *not* claimed, and why the statements are shaped this way

The induction hypothesis `IH : ∀ m < N, …` is **omitted** from `DescendBranchLocal…`.  That
makes each statement *stronger* than the actual goal, so refuting it does **not** by itself
refute the goal — it shows only that no argument from the local data closes the branch.  The
omission is not laziness and must not be "fixed": including `IH` would make the statement
**unrefutable by construction**, because a refutation would then have to *supply* `IH`, i.e.
prove `descend` below size `N` at `refParams`, which is a fragment of the statement already
known false.  §3 states the exact residual instead: at each witness the branch goal is
**equivalent to `¬ IH`** (`descendBranch…_iff_not_ih`).  That is the whole truth about the
branch, and it is why these statements are ugly.  *Do not tidy the `IH`-freedom away.*

`hszf`/`hsza` are likewise omitted: both are derived from `hsz` inside `descend`
(`by simp at hsz; omega`), so keeping them would be redundant, not stronger.

## Cones

Every result here is `sorryAx`-free (the two `refEnv.SortUniq 0` / `refEnv.UniqTyping 0`
hypotheses are `not_descendStatement`'s own, carried unchanged and *not* discharged, exactly
as there).  `NormalEq.descend` is **not** in any cone below — the refutation is not circular.
-/

namespace Lean4Lean
open VExpr

/-! ## §0 The induction hypothesis, named

`descend`'s strong recursion supplies exactly this at each branch.  It is quantified over an
arbitrary `q`, `Γ`, `g'`, so it is a restriction of `DescendStatement` to terms of size `< N`
and nothing else. -/

/-- `descend`'s own induction hypothesis at bound `N`, verbatim from the goal state. -/
def DescendIH (I : VEnv.Params) (N : Nat) : Prop :=
  ∀ (m : Nat), m < N → ∀ {g : VExpr}, sizeOf g ≤ m →
    ∀ {Γ : List VExpr} {q : Pattern} {g' : VExpr}
      {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr},
      OnCtx Γ (VEnv.IsType I.env I.univs) → @VEnv.NormalEq I Γ g g' → q.Matches g' n1 n2 →
      @VEnv.DescentOut I Γ q g g' n1 n2

/-- `DescendIH` is a *weakening* of `DescendStatement`, so it is available wherever the latter
is: this is the bound that stops `DescendIH` from being read as an independent assumption. -/
theorem descendIH_of_descendStatement {I : VEnv.Params} {N : Nat}
    (H : DescendStatement I) : DescendIH I N := by
  intro m _ _ hsz _ _ _ _ _ hΓ hne hm
  exact H m hsz hΓ hne hm

/-! ## §1 The three branch statements, `IH` excluded

All three share the goal `DescentOut Γ (q₁.app q₂) (f₁.app a₁) (f₂.app a₂) …` and the data
`l1`-`l6`, `hf`, `ha` of `descend`'s `appDF` × `app` case; they differ only in which of the two
recursive calls returned what. -/

section
variable (I : VEnv.Params)

/-- **Branch 1** (`ChurchRosser.lean:2085`, case `ind.appDF.app.inl.inl.succ`): the *function*
side's descent returned an answer under `kf+1` pending eta layers. -/
def DescendBranchLocalEtaFun : Prop :=
  ∀ {N : Nat} {Γ : List VExpr} {f₁ A₀ B₀ f₂ a₁ a₂ : VExpr}
    {q₁ : Pattern} {m1 : q₁.LPath → List VLevel} {g1 : q₁.Path → VExpr}
    {q₂ : Pattern} {m2 : q₂.LPath → List VLevel} {g2 : q₂.Path → VExpr} {kf ka : Nat},
    OnCtx Γ (VEnv.IsType I.env I.univs) →
    VEnv.HasType I.env I.univs Γ f₁ (.forallE A₀ B₀) →
    VEnv.HasType I.env I.univs Γ f₂ (.forallE A₀ B₀) →
    VEnv.HasType I.env I.univs Γ a₁ A₀ →
    VEnv.HasType I.env I.univs Γ a₂ A₀ →
    @VEnv.NormalEq I Γ f₁ f₂ → @VEnv.NormalEq I Γ a₁ a₂ →
    sizeOf (VExpr.app f₁ a₁) ≤ N →
    q₁.Matches f₂ m1 g1 → q₂.Matches a₂ m2 g2 →
    @VEnv.DescentLam I (kf+1) Γ q₁ f₁ f₂ m1 g1 →
    @VEnv.DescentLam I ka Γ q₂ a₁ a₂ m2 g2 →
    @VEnv.DescentOut I Γ (q₁.app q₂) (f₁.app a₁) (f₂.app a₂)
      (Sum.elim m1 m2) (Sum.elim g1 g2)

/-- **Branch 2** (`ChurchRosser.lean:2090`, case `ind.appDF.app.inl.inl.zero.succ`): the
function side answered at depth `0`, the *argument* side under `ka+1` pending layers. -/
def DescendBranchLocalEtaArg : Prop :=
  ∀ {N : Nat} {Γ : List VExpr} {f₁ A₀ B₀ f₂ a₁ a₂ : VExpr}
    {q₁ : Pattern} {m1 : q₁.LPath → List VLevel} {g1 : q₁.Path → VExpr}
    {q₂ : Pattern} {m2 : q₂.LPath → List VLevel} {g2 : q₂.Path → VExpr} {ka : Nat},
    OnCtx Γ (VEnv.IsType I.env I.univs) →
    VEnv.HasType I.env I.univs Γ f₁ (.forallE A₀ B₀) →
    VEnv.HasType I.env I.univs Γ f₂ (.forallE A₀ B₀) →
    VEnv.HasType I.env I.univs Γ a₁ A₀ →
    VEnv.HasType I.env I.univs Γ a₂ A₀ →
    @VEnv.NormalEq I Γ f₁ f₂ → @VEnv.NormalEq I Γ a₁ a₂ →
    sizeOf (VExpr.app f₁ a₁) ≤ N →
    q₁.Matches f₂ m1 g1 → q₂.Matches a₂ m2 g2 →
    @VEnv.DescentLam I 0 Γ q₁ f₁ f₂ m1 g1 →
    @VEnv.DescentLam I (ka+1) Γ q₂ a₁ a₂ m2 g2 →
    @VEnv.DescentOut I Γ (q₁.app q₂) (f₁.app a₁) (f₂.app a₂)
      (Sum.elim m1 m2) (Sum.elim g1 g2)

/-- **Branch 3** (`ChurchRosser.lean:2105`, case `ind.appDF.app.inl.inr`): the *argument*
side's descent escaped — it is a proof, at no eta depth at all. -/
def DescendBranchLocalProofArg : Prop :=
  ∀ {N : Nat} {Γ : List VExpr} {f₁ A₀ B₀ f₂ a₁ a₂ : VExpr}
    {q₁ : Pattern} {m1 : q₁.LPath → List VLevel} {g1 : q₁.Path → VExpr}
    {q₂ : Pattern} {m2 : q₂.LPath → List VLevel} {g2 : q₂.Path → VExpr} {kf : Nat},
    OnCtx Γ (VEnv.IsType I.env I.univs) →
    VEnv.HasType I.env I.univs Γ f₁ (.forallE A₀ B₀) →
    VEnv.HasType I.env I.univs Γ f₂ (.forallE A₀ B₀) →
    VEnv.HasType I.env I.univs Γ a₁ A₀ →
    VEnv.HasType I.env I.univs Γ a₂ A₀ →
    @VEnv.NormalEq I Γ f₁ f₂ → @VEnv.NormalEq I Γ a₁ a₂ →
    sizeOf (VExpr.app f₁ a₁) ≤ N →
    q₁.Matches f₂ m1 g1 → q₂.Matches a₂ m2 g2 →
    @VEnv.DescentLam I kf Γ q₁ f₁ f₂ m1 g1 →
    (∃ P, VEnv.HasType I.env I.univs Γ P (.sort .zero) ∧
      VEnv.HasType I.env I.univs Γ a₁ P ∧ VEnv.HasType I.env I.univs Γ a₂ P) →
    @VEnv.DescentOut I Γ (q₁.app q₂) (f₁.app a₁) (f₂.app a₂)
      (Sum.elim m1 m2) (Sum.elim g1 g2)

end

/-- **Anti-strawman, branch 1.**  `DescendBranchLocalEtaFun` follows from the full statement,
so it is not stronger than the branch it names.  (The converse — that it is exactly the goal —
is false and deliberately so: the goal also has `IH`.  See §3.) -/
theorem descendBranchLocalEtaFun_of_descendStatement {I : VEnv.Params}
    (H : DescendStatement I) : DescendBranchLocalEtaFun I := by
  intro N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΓ l1 l2 l3 l4 l5 l6 hsz hf ha _ _
  exact H N hsz hΓ (.appDF l1 l2 l3 l4 l5 l6) (.app hf ha)

/-- **Anti-strawman, branch 2.**  See `descendBranchLocalEtaFun_of_descendStatement`. -/
theorem descendBranchLocalEtaArg_of_descendStatement {I : VEnv.Params}
    (H : DescendStatement I) : DescendBranchLocalEtaArg I := by
  intro N _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΓ l1 l2 l3 l4 l5 l6 hsz hf ha _ _
  exact H N hsz hΓ (.appDF l1 l2 l3 l4 l5 l6) (.app hf ha)

/-- **Anti-strawman, branch 3.**  See `descendBranchLocalEtaFun_of_descendStatement`. -/
theorem descendBranchLocalProofArg_of_descendStatement {I : VEnv.Params}
    (H : DescendStatement I) : DescendBranchLocalProofArg I := by
  intro N _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΓ l1 l2 l3 l4 l5 l6 hsz hf ha _ _
  exact H N hsz hΓ (.appDF l1 l2 l3 l4 l5 l6) (.app hf ha)

/-! ## §2 Each branch refuted, at the witness the prose assigned it

The witnesses are `DescendRefute.lean`'s, unchanged.  What is new is the branch data: the
`DescentLam` at the *exact* eta depth that puts `descend` in that branch, and (for branch 3)
the proof escape.  Building them is what turns "tracing `descend` on witness A takes this
branch" from a claim about the source into a checked fact. -/

/-- An answer at eta depth `0` at a bare `const` leaf: nothing reduces, the level list is
empty so both `WF` obligations are vacuous, and `(Pattern.const c).Path` is `Empty` so there
are no arguments to relate.  This is `descend`'s `constDF`/`refl` output, reused as *input*
to the branches below. -/
theorem refDescentLam_zero_const {Γ : List VExpr} {c : Name}
    {n2 : (Pattern.const c).Path → VExpr} :
    @VEnv.DescentLam refParams 0 Γ (.const c) (.const c []) (.const c []) (fun _ => []) n2 := by
  letI := refParams
  refine ⟨_, _, _, .rfl, .const, fun _ => .nil,
    (fun _ _ h => absurd h (by simp)), (fun _ _ h => absurd h (by simp)), ?_⟩
  exact fun x => nomatch x

/-- **Branch 3 is not closable locally**: witness A supplies `Df` at depth `0` on the function
side and the *proof escape* on the argument side — `.bvar 0` and `D` are two proofs of `P` —
and `DescentOut` still fails at the node, because `C (bvar 0)` is `ParRed`-normal
(`refParRedS_G`) and is not itself a proof (`refNotProof`).

The hypotheses are `not_descendStatement`'s, unchanged and **not** discharged. -/
theorem not_descendBranchLocalProofArg
    (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) :
    ¬ DescendBranchLocalProofArg refParams := by
  letI := refParams
  intro H
  exact refNoDescentOut hsu huq
    (H (N := sizeOf refG) (q₁ := .const `C) (q₂ := .const `D) refEnv_hΓ
      refEnv_hasC refEnv_hasC refEnv_hasBvar refEnv_hasD
      (.refl refEnv_hasC) (.proofIrrel refEnv_hasP refEnv_hasBvar refEnv_hasD)
      (Nat.le_refl _) .const .const refDescentLam_zero_const
      ⟨_, refEnv_hasP, refEnv_hasBvar, refEnv_hasD⟩)

/-- Witness B's argument side, at eta depth **1**: `refId` is already a `.lam`, so no reduction
is needed, and under the binder its body `E (bvar 0)` matches the enlarged pattern
`.var (.const E)` with the bound variable in the argument slot — `NormalEq`-related to itself
by `refl`.  This is exactly what puts `descend` in its `ka+1` branch. -/
theorem refDescentLam_one_id {n2 : (Pattern.const `E).Path → VExpr} :
    @VEnv.DescentLam refParams (0+1) refCtx (.const `E) refId (.const `E []) (fun _ => []) n2 := by
  letI := refParams
  refine ⟨.const `P [], .app (.const `E []) (.bvar 0), .const `P [], .rfl, refEnv_hasE,
    _, _, _, .rfl, .var .const, fun _ => .nil,
    (fun _ _ h => absurd h (by simp)), (fun _ _ h => absurd h (by simp)), ?_⟩
  rintro (_|x)
  · exact .refl (VEnv.IsDefEq.bvar .zero)
  · exact nomatch x

/-- **Branch 2 is not closable locally**: witness B supplies `Df` at depth `0` and `Da` at
depth `1`, and `DescentOut` still fails, because `ParRed` has no eta-contraction step so
`F (fun _ => E (bvar 0))` is normal (`refParRedS_G2`).

Hypotheses as in `not_descendBranchLocalProofArg`. -/
theorem not_descendBranchLocalEtaArg
    (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) :
    ¬ DescendBranchLocalEtaArg refParams := by
  letI := refParams
  intro H
  exact refNoDescentOut2 hsu huq
    (H (N := sizeOf refG2) (ka := 0) (q₁ := .const `F) (q₂ := .const `E) refEnv_hΓ
      refEnv_hasF refEnv_hasF refEnv_hasId refEnv_hasE
      (.refl refEnv_hasF) (.etaL refEnv_hasE (.refl refEnv_hasIdBody))
      (Nat.le_refl _) .const .const refDescentLam_zero_const refDescentLam_one_id)

/-- Witness C's *function* side, at eta depth **1**.  `refF3 = fun _ : P => C (bvar 1)` is a
`.lam`, and under the binder its body matches `.var (.const C)` with `bvar 1` in the argument
slot; the answer relates that to the enlarged right-hand side's `bvar 0` by **proof
irrelevance** — both are proofs of `P`.  That mismatch is the whole content of the branch: the
node is a β-redex whose contractum puts the wrong proof in the argument position. -/
theorem refDescentLam_one_F3 {n2 : (Pattern.const `C).Path → VExpr} :
    @VEnv.DescentLam refParams (0+1) refCtx (.const `C) refF3 (.const `C []) (fun _ => []) n2 := by
  letI := refParams
  refine ⟨.const `P [], .app (.const `C []) (.bvar 1), .const `T [], .rfl, refEnv_hasC,
    _, _, _, .rfl, .var .const, fun _ => .nil,
    (fun _ _ h => absurd h (by simp)), (fun _ _ h => absurd h (by simp)), ?_⟩
  rintro (_|x)
  · exact .proofIrrel refEnv_hasP (VEnv.IsDefEq.bvar (.succ .zero)) (VEnv.IsDefEq.bvar .zero)
  · exact nomatch x

/-- **Branch 1 is not closable locally**: witness C supplies `Df` at depth `1` and `Da` at
depth `0`, and `DescentOut` still fails.  The node's only reducts are itself and
`C (bvar 0)` — i.e. witness A again (`refParRedS_G3`) — and neither matches.

Hypotheses as in `not_descendBranchLocalProofArg`. -/
theorem not_descendBranchLocalEtaFun
    (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) :
    ¬ DescendBranchLocalEtaFun refParams := by
  letI := refParams
  intro H
  exact refNoDescentOut3 hsu huq
    (H (N := sizeOf refG3) (kf := 0) (ka := 0) (q₁ := .const `C) (q₂ := .const `D) refEnv_hΓ
      refEnv_hasF3 refEnv_hasC refEnv_hasD refEnv_hasD
      (.etaL refEnv_hasC (.appDF refEnv_hasC refEnv_hasC
        (VEnv.IsDefEq.bvar (.succ .zero)) (VEnv.IsDefEq.bvar .zero) (.refl refEnv_hasC)
        (.proofIrrel refEnv_hasP (VEnv.IsDefEq.bvar (.succ .zero)) (VEnv.IsDefEq.bvar .zero))))
      (.refl refEnv_hasD) (Nat.le_refl _) .const .const
      refDescentLam_one_F3 refDescentLam_zero_const)

/-- **All three at once, unconditionally.**  The two hypotheses are exactly the pair
`descend_uniq_sortUniq_not_all` keeps, so this is that headline refined to branch
granularity: whatever else is true, `descend`'s three open branches cannot *all* be closed
from local data together with unique typing and universe uniqueness — and in fact none of
them can. -/
theorem descendBranchesLocal_uniq_sortUniq_not_all :
    ¬ (DescendBranchLocalEtaFun refParams ∧ refEnv.SortUniq 0 ∧ refEnv.UniqTyping 0) ∧
    ¬ (DescendBranchLocalEtaArg refParams ∧ refEnv.SortUniq 0 ∧ refEnv.UniqTyping 0) ∧
    ¬ (DescendBranchLocalProofArg refParams ∧ refEnv.SortUniq 0 ∧ refEnv.UniqTyping 0) :=
  ⟨fun ⟨h, a, b⟩ => not_descendBranchLocalEtaFun a b h,
   fun ⟨h, a, b⟩ => not_descendBranchLocalEtaArg a b h,
   fun ⟨h, a, b⟩ => not_descendBranchLocalProofArg a b h⟩

/-! ## §3 The exact residual: with `IH` in scope, each branch goal is *equivalent to* `¬ IH`

§2 refutes the branch statements with `IH` removed.  The real `sorry` goals have `IH` in scope,
and the honest accounting of that is below.  It is short because the content is entirely in §2:
the branch's **conclusion** is false at the witness, so the goal `IH → conclusion` reduces to
`¬ IH`.

Read as instructions to a successor: **closing any one of the three `sorry`s at these
instances requires refuting `descend`'s own induction hypothesis.**  That is not a repair —
`DescendIH` is a weakening of `DescendStatement` (`descendIH_of_descendStatement`), so
refuting it *is* refuting the statement again, one size class lower.  There is no third
option, and in particular no hypothesis that can be added: §2 shows the local data is
satisfiable and insufficient, and this section shows the only remaining resource is
self-defeating.

These are stated as `↔`, not as one-directional refutations, deliberately: the point is that
the branch goal has **no content beyond** `¬ IH`, so a successor cannot come back with "but
maybe the goal is provable for a different reason". -/

/-- Branch 3's goal at witness A carries no content beyond `¬ IH`.  See the section note. -/
theorem descendBranchProofArg_iff_not_ih
    (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) {N : Nat} {n1 n2} :
    (DescendIH refParams N → @VEnv.DescentOut refParams refCtx refQ refG refG' n1 n2)
      ↔ ¬ DescendIH refParams N :=
  ⟨fun h hIH => refNoDescentOut hsu huq (h hIH), fun h hIH => absurd hIH h⟩

/-- Branch 2's goal at witness B carries no content beyond `¬ IH`. -/
theorem descendBranchEtaArg_iff_not_ih
    (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) {N : Nat} {n1 n2} :
    (DescendIH refParams N → @VEnv.DescentOut refParams refCtx refQ2 refG2 refG2' n1 n2)
      ↔ ¬ DescendIH refParams N :=
  ⟨fun h hIH => refNoDescentOut2 hsu huq (h hIH), fun h hIH => absurd hIH h⟩

/-- Branch 1's goal at witness C carries no content beyond `¬ IH`. -/
theorem descendBranchEtaFun_iff_not_ih
    (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) {N : Nat} {n1 n2} :
    (DescendIH refParams N → @VEnv.DescentOut refParams refCtx refQ refG3 refG' n1 n2)
      ↔ ¬ DescendIH refParams N :=
  ⟨fun h hIH => refNoDescentOut3 hsu huq (h hIH), fun h hIH => absurd hIH h⟩

/-! ## §4 What this does *not* settle, recorded so nobody re-derives it

* **The two side hypotheses.**  `refEnv.SortUniq 0` and `refEnv.UniqTyping 0` are carried, not
  discharged, exactly as in `DescendRefute.lean`.  Their satisfiability is **open**; see
  `DescendRefute.not_descendStatement_of_wf`'s docstring, which is careful about this and which
  this file does not improve on.  The unconditional headline remains
  `DescendRefute.descend_uniq_sortUniq_not_all`, and its branch-level refinement here is
  `descendBranchesLocal_uniq_sortUniq_not_all`.
* **Whether `descend`'s `.app` case is rescued by restricting `q`.**  It is, by `q.NoApp` —
  `KDescend.lean`'s `NormalEq.descendV`, bounded both ways in `DescendRestate.lean`.  Nothing
  here bears on that; §2's witnesses all use `.app`-headed patterns, which `NoApp` excludes by
  construction (`VEnv.refQ_not_noApp`, `VEnv.refQ2_not_noApp`).
* **Whether the `.app` case is rescued by a `Params` condition on argument positions.**  Not
  investigated here.  `DescendRefute.lean`'s header argues by *analysis* that the natural
  candidate ("no term matching an argument sub-pattern is a proof") is false at any environment
  with a large-eliminating `Prop` inductive, hence vacuous; that argument is not machine-checked
  and building a witness for it needs an environment with a registered ι-rule, which this tree
  does not have with a `Params` instance.  Left open, deliberately, rather than asserted.
-/

end Lean4Lean
