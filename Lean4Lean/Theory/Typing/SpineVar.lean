import Lean4Lean.Theory.Typing.SpineVarClosed
import Lean4Lean.Theory.Typing.KEta

/-!
# `SpineVar`: the variable-headed **spine** entry, and the variable slice of the `.app` row

Round 11 of the `PiDescend` line.  Input: `Theory/Typing/ShapeVar.lean` (the bare-variable entry,
which deleted the `.bvar` row of `PiCodLiftNeutral`) and `docs/handoff-shapevar.md`, whose §9.1
names the next target — the entry `var i as`, covering the **variable slice of the `.app` row** —
and measures **one** missing ingredient for it: a `ClosedN`-of-`spineHead` lemma, so that the
`extra` case of the `IsDefEqStrong` induction closes from `VDefEq.WF`'s empty-context typing
rather than from head shape (`IsDeclRule.lhs_shape` explicitly permits an `.app` left-hand side).

`SpineVarClosed.lean` supplies that ingredient (`VExpr.ClosedN.spineHead`,
`WF.instL_lhs_spineHead_ne_bvar`), hole-free.  This file spends it.

## What is here

* **§1** the expressiveness gap, as theorems: `RigidShapeV` (`ShapeVar.lean`) denotes a variable
  spine **only with an empty argument list** — `RigidShapeV.toExpr_bvar_mkApp_nil` — so a
  variable-headed *application* is still outside the vocabulary.  This is the "old cannot express"
  half of the firing test, machine-checked rather than grepped.
* **§2-§3** `RigidShapeVS` — `RigidShape` with a `varApp i as` entry, which **subsumes**
  `RigidShapeV`'s `var i` (it is `varApp i []`) — and the two collapses
  `RigidShapeVSUniq → RigidShapeVUniq → RigidShapeUniq`, hole-free.
* **§4** the firing test: `SpineVarPiDisj`, "a variable-headed spine is not convertible to a Π",
  reduced to the extended bridge by the thirteen-case `IsDefEqStrong` induction.  Twelve cases
  close outright — `extra` **only** because of `SpineVarClosed.lean` §2 — and the thirteenth is
  `trans`, discharged at the shapes `varApp i as` / `pi A B`, an appeal that cannot be written in
  either `RigidShape` or `RigidShapeV`.
* **§5** uses it: the **variable slice of `PiCodLiftNeutral`'s `.app` row** is deleted, and
  `piDescend_iff_neutralNVS_sortConv` is `piDescend_iff_neutralNV_sortConv` with the type's spine
  head no longer allowed to be a variable at all.
* **§6** the price: `rigidShapeVSUniq_iff` — the extension is `RigidShapeUniq` conjoined with
  **exactly three** spine-disjointness rows and nothing else.
* **§7** anti-vacuity, including **two refutations of my own draft rows**, both at `VEnv.WF`
  environments, both at *non-empty* spines (so neither is a transport of `ShapeVar.lean` §8/§10).
  Continued in `Theory/Typing/SpineVarVacuity.lean` §7.5-§7.12: the non-proof witness this file
  does not have, the consumer-side firing test, the per-row refutation attempts, the machine-checked
  `trans` residual, and the two hard constraints checked at every midpoint.
* **§8** the regression, and **§9** the exact in-place edit, stated and not made.

## What this is NOT

**Not a strength gain, and not a reduction** — the same grading `ShapeVar.lean` carries. §6 is an
`iff`: `RigidShapeVSUniq` *is* the old bridge plus three disjointness rows. So §4 is a
**localisation** of the `.app` row's variable slice into the corner's existing shared node.

**Does the new entry constrain a `trans` midpoint?  No.**  `docs/vacuity-ledger.md` rows 94/94a
and 100-103 make this question mandatory: no syntactic condition on a `trans` midpoint can
localise anything, because β manufactures a midpoint of any shape
(`InjOneFact.midShapeless_vacuous`).  `RigidShapeVS` values occur in `RigidShapeVSUniq` only as
the two **endpoints** `s₁`, `s₂`; the middle term `e` is bound by `∀` with typing premises only
and carries no syntactic condition, byte for byte as in `RigidShapeUniq` and `RigidShapeVUniq`.
`SpineVarPiDisj`, `SpineVarSortDisj` and `SpineVarAppDisj` mention no midpoint at all: they are
`¬ IsDefEqU` statements between two explicit endpoints.  **§5's `PiCodLiftNeutralNVS` is the one
place to look twice**, and it is safe for the same reason `PiCodLiftNeutralNV` is: its new
hypothesis is on `T`, an **endpoint** of the conversion it constrains (the type that is asserted
convertible to a Π), not on a midpoint of any `trans`.  [read off the definitions in §2 and §5;
there is no formal statement of "is not a midpoint restriction".]

## Holes

`spineVarPiDisj_of_rigidShapeVSUniq`, `RigidShapeVSUniq.spineVarSortDisj` and
`.spineVarAppDisj` carry `sorryAx` through **`IsDefEqU.forallE_inv_stratified`** only (via
`IsDefEqStrong`); `piDescend_iff_neutralNVS_sortConv` carries that **and**
`WF.rigidShapeUniqNS`, the same two as the theorems it refines.  `IsDefEqU.weakN_iff` is in **no**
cone here.  Hole-free: all of §1, §2, §3, §5's mechanics, §6's price tag, §7 in full, and the
whole of `SpineVarClosed.lean`.  **Hole-freeness is not the same as discharge**: the extended
bridge is carried as a *hypothesis*, and a hypothesis is not a dependency
(`docs/vacuity-ledger.md` §0, third instrument).
-/

namespace Lean4Lean

/-! ## §0 Spine decomposition, the two-line bridge between `spineHead` and `spine`

`VExpr.spineHead` (`Injectivity.lean:88`) and `VExpr.spine` (`PatternDecode.lean:102`) were
written independently; nothing in the tree relates them.  One `rfl`-induction does. -/

/-- `spine`'s head component *is* `spineHead`. -/
theorem VExpr.spine_fst_eq_spineHead : ∀ e : VExpr, (VExpr.spine e).1 = e.spineHead
  | .app f _ => VExpr.spine_fst_eq_spineHead f
  | .bvar _ | .sort _ | .const .. | .lam .. | .forallE .. => rfl

/-- A spine head is never itself an application — the `spineHead` sibling of
`VExpr.spine_head_not_app` (`PatternDecode.lean:114`), which is about `spine`. -/
theorem VExpr.spineHead_ne_app : ∀ (e f a : VExpr), e.spineHead ≠ .app f a
  | .app g _, f, a => VExpr.spineHead_ne_app g f a
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _
  | .lam .., _, _ | .forallE .., _, _ => nofun

/-- **A term with a variable spine head *is* a variable-headed spine.**  This is what lets a
`spineHead` hypothesis be cashed in for a `RigidShapeVS` shape at the `trans` step. -/
theorem VExpr.eq_bvar_mkApp_of_spineHead {e : VExpr} {i : Nat} (h : e.spineHead = .bvar i) :
    e = (VExpr.bvar i).mkApp (VExpr.spine e).2 := by
  have hm := VExpr.mkApp_spine e
  rw [VExpr.spine_fst_eq_spineHead, h] at hm
  exact hm.symm

namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 The gap, as theorems rather than greps

`ShapeVar.lean` §1 proves the old vocabularies cannot denote a **bare** variable.  That is now
fixed, so the question for this round is different and sharper: `RigidShapeV` *can* denote
`.bvar i`; can it denote `.app (.bvar i) x`?  No — and the proof is the arity, not the head. -/

/-- **`RigidShapeV` denotes a variable spine only when the spine is empty.**  `spineHead` cannot
see the difference between `.bvar i` and `.app (.bvar i) x` — both have head `.bvar i` — so this
is proved by `appArity`, which can. -/
theorem RigidShapeV.toExpr_bvar_mkApp_nil (s : RigidShapeV) {i : Nat} {as : List VExpr}
    (h : s.toExpr = (VExpr.bvar i).mkApp as) : as = [] := by
  cases s with
  | sort u =>
    exact absurd ((VExpr.spineHead_mkApp as (.bvar i) ▸ congrArg VExpr.spineHead h).symm) nofun
  | pi A B =>
    exact absurd ((VExpr.spineHead_mkApp as (.bvar i) ▸ congrArg VExpr.spineHead h).symm) nofun
  | app c ls as' =>
    refine absurd ?_ (nofun : ¬ (VExpr.const c ls = VExpr.bvar i))
    have hs := congrArg VExpr.spineHead h
    rwa [RigidShapeV.toExpr, VExpr.spineHead_mkApp, VExpr.spineHead_mkApp] at hs
  | var j =>
    have ha := congrArg VExpr.appArity h
    rw [RigidShapeV.toExpr_var, VExpr.appArity_mkApp] at ha
    exact List.eq_nil_of_length_eq_zero (by simpa [VExpr.appArity] using ha.symm)

/-- **So a variable-headed *application* is outside `RigidShapeV`'s vocabulary** — the
"cannot express" half of the firing test. -/
theorem RigidShapeV.toExpr_ne_bvar_app (s : RigidShapeV) (i : Nat) (a : VExpr)
    (as : List VExpr) : s.toExpr ≠ (VExpr.bvar i).mkApp (a :: as) :=
  fun h => absurd (s.toExpr_bvar_mkApp_nil h) nofun

/-- …and a fortiori outside `RigidShape`'s (`Injectivity.lean:918`). -/
theorem RigidShape.toExpr_ne_bvar_app (s : RigidShape) (i : Nat) (a : VExpr)
    (as : List VExpr) : s.toExpr ≠ (VExpr.bvar i).mkApp (a :: as) := by
  rw [← RigidShape.toExpr_toV]; exact s.toV.toExpr_ne_bvar_app i a as

/-! ## §2 The extended vocabulary -/

/-- `RigidShape` with a **variable-headed spine** entry.  `varApp i []` is `RigidShapeV.var i`,
so this vocabulary subsumes that one (§3). -/
inductive RigidShapeVS where
  | sort (u : VLevel)
  | pi (A B : VExpr)
  | app (c : Lean.Name) (ls : List VLevel) (as : List VExpr)
  | varApp (i : Nat) (as : List VExpr)

/-- The term a shape denotes. -/
def RigidShapeVS.toExpr : RigidShapeVS → VExpr
  | .sort u => .sort u
  | .pi A B => .forallE A B
  | .app c ls as => (VExpr.const c ls).mkApp as
  | .varApp i as => (VExpr.bvar i).mkApp as

@[simp] theorem RigidShapeVS.toExpr_varApp {i : Nat} {as : List VExpr} :
    (RigidShapeVS.varApp i as).toExpr = (VExpr.bvar i).mkApp as := rfl

@[simp] theorem RigidShapeVS.spineHead_toExpr_varApp {i : Nat} {as : List VExpr} :
    (RigidShapeVS.varApp i as).toExpr.spineHead = .bvar i := VExpr.spineHead_mkApp as _

/-- The side condition.  The variable-spine entry carries **none**: no rule rewrites a
variable-headed spine (`WF.instL_lhs_spineHead_ne_bvar`, `SpineVarClosed.lean` §2), so there is no
`RuleFreeHead` analogue to ask for.  Note this is *not* free the way `RigidShapeV.var`'s was: for
a bare variable it follows from `IsDeclRule.lhs_shape`, for a spine it needs scope. -/
def RigidShapeVS.RuleFree (env : VEnv) : RigidShapeVS → Prop
  | .sort _ => True
  | .pi _ _ => True
  | .app c _ _ => env.RuleFreeHead c
  | .varApp _ _ => True

/-- **What two shapes in one conversion class have in common.**  The variable-spine **diagonal is
`True`**, and §7.2 refutes the naive `i = j` reading *at a non-empty spine*, over `VEnv.empty`:
two variable spines with **different heads** are convertible there. -/
def RigidShapeVS.Compat (env : VEnv) (U : Nat) (Γ : List VExpr) :
    RigidShapeVS → RigidShapeVS → Prop
  | .sort u, .sort v => u ≈ v
  | .pi A B, .pi A' B' =>
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧ env.IsDefEq U (A'::Γ) B B' (.sort u)
  | .app c ls as, .app c' ls' as' =>
    c = c' → List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as'
  | .varApp _ _, .varApp _ _ => True
  | _, _ => False

/-- The two shapes are both sorts. -/
def RigidShapeVS.BothSort : RigidShapeVS → RigidShapeVS → Prop
  | .sort _, .sort _ => True
  | _, _ => False

/-- **The extended bridge.**  Identical to `RigidShapeUniq` / `RigidShapeVUniq` except that
`s₁`, `s₂` range over `RigidShapeVS`.  The middle term `e` is untouched. -/
def RigidShapeVSUniq (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T : VExpr} {s₁ s₂ : RigidShapeVS},
    OnCtx Γ (env.IsType U) → ¬ env.IsProof U Γ e →
    s₁.RuleFree env → s₂.RuleFree env →
    env.IsDefEq U Γ e s₁.toExpr T → env.IsDefEq U Γ e s₂.toExpr T →
    s₁.Compat env U Γ s₂

/-- `RigidShapeVSUniq` minus its `sort`/`sort` entry. -/
def RigidShapeVSUniqNS (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T : VExpr} {s₁ s₂ : RigidShapeVS},
    OnCtx Γ (env.IsType U) → ¬ env.IsProof U Γ e →
    s₁.RuleFree env → s₂.RuleFree env → ¬ s₁.BothSort s₂ →
    env.IsDefEq U Γ e s₁.toExpr T → env.IsDefEq U Γ e s₂.toExpr T →
    s₁.Compat env U Γ s₂

/-! ## §3 The collapse: nothing either older vocabulary said is lost or changed -/

/-- The embedding of `ShapeVar.lean`'s vocabulary: `var i` is the empty spine. -/
def RigidShapeV.toVS : RigidShapeV → RigidShapeVS
  | .sort u => .sort u
  | .pi A B => .pi A B
  | .app c ls as => .app c ls as
  | .var i => .varApp i []

@[simp] theorem RigidShapeV.toExpr_toVS (s : RigidShapeV) : s.toVS.toExpr = s.toExpr := by
  cases s <;> rfl

@[simp] theorem RigidShapeV.ruleFree_toVS (s : RigidShapeV) :
    s.toVS.RuleFree env ↔ s.RuleFree env := by
  cases s <;> exact Iff.rfl

@[simp] theorem RigidShapeV.compat_toVS {Γ : List VExpr} (s₁ s₂ : RigidShapeV) :
    s₁.toVS.Compat env U Γ s₂.toVS ↔ s₁.Compat env U Γ s₂ := by
  cases s₁ <;> cases s₂ <;> exact Iff.rfl

@[simp] theorem RigidShapeV.bothSort_toVS (s₁ s₂ : RigidShapeV) :
    s₁.toVS.BothSort s₂.toVS ↔ s₁.BothSort s₂ := by
  cases s₁ <;> cases s₂ <;> exact Iff.rfl

/-- **The extension is at least as strong as `ShapeVar.lean`'s.** -/
theorem RigidShapeVSUniq.rigidShapeVUniq (H : RigidShapeVSUniq env U) : RigidShapeVUniq env U := by
  intro Γ e T s₁ s₂ hΓ hnp hr₁ hr₂ h₁ h₂
  have h₁' : env.IsDefEq U Γ e s₁.toVS.toExpr T := by rw [RigidShapeV.toExpr_toVS]; exact h₁
  have h₂' : env.IsDefEq U Γ e s₂.toVS.toExpr T := by rw [RigidShapeV.toExpr_toVS]; exact h₂
  exact (RigidShapeV.compat_toVS s₁ s₂).1
    (H hΓ hnp ((RigidShapeV.ruleFree_toVS s₁).2 hr₁) ((RigidShapeV.ruleFree_toVS s₂).2 hr₂) h₁' h₂')

@[inherit_doc RigidShapeVSUniq.rigidShapeVUniq]
theorem RigidShapeVSUniqNS.rigidShapeVUniqNS (H : RigidShapeVSUniqNS env U) :
    RigidShapeVUniqNS env U := by
  intro Γ e T s₁ s₂ hΓ hnp hr₁ hr₂ hbs h₁ h₂
  have h₁' : env.IsDefEq U Γ e s₁.toVS.toExpr T := by rw [RigidShapeV.toExpr_toVS]; exact h₁
  have h₂' : env.IsDefEq U Γ e s₂.toVS.toExpr T := by rw [RigidShapeV.toExpr_toVS]; exact h₂
  exact (RigidShapeV.compat_toVS s₁ s₂).1
    (H hΓ hnp ((RigidShapeV.ruleFree_toVS s₁).2 hr₁) ((RigidShapeV.ruleFree_toVS s₂).2 hr₂)
      (fun h => hbs ((RigidShapeV.bothSort_toVS s₁ s₂).1 h)) h₁' h₂')

/-- …and hence as strong as the original. -/
theorem RigidShapeVSUniq.rigidShapeUniq (H : RigidShapeVSUniq env U) : RigidShapeUniq env U :=
  RigidShapeVUniq.rigidShapeUniq H.rigidShapeVUniq

@[inherit_doc RigidShapeVSUniq.rigidShapeUniq]
theorem RigidShapeVSUniqNS.rigidShapeUniqNS (H : RigidShapeVSUniqNS env U) :
    RigidShapeUniqNS env U :=
  RigidShapeVUniqNS.rigidShapeUniqNS H.rigidShapeVUniqNS


/-! ## §4 The firing test: the variable slice of the `.app` row, stated and reduced

`PiDescendFstCod.lean` §7 records that a variable-headed type versus a Π is "a disjointness fact
for which the injectivity corner's machinery has no slot at all".  `ShapeVar.lean` §5 built the
slot for a **bare** variable; §1 above proves the slot for a variable-headed **application** is
still missing.  Here it is, and the same thirteen-case `IsDefEqStrong` induction closes twelve
cases outright.

The one case that is genuinely new is **`extra`**.  For a bare variable it closes from
`IsDeclRule.lhs_shape` alone (`ShapeVar.lean` §4).  For a spine it cannot — `lhs_shape` permits
`df.lhs = .app f a` — and it closes instead from **scope**: a rule's sides are typed in the empty
context, so they are closed, so their spine heads are closed, so no spine head of a rule side is a
variable (`SpineVarClosed.lean`).  That is the single ingredient `docs/handoff-shapevar.md` §9.1
measured as missing, and it is the whole cost of this entry. -/

/-- **A variable-headed spine is not convertible to a Π.**  Stated on `spineHead` rather than on
an explicit `mkApp`, because that is the form the consumer (§5) has: it splits on the head
constructor of a type, and `spineHead` is what survives lifting (`VExpr.spineHead_liftN`). -/
def SpineVarPiDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr} {i : Nat}, OnCtx Γ (env.IsType U) →
    e.spineHead = .bvar i → ¬ env.IsDefEqU U Γ e (.forallE A B)

/-- **The firing test.**  Twelve of thirteen `IsDefEqStrong` cases close outright; the thirteenth
is `trans`, discharged at the shapes `varApp i as` / `pi A B`, whose `RigidShapeVS.Compat` entry is
`False` — an appeal that cannot be written in `RigidShape` (`RigidShape.toExpr_ne_bvar_app`) or in
`RigidShapeV` (`RigidShapeV.toExpr_ne_bvar_app`).

Case by case: `extra` by `WF.instL_lhs_spineHead_ne_bvar` (the new ingredient) and
`WF.instL_lhs_ne_forallE`; `proofIrrel` by `forallE_not_proof`, so the statement pays no
hypothesis for it — **this is why the row needs no `¬ IsProof` guard where `SpineVarAppDisj` (§6)
does**; `forallEDF` and `beta`/`eta` on the *spine head* of their left endpoint (`.forallE`, `.lam`
and `.lam` respectively — note `beta`'s left endpoint **is** an `.app`, so head-constructor
reasoning would not have closed it and `spineHead` is doing real work); `bvar`, `sortDF`,
`constDF`, `appDF`, `lamDF` on the Π side; `symm`/`defeqDF` bookkeeping. -/
theorem spineVarPiDisj_of_rigidShapeVSUniq (henv : VEnv.WF env) (H : RigidShapeVSUniq env U) :
    SpineVarPiDisj env U := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      OnCtx Γ (env.IsType U) → ∀ (i : Nat) (A B : VExpr),
        (e₁.spineHead = .bvar i ∧ e₂ = .forallE A B) ∨
        (e₂.spineHead = .bvar i ∧ e₁ = .forallE A B) → False := by
    intro Γ e₁ e₂ T HH
    induction HH with
    | symm _ ih => exact fun hΓ' i A B h => ih hΓ' i A B h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans hd1 hd2 ih1 ih2 =>
      rintro hΓ' i A B (⟨hsh, rfl⟩ | ⟨hsh, rfl⟩)
      · rw [VExpr.eq_bvar_mkApp_of_spineHead hsh] at hd1
        exact H (s₁ := .varApp i _) (s₂ := .pi A B) hΓ'
          (not_isProof_of_defeqU_forallE henv hΓ' ⟨_, hd2.defeq⟩) trivial trivial
          hd1.defeq.symm hd2.defeq
      · rw [VExpr.eq_bvar_mkApp_of_spineHead hsh] at hd2
        exact H (s₁ := .pi A B) (s₂ := .varApp i _) hΓ'
          (not_isProof_of_defeqU_forallE henv hΓ' ⟨_, hd1.defeq.symm⟩) trivial trivial
          hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 h3 _ _ _ =>
      rintro hΓ' i A B (⟨-, rfl⟩ | ⟨-, rfl⟩)
      · exact forallE_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h3.defeq.hasType.1
      · exact forallE_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h2.defeq.hasType.1
    | extra h1 =>
      rintro _ i A B (⟨he, -⟩ | ⟨-, hf⟩)
      · exact henv.instL_lhs_spineHead_ne_bvar h1 _ _ he
      · exact henv.instL_lhs_ne_forallE h1 _ _ _ hf
    | bvar _ _ _ | sortDF _ _ _ | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _
    | lamDF _ _ _ _ _ _ _ =>
      rintro _ i A B (⟨-, hf⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
    | forallEDF _ _ _ _ _ =>
      rintro _ i A B (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact absurd hf nofun
    | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      rintro _ i A B (⟨hf, -⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
  intro Γ e A B i hΓ hsh hc
  obtain ⟨_, hd⟩ := hc
  exact aux (hd.strong henv.ordered hΓ) hΓ i A B (.inl ⟨hsh, rfl⟩)

/-- **What a refutation of the row would cost, as a theorem.**  Before proving a shape row this
corner asks you to try to refute it (`docs/vacuity-ledger.md` §0, and `ShapeVar.lean` §8/§10, where
two draft rows fell).  I could not refute this one, and the contrapositive of the firing test says
what a refutation would buy: a `VEnv.WF` environment with a variable-headed spine convertible to a
Π **refutes the extended bridge**, hence (by §6) refutes `RigidShapeUniq` itself or one of its
three spine rows — i.e. it would be a refutation of the injectivity corner's *shared* node, not of
my entry.  That is the honest status of "I tried to refute it and failed".

Why the two mechanisms that killed `ShapeVar.lean`'s draft rows cannot fire here: proof
irrelevance needs the Π side to be a proof, and it is not (`forallE_not_proof`); and δ needs a
rule with a variable-headed spine on one side, and there is none (`SpineVarClosed.lean` §2). -/
theorem not_rigidShapeVSUniq_of_not_spineVarPiDisj (henv : VEnv.WF env)
    (h : ¬ SpineVarPiDisj env U) : ¬ RigidShapeVSUniq env U :=
  fun H => h (spineVarPiDisj_of_rigidShapeVSUniq henv H)

/-! ## §5 …and it deletes the variable slice of `PiCodLiftNeutral`'s `.app` row

`ShapeVar.lean` §6 deleted the `.bvar` row of `PiCodLiftNeutral` by a six-way case split on the
head constructor of `T`.  With the spine entry no case split is needed at all: the guard is a
condition on `T.spineHead`, and it covers the `.bvar` row **and** the variable slice of the `.app`
row in one clause.  `VExpr.spineHead_liftN` (`KEta.lean:101`) is what makes the lift transparent. -/

/-- **The variable-spine row of `PiCodLiftNeutral` is closed** — the analogue of
`codLift_const_ruleFree` (`PiDescendFstCod.lean` §7) and `codLift_bvar_absurd`
(`ShapeVar.lean` §6) for the slice neither covered. -/
theorem codLift_spineVar_absurd (H : SpineVarPiDisj env U) {Γ' : List VExpr}
    (hΓ' : OnCtx Γ' (env.IsType U)) {T S B : VExpr} {i n k : Nat}
    (hsh : T.spineHead = .bvar i)
    (hconv : env.IsDefEqU U Γ' (T.liftN n k) (.forallE (S.liftN n k) B)) : False := by
  refine H hΓ' (i := liftVar n i k) ?_ hconv
  rw [VExpr.spineHead_liftN, hsh, liftN_bvar_eq]

/-- **`PiCodLiftNeutral` with every variable-headed type deleted** — not just the bare-variable
ones.  Compare `PiCodLiftNeutralNV` (`ShapeVar.lean` §6), whose guard is `∀ i, T ≠ .bvar i`; this
guard is on the **spine head**, so it also removes the variable slice of the `.app` row. -/
def PiCodLiftNeutralNVS (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {f a T S B : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) → T.PiDescendNeutral →
    (∀ i, T.spineHead ≠ .bvar i) →
    env.HasType U Γ f T → env.HasType U Γ a S →
    env.IsDefEqU U Γ' (T.liftN n k) (.forallE (S.liftN n k) B) →
    ∃ B₀ : VExpr, env.IsDefEqU U (S.liftN n k :: Γ') B (B₀.liftN n (k+1))

/-- The slice deletion, as a reduction.  Note there is **no case split on `T`**: the guard is
about `T.spineHead`, so the two rows are removed by one `by_cases`. -/
theorem PiCodLiftNeutral.of_noSpineVar (H : SpineVarPiDisj env U) (h : PiCodLiftNeutralNVS env U) :
    PiCodLiftNeutral env U := by
  intro n k Γ Γ' f a T S B W hΓ hΓ' hne hfT haS hconv
  by_cases hsv : ∃ i, T.spineHead = .bvar i
  · obtain ⟨i, hi⟩ := hsv
    exact (codLift_spineVar_absurd H hΓ' hi hconv).elim
  · exact h W hΓ hΓ' hne (fun i hi => hsv ⟨i, hi⟩) hfT haS hconv

/-- The converse half, free: deleting rows only weakens. -/
theorem PiCodLiftNeutral.toNVS (h : PiCodLiftNeutral env U) : PiCodLiftNeutralNVS env U :=
  fun W hΓ hΓ' hne _ hfT haS hconv => h W hΓ hΓ' hne hfT haS hconv

/-- **The new residual is weaker than `ShapeVar.lean`'s**, and by construction rather than by
appeal: the spine-head guard implies the bare-variable guard. -/
theorem PiCodLiftNeutralNV.toNVS (h : PiCodLiftNeutralNV env U) : PiCodLiftNeutralNVS env U := by
  intro n k Γ Γ' f a T S B W hΓ hΓ' hne hsv hfT haS hconv
  exact h W hΓ hΓ' hne (fun i hi => hsv i (by rw [hi]; rfl)) hfT haS hconv

variable! (henv : VEnv.WF env) in
/-- **`PiDescend`'s residual with the whole variable slice gone.**  Compare
`piDescend_iff_neutralNV_sortConv` (`ShapeVar.lean` §6) and
`piDescend_iff_neutral_sortConv` (`PiDescendFstCod.lean` §6): the same equivalence, with the
type's spine head no longer allowed to be a variable at all, at the price of `SpineVarPiDisj` —
which §4 reduces to the extended bridge. -/
theorem piDescend_iff_neutralNVS_sortConv (H : SpineVarPiDisj env U) :
    PiDescend env U ↔ PiCodLiftNeutralNVS env U ∧ SortConvStrengthening env U := by
  refine ⟨fun HP => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · obtain ⟨hn, hs⟩ := (piDescend_iff_neutral_sortConv henv).1 HP
    exact ⟨hn.toNVS, hs⟩
  · exact (piDescend_iff_neutral_sortConv henv).2 ⟨PiCodLiftNeutral.of_noSpineVar H h1, h2⟩

/-- **What is left of the `.app` row**, named precisely.  After `codLift_const_ruleFree`
(`PiDescendFstCod.lean` §7) removes the rule-free constant spines and §5 removes the variable
spines, a type surviving `PiCodLiftNeutralNVS` and headed by an `.app` has a spine head that is a
`.lam` (a β-redex type), a `.sort`, a `.forallE`, or a `.const` **carrying a δ-rule**.  Stated as
an exhaustive disjunction so the remaining slice is on the record rather than in prose; the
`.sort`/`.forallE` cases are very likely unreachable by typing and the `.lam` case is a genuine
residual. -/
theorem spineHead_cases_of_noSpineVar {T : VExpr} (hsv : ∀ i, T.spineHead ≠ .bvar i) :
    (∃ u, T.spineHead = .sort u) ∨ (∃ c ls, T.spineHead = .const c ls) ∨
    (∃ A b, T.spineHead = .lam A b) ∨ ∃ A B, T.spineHead = .forallE A B := by
  rcases h : T.spineHead with i | u | ⟨c, ls⟩ | ⟨f, a⟩ | ⟨A, b⟩ | ⟨A, B⟩
  · exact absurd h (hsv i)
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inl ⟨_, _, rfl⟩)
  · exact absurd h (VExpr.spineHead_ne_app T f a)
  · exact .inr (.inr (.inl ⟨_, _, rfl⟩))
  · exact .inr (.inr (.inr ⟨_, _, rfl⟩))

/-! ## §6 The price tag: the extension is the old bridge plus exactly three spine rows

`ShapeVar.lean` §7 measures its entry as `RigidShapeUniq` conjoined with three bare-variable
disjointness rows.  This is that measurement for the spine entry, and the answer is the same
shape: **no new `trans`-level demand, no new side condition, and the variable-spine diagonal costs
nothing at all** (it is `True`, and §7.2 refutes the naive `i = j` reading at a non-empty spine).

The variable-spine rows differ from the bare-variable rows in exactly one place, and it is worth
recording because it is the one thing the `ClosedN`-of-`spineHead` lemma bought beyond stating the
entry: the **`extra`** case of the `app` row closes from *both* sides' closedness
(`WF.instL_lhs_spineHead_ne_bvar` and `WF.instL_rhs_spineHead_ne_bvar`), where
`ShapeVar.lean`'s `RigidShapeVUniq.varAppDisj` had to appeal to `RuleFreeHead` for the right-hand
side.  So `RuleFreeHead` is now needed only at `trans`, i.e. only to invoke the bridge. -/

/-- The variable-spine / sort row. -/
def SpineVarSortDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e : VExpr} {u : VLevel} {i : Nat}, OnCtx Γ (env.IsType U) →
    e.spineHead = .bvar i → ¬ env.IsDefEqU U Γ e (.sort u)

/-- The variable-spine / constant-spine row, guarded by `RuleFreeHead` **and by `¬ IsProof`**.
The second guard is not prudence: §7.3 refutes the unguarded form at a `VEnv.WF` environment *and
at a non-empty spine*, so it is not merely inherited from `ShapeVar.lean` §10. -/
def SpineVarAppDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e : VExpr} {i : Nat} {c : Lean.Name} {ls : List VLevel} {as : List VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c → ¬ env.IsProof U Γ e →
    e.spineHead = .bvar i → ¬ env.IsDefEqU U Γ e ((VExpr.const c ls).mkApp as)

/-- **Bounded above.**  The extended bridge follows from the old one plus the three rows. -/
theorem rigidShapeVSUniq_of_family (htr : env.ProofTransport U) (hold : env.RigidShapeUniq U)
    (hvp : SpineVarPiDisj env U) (hvs : SpineVarSortDisj env U) (hva : SpineVarAppDisj env U) :
    env.RigidShapeVSUniq U := by
  intro Γ e T s₁ s₂ hΓ hnp hr₁ hr₂ h₁ h₂
  have hs : env.IsDefEqU U Γ s₁.toExpr s₂.toExpr := ⟨T, h₁.symm.trans h₂⟩
  cases s₁ with
  | varApp i as =>
    cases s₂ with
    | varApp j as' => trivial
    | sort u => exact hvs hΓ RigidShapeVS.spineHead_toExpr_varApp hs
    | pi A B => exact hvp hΓ RigidShapeVS.spineHead_toExpr_varApp hs
    | app c ls as' =>
      exact hva hΓ hr₂ (fun hp => hnp (htr hΓ ⟨_, h₁.symm⟩ hp))
        RigidShapeVS.spineHead_toExpr_varApp hs
  | sort u =>
    cases s₂ with
    | varApp j as' => exact hvs hΓ RigidShapeVS.spineHead_toExpr_varApp hs.symm
    | sort v => exact hold (s₁ := .sort u) (s₂ := .sort v) hΓ hnp hr₁ hr₂ h₁ h₂
    | pi A B => exact hold (s₁ := .sort u) (s₂ := .pi A B) hΓ hnp hr₁ hr₂ h₁ h₂
    | app c ls as' => exact hold (s₁ := .sort u) (s₂ := .app c ls as') hΓ hnp hr₁ hr₂ h₁ h₂
  | pi A B =>
    cases s₂ with
    | varApp j as' => exact hvp hΓ RigidShapeVS.spineHead_toExpr_varApp hs.symm
    | sort v => exact hold (s₁ := .pi A B) (s₂ := .sort v) hΓ hnp hr₁ hr₂ h₁ h₂
    | pi A' B' => exact hold (s₁ := .pi A B) (s₂ := .pi A' B') hΓ hnp hr₁ hr₂ h₁ h₂
    | app c ls as' => exact hold (s₁ := .pi A B) (s₂ := .app c ls as') hΓ hnp hr₁ hr₂ h₁ h₂
  | app c ls as =>
    cases s₂ with
    | varApp j as' =>
      exact hva hΓ hr₁ (fun hp => hnp (htr hΓ ⟨_, h₂.symm⟩ hp))
        RigidShapeVS.spineHead_toExpr_varApp hs.symm
    | sort v => exact hold (s₁ := .app c ls as) (s₂ := .sort v) hΓ hnp hr₁ hr₂ h₁ h₂
    | pi A B => exact hold (s₁ := .app c ls as) (s₂ := .pi A B) hΓ hnp hr₁ hr₂ h₁ h₂
    | app c' ls' as' =>
      exact hold (s₁ := .app c ls as) (s₂ := .app c' ls' as') hΓ hnp hr₁ hr₂ h₁ h₂

/-- The sort row comes out of the extended bridge — the same induction as §4 with
`sort_not_proof` in place of `forallE_not_proof`. -/
theorem RigidShapeVSUniq.spineVarSortDisj (henv : VEnv.WF env) (H : RigidShapeVSUniq env U) :
    SpineVarSortDisj env U := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      OnCtx Γ (env.IsType U) → ∀ (i : Nat) (u : VLevel),
        (e₁.spineHead = .bvar i ∧ e₂ = .sort u) ∨ (e₂.spineHead = .bvar i ∧ e₁ = .sort u) →
        False := by
    intro Γ e₁ e₂ T HH
    induction HH with
    | symm _ ih => exact fun hΓ' i u h => ih hΓ' i u h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans hd1 hd2 ih1 ih2 =>
      rintro hΓ' i u (⟨hsh, rfl⟩ | ⟨hsh, rfl⟩)
      · rw [VExpr.eq_bvar_mkApp_of_spineHead hsh] at hd1
        exact H (s₁ := .varApp i _) (s₂ := .sort u) hΓ'
          (not_isProof_of_defeqU_sort henv hΓ' ⟨_, hd2.defeq⟩) trivial trivial
          hd1.defeq.symm hd2.defeq
      · rw [VExpr.eq_bvar_mkApp_of_spineHead hsh] at hd2
        exact H (s₁ := .sort u) (s₂ := .varApp i _) hΓ'
          (not_isProof_of_defeqU_sort henv hΓ' ⟨_, hd1.defeq.symm⟩) trivial trivial
          hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 h3 _ _ _ =>
      rintro hΓ' i u (⟨-, rfl⟩ | ⟨-, rfl⟩)
      · exact sort_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h3.defeq.hasType.1
      · exact sort_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h2.defeq.hasType.1
    | extra h1 =>
      rintro _ i u (⟨he, -⟩ | ⟨-, hf⟩)
      · exact henv.instL_lhs_spineHead_ne_bvar h1 _ _ he
      · exact henv.instL_lhs_ne_sort h1 _ _ hf
    | bvar _ _ _ | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _
    | lamDF _ _ _ _ _ _ _ | forallEDF _ _ _ _ _ =>
      rintro _ i u (⟨-, hf⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
    | sortDF _ _ _ =>
      rintro _ i u (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact absurd hf nofun
    | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      rintro _ i u (⟨hf, -⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
  intro Γ e u i hΓ hsh hc
  obtain ⟨_, hd⟩ := hc
  exact aux (hd.strong henv.ordered hΓ) hΓ i u (.inl ⟨hsh, rfl⟩)

/-- **The constant-spine row comes out of the extended bridge too**, so §6 is an equivalence.

This is the one induction here that is *harder* than `ShapeVar.lean`'s counterpart rather than
easier, and for the reason `const_app_inv` records: at `appDF` **both** endpoints are `.app`s, so
neither the Π side nor the sort side is available to close the case, and the only route is to peel
one argument off each spine (`VExpr.mkApp_app_inv`) and recurse — which means threading
`¬ IsProof` down the spine (`IsProof.app'`).  `ShapeVar.lean`'s `varAppDisj` escaped this because
its variable endpoint was **bare**, so `appDF` was vacuous on it.  A variable-headed spine is not,
and that is the honest extra cost of this row. -/
theorem RigidShapeVSUniq.spineVarAppDisj (henv : VEnv.WF env) (H : RigidShapeVSUniq env U) :
    SpineVarAppDisj env U := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      OnCtx Γ (env.IsType U) → ∀ (i : Nat) (c : Lean.Name) (ls : List VLevel) (as : List VExpr),
        env.RuleFreeHead c →
        (e₁.spineHead = .bvar i ∧ ¬ env.IsProof U Γ e₁ ∧
            e₂ = (VExpr.const c ls).mkApp as) ∨
        (e₂.spineHead = .bvar i ∧ ¬ env.IsProof U Γ e₂ ∧
            e₁ = (VExpr.const c ls).mkApp as) → False := by
    intro Γ e₁ e₂ T HH
    induction HH with
    | symm _ ih => exact fun hΓ' i c ls as hrf h => ih hΓ' i c ls as hrf h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans hd1 hd2 ih1 ih2 =>
      rintro hΓ' i c ls as hrf (⟨hsh, hnp, rfl⟩ | ⟨hsh, hnp, rfl⟩)
      · rw [VExpr.eq_bvar_mkApp_of_spineHead hsh] at hd1 hnp
        exact H (s₁ := .varApp i _) (s₂ := .app c ls as) hΓ'
          (fun hp => hnp (hp.defeqU henv hΓ' ⟨_, hd1.defeq.symm⟩)) trivial hrf
          hd1.defeq.symm hd2.defeq
      · rw [VExpr.eq_bvar_mkApp_of_spineHead hsh] at hd2 hnp
        exact H (s₁ := .app c ls as) (s₂ := .varApp i _) hΓ'
          (fun hp => hnp (hp.defeqU henv hΓ' ⟨_, hd2.defeq⟩)) hrf trivial
          hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 h3 _ _ _ =>
      rintro hΓ' i c ls as hrf (⟨-, hnp, -⟩ | ⟨-, hnp, -⟩)
      · exact hnp ⟨_, h1.defeq.hasType.1, h2.defeq.hasType.1⟩
      · exact hnp ⟨_, h1.defeq.hasType.1, h3.defeq.hasType.1⟩
    | extra h1 =>
      rintro _ i c ls as _ (⟨he, -, -⟩ | ⟨he, -, -⟩)
      · exact henv.instL_lhs_spineHead_ne_bvar h1 _ _ he
      · exact henv.instL_rhs_spineHead_ne_bvar h1 _ _ he
    | appDF _ _ hA hB hf ha _ _ _ ihf =>
      rintro hΓ' i c ls as hrf (⟨hsh, hnp, he⟩ | ⟨hsh, hnp, he⟩)
      · rcases VExpr.mkApp_app_inv as _ he.symm with ⟨-, hbad⟩ | ⟨bs, rfl, hb⟩
        · exact absurd hbad nofun
        refine ihf hΓ' i c ls bs hrf (.inl ⟨hsh, ?_, hb.symm⟩)
        exact fun hp => hnp (hp.app' henv hΓ' hA.defeq.hasType.1 hB.defeq.hasType.1
          hf.defeq.hasType.1 ha.defeq.hasType.1)
      · rcases VExpr.mkApp_app_inv as _ he.symm with ⟨-, hbad⟩ | ⟨bs, rfl, hb⟩
        · exact absurd hbad nofun
        refine ihf hΓ' i c ls bs hrf (.inr ⟨hsh, ?_, hb.symm⟩)
        exact fun hp => hnp (hp.app' henv hΓ' hA.defeq.hasType.1 hB.defeq.hasType.1
          hf.defeq.hasType.2 ha.defeq.hasType.2)
    | bvar _ _ _ =>
      rintro _ i c ls as _ (⟨-, -, he⟩ | ⟨-, -, he⟩) <;>
        (have hs := congrArg VExpr.spineHead he
         rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun)
    | sortDF _ _ _ | constDF _ _ _ _ _ _ _ _
    | lamDF _ _ _ _ _ _ _ | forallEDF _ _ _ _ _ =>
      rintro _ i c ls as _ (⟨hf, -, -⟩ | ⟨hf, -, -⟩) <;> exact absurd hf nofun
    | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      rintro _ i c ls as _ (⟨hf, -, -⟩ | ⟨-, -, he⟩)
      · exact absurd hf nofun
      · have hs := congrArg VExpr.spineHead he
        rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun
  intro Γ e i c ls as hΓ hrf hnp hsh hc
  obtain ⟨_, hd⟩ := hc
  exact aux (hd.strong henv.ordered hΓ) hΓ i c ls as hrf (.inl ⟨hsh, hnp, rfl⟩)

/-- **The exact price, both ways.**  `RigidShapeVSUniq` is `RigidShapeUniq` plus exactly the three
variable-spine rows — no more, no less.  So this file buys **vocabulary**, not strength, and §4 is
a *localisation* of the `.app` row's variable slice, not a discharge of it. -/
theorem rigidShapeVSUniq_iff (henv : VEnv.WF env) (htr : env.ProofTransport U) :
    env.RigidShapeVSUniq U ↔
      env.RigidShapeUniq U ∧ SpineVarPiDisj env U ∧ SpineVarSortDisj env U ∧
        SpineVarAppDisj env U :=
  ⟨fun H => ⟨H.rigidShapeUniq, spineVarPiDisj_of_rigidShapeVSUniq henv H,
      H.spineVarSortDisj henv, H.spineVarAppDisj henv⟩,
   fun ⟨h1, h2, h3, h4⟩ => rigidShapeVSUniq_of_family htr h1 h2 h3 h4⟩

/-! ## §7 Anti-vacuity, in the order `docs/vacuity-ledger.md` §0 asks for them

**Four checks here, eight more in `SpineVarVacuity.lean`.**  §7.1 is the degenerate instance;
§7.2 the reachability of the slice §5 deletes, which is also the **firing test for the row
deletion**; §7.3 and §7.4 are two refutations of my own draft rows, both at `VEnv.WF`
environments and both at **non-empty** spines, so neither is a transport of `ShapeVar.lean`
§8/§10.

`Theory/Typing/SpineVarVacuity.lean` (§7.5-§7.12) carries the rest, and two of its checks correct
or sharpen what is claimed here: §7.5 supplies the witness this section lacks — a non-empty
variable spine that is **not** a proof, without which the `¬ IsProof` guard would exclude the whole
slice this entry adds and the entry would be a rename; §7.9 upgrades §7.3's and §7.4's
one-midpoint checks to *every* midpoint; and §7.10 replaces the read-off answer to the
midpoint question with an exhibited β-redex midpoint. -/

/-! ### §7.1 The degenerate instance

`SpineVarPiDisj` is a *negation*, so the degenerate risk is triviality, not emptiness — and at
`Γ = []` it is a **theorem**, at every `Ordered` environment, by the scope invariant
`IsDefEq.closedN` composed with `SpineVarClosed.lean` §1.  So all of its content lives at
non-empty contexts, and §7.2's witness is deliberately at a context of length three. -/
theorem spineVarPiDisj_nil (henv : Ordered env) {e A B : VExpr} {i : Nat}
    (hsh : e.spineHead = .bvar i) : ¬ env.IsDefEqU U [] e (.forallE A B) := by
  rintro ⟨T, h⟩
  exact VExpr.spineHead_ne_bvar_of_closed (h.closedN henv trivial) hsh

/-- The sort-side sibling of `spineVarPiDisj_nil`, same proof. -/
theorem spineVarSortDisj_nil (henv : Ordered env) {e : VExpr} {u : VLevel} {i : Nat}
    (hsh : e.spineHead = .bvar i) : ¬ env.IsDefEqU U [] e (.sort u) := by
  rintro ⟨T, h⟩
  exact VExpr.spineHead_ne_bvar_of_closed (h.closedN henv trivial) hsh

/-! ### §7.2 The deleted slice is reachable, and the deletion is proper

`Prop → Prop` in a context, applied to a proposition: the type `.app (.bvar 2) (.bvar 1)` is an
**application with a variable spine head**.  It is `PiDescendNeutral`, it is a type, something
inhabits it, and — the point — it satisfies `PiCodLiftNeutralNV`'s guard `∀ i, T ≠ .bvar i`
(`ShapeVar.lean` §6 does **not** delete it) while failing `PiCodLiftNeutralNVS`'s.  So §5 deletes a
slice with live instances on its type side, and it deletes something the previous round did not.

Over `VEnv.empty`, which is `VEnv.WF` by `⟨[], .empty⟩` — no axiom is declared anywhere in this
section, so nothing here rests on an inconsistent witness environment. -/

/-- `Prop → Prop`, closed. -/
def propFn : VExpr := .forallE (.sort .zero) (.sort .zero)

theorem propFn_lift : propFn.lift = propFn := rfl

theorem propFn_type {Γ : List VExpr} :
    env.HasType U Γ propFn (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallEDF (.sortDF trivial trivial rfl) (.sortDF trivial trivial rfl)

/-- `[f a, a, f]` read innermost-first: `f : Prop → Prop`, `a : Prop`, and an inhabitant of the
**variable-headed application** `f a`. -/
def spCtx : List VExpr := [.app (.bvar 1) (.bvar 0), .sort .zero, propFn]

theorem spCtx_onCtx : OnCtx spCtx ((∅ : VEnv).IsType 0) :=
  ⟨⟨⟨trivial, _, propFn_type⟩, _, .sort trivial⟩, _,
    HasType.app (.bvar (.succ (Lookup.zero' propFn_lift))) (.bvar (Lookup.zero' rfl))⟩

/-- **The variable slice of the `.app` row is reachable**, and `ShapeVar.lean`'s guard does not
reach it.  Seven conjuncts, all machine-checked:
`VEnv.empty` is `WF`; the context is `OnCtx`; `T = .app (.bvar 2) (.bvar 1)` is a type; `.bvar 0`
inhabits it; it is `PiDescendNeutral`; **it is not a `.bvar`**, so `PiCodLiftNeutralNV`'s guard
admits it; and its **spine head is a variable**, so `PiCodLiftNeutralNVS`'s guard rejects it. -/
theorem spineVar_row_reachable :
    (∅ : VEnv).WF ∧ OnCtx spCtx ((∅ : VEnv).IsType 0) ∧
      (∅ : VEnv).IsType 0 spCtx (.app (.bvar 2) (.bvar 1)) ∧
      (∅ : VEnv).HasType 0 spCtx (.bvar 0) (.app (.bvar 2) (.bvar 1)) ∧
      (VExpr.app (.bvar 2) (.bvar 1)).PiDescendNeutral ∧
      (∀ i, VExpr.app (.bvar 2) (.bvar 1) ≠ .bvar i) ∧
      (VExpr.app (.bvar 2) (.bvar 1)).spineHead = .bvar 2 :=
  ⟨⟨[], .empty⟩, spCtx_onCtx,
   ⟨_, HasType.app (.bvar (.succ (.succ (Lookup.zero' propFn_lift))))
      (.bvar (.succ (Lookup.zero' rfl)))⟩,
   .bvar (Lookup.zero' rfl), trivial, nofun, rfl⟩

/-- …and **neither old vocabulary can denote it**: this is §1 instantiated at the witness, which
is what makes §4 a firing test rather than a rename. -/
theorem spineVar_row_unexpressible :
    (∀ s : RigidShape, s.toExpr ≠ .app (VExpr.bvar 2) (.bvar 1)) ∧
    (∀ s : RigidShapeV, s.toExpr ≠ .app (VExpr.bvar 2) (.bvar 1)) ∧
    (RigidShapeVS.varApp 2 [.bvar 1]).toExpr = .app (VExpr.bvar 2) (.bvar 1) :=
  ⟨fun s => s.toExpr_ne_bvar_app 2 (.bvar 1) [], fun s => s.toExpr_ne_bvar_app 2 (.bvar 1) [],
   rfl⟩

/-! ### §7.3 The naive spine diagonal is FALSE at a non-empty spine

`ShapeVar.lean` §8 refutes the *bare*-variable diagonal `i = j` by proof irrelevance in a
three-entry context.  That refutation transports to `varApp i [] / varApp j []` for free, which
would leave open whether a **non-empty** spine could be told apart by its head.  It cannot: with
two distinct inhabitants of `∀ X : Prop, X` in scope, the spines `F P` and `G P` are both proofs of
`P`, so proof irrelevance identifies two variable-headed applications with **different heads**.

Over `VEnv.empty` again, so `VEnv.WF` holds and no axiom is involved. -/

/-- `[G, F, P]` innermost-first: `P : Prop`, then two inhabitants of `∀ X : Prop, X`. -/
def spDiagCtx : List VExpr := [svFalse, svFalse, .sort .zero]

theorem spDiagCtx_onCtx : OnCtx spDiagCtx ((∅ : VEnv).IsType 0) :=
  ⟨⟨⟨trivial, _, .sort trivial⟩, _, svFalse_type⟩, _, svFalse_type⟩

theorem spDiagCtx_prop : (∅ : VEnv).HasType 0 spDiagCtx (.bvar 2) (.sort .zero) :=
  .bvar (.succ (.succ (Lookup.zero' rfl)))

/-- `F P : P`, where `F = .bvar 1`. -/
theorem spDiagCtx_F : (∅ : VEnv).HasType 0 spDiagCtx (.app (.bvar 1) (.bvar 2)) (.bvar 2) :=
  HasType.app (.bvar (.succ (Lookup.zero' svFalse_lift))) spDiagCtx_prop

/-- `G P : P`, where `G = .bvar 0`. -/
theorem spDiagCtx_G : (∅ : VEnv).HasType 0 spDiagCtx (.app (.bvar 0) (.bvar 2)) (.bvar 2) :=
  HasType.app (.bvar (Lookup.zero' svFalse_lift)) spDiagCtx_prop

/-- **Two variable-headed spines with different heads are convertible**, at a `VEnv.WF`
environment. -/
theorem spDiagCtx_conv : (∅ : VEnv).IsDefEqU 0 spDiagCtx
    (.app (.bvar 1) (.bvar 2)) (.app (.bvar 0) (.bvar 2)) :=
  ⟨_, .proofIrrel spDiagCtx_prop spDiagCtx_F spDiagCtx_G⟩

/-- The naive variable-spine no-confusion row: heads agree. -/
def SpineVarNoConf (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ : VExpr} {i j : Nat}, OnCtx Γ (env.IsType U) →
    e₁.spineHead = .bvar i → e₂.spineHead = .bvar j → env.IsDefEqU U Γ e₁ e₂ → i = j

/-- **Refuted**, and at a spine of length one, so this is not `ShapeVar.lean` §8 transported. -/
theorem spineVarNoConf_false : ¬ SpineVarNoConf (∅ : VEnv) 0 :=
  fun h => absurd (h spDiagCtx_onCtx (i := 1) (j := 0) rfl rfl spDiagCtx_conv) nofun

/-- …and **the control is a control**: the row this file declares is `True` at the witness, and
the bridge's own `¬ IsProof` premise fails there, so nothing here refutes `RigidShapeVSUniq`. -/
theorem spDiagCtx_compat :
    RigidShapeVS.Compat (∅ : VEnv) 0 spDiagCtx (.varApp 1 [.bvar 2]) (.varApp 0 [.bvar 2]) :=
  trivial

@[inherit_doc spDiagCtx_compat]
theorem spDiagCtx_isProof : (∅ : VEnv).IsProof 0 spDiagCtx (.app (.bvar 1) (.bvar 2)) :=
  ⟨_, spDiagCtx_prop, spDiagCtx_F⟩

/-! ### §7.4 The variable-spine / constant-spine row is FALSE unguarded, at a non-empty spine

`ShapeVar.lean` §10 refutes the *bare*-variable version over `svEnv` (`VEnv.empty` plus one
axiom `svC : ∀ X : Prop, X`, no rules, `VEnv.WF` by `wf_svEnv`).  Again that transports to the
empty spine for free; the question this round has to answer is whether a non-empty spine escapes,
and it does not.  In the context `[F, P]` the spine `F P` and the spine `svC P` are both proofs of
`P`, and proof irrelevance identifies them — with a **length-one** spine on both sides.

Read in two halves, as `ForallInvPrice`'s control has to be: it **refutes** the unguarded row, and
it is **silent** on what §6 declares, because the bridge's `¬ IsProof` premise fails at the
witness (`spAppCtx_isProof`).  The witness **is** `VEnv.WF`, so no `not_wf_…` half exists or is
needed — that is what makes this a hard constraint on the vocabulary rather than a control. -/

/-- `[F, P]` innermost-first: `P : Prop`, `F : ∀ X : Prop, X`. -/
def spAppCtx : List VExpr := [svFalse, .sort .zero]

theorem spAppCtx_onCtx : OnCtx spAppCtx (svEnv.IsType 0) :=
  ⟨⟨trivial, _, .sort trivial⟩, _, svFalse_type⟩

theorem spAppCtx_prop : svEnv.HasType 0 spAppCtx (.bvar 1) (.sort .zero) :=
  .bvar (.succ (Lookup.zero' rfl))

theorem spAppCtx_var : svEnv.HasType 0 spAppCtx (.app (.bvar 0) (.bvar 1)) (.bvar 1) :=
  HasType.app (.bvar (Lookup.zero' svFalse_lift)) spAppCtx_prop

/-- `svC` typed in `spAppCtx` rather than in `[svFalse]` — `svEnv_const` is stated at the shorter
context, and `VDefEq`-free constant typing does not depend on the context, but the *statement*
does, so it is restated here. -/
theorem spAppCtx_svC : svEnv.HasType 0 spAppCtx (.const svC []) svFalse :=
  .constDF svEnv_constants (ls := []) nofun nofun rfl .nil

theorem spAppCtx_const :
    svEnv.HasType 0 spAppCtx ((VExpr.const svC []).mkApp [.bvar 1]) (.bvar 1) :=
  HasType.app spAppCtx_svC spAppCtx_prop

/-- **A variable-headed spine and a rule-free constant spine are convertible**, at a `VEnv.WF`
environment, both spines of length one. -/
theorem spAppCtx_conv : svEnv.IsDefEqU 0 spAppCtx
    (.app (.bvar 0) (.bvar 1)) ((VExpr.const svC []).mkApp [.bvar 1]) :=
  ⟨_, .proofIrrel spAppCtx_prop spAppCtx_var spAppCtx_const⟩

/-- `SpineVarAppDisj` with the `¬ IsProof` premise deleted. -/
def SpineVarAppDisjNaive (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e : VExpr} {i : Nat} {c : Lean.Name} {ls : List VLevel} {as : List VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
    e.spineHead = .bvar i → ¬ env.IsDefEqU U Γ e ((VExpr.const c ls).mkApp as)

/-- **Refuted**, at a length-one spine. -/
theorem spineVarAppDisjNaive_false : ¬ SpineVarAppDisjNaive svEnv 0 :=
  fun h => h spAppCtx_onCtx (ruleFreeHead_svEnv svC) (i := 0) rfl spAppCtx_conv

/-- The control's second half: the guard the row carries excludes the witness. -/
theorem spAppCtx_isProof : svEnv.IsProof 0 spAppCtx (.app (.bvar 0) (.bvar 1)) :=
  ⟨_, spAppCtx_prop, spAppCtx_var⟩

/-- …and neither refutation touches the **Π** or **sort** rows: the right endpoint of each witness
is an application, not a Π and not a sort.  Stated so it is on the record. -/
theorem spineVar_witnesses_right_not_pi_nor_sort (A B : VExpr) (u : VLevel) :
    ((VExpr.const svC []).mkApp [.bvar 1] ≠ .forallE A B) ∧
    ((VExpr.const svC []).mkApp [.bvar 1] ≠ .sort u) ∧
    (VExpr.app (.bvar 0) (.bvar 2) ≠ .forallE A B) :=
  ⟨nofun, nofun, nofun⟩

/-! ## §8 Regression: existing consumers come out identical

Nothing in the tree was edited, so existing results are unchanged by construction.  These
re-derive two consumers *through* the new vocabulary; because the collapse (§3) is hole-free,
composing with it cannot change an axiom set, which is the point. -/

/-- `rigidShapeUniq_of_sortUniq`, through the spine vocabulary. -/
theorem RigidShapeVSUniqNS.rigidShapeUniq' (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (h : env.RigidShapeVSUniqNS U) : env.RigidShapeUniq U :=
  rigidShapeUniq_of_sortUniq henv hsu h.rigidShapeUniqNS

/-- `RigidShapeUniqNS.piUniq`, through the spine vocabulary. -/
theorem RigidShapeVSUniqNS.piUniq (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (h : env.RigidShapeVSUniqNS U) : env.RigidPiUniq U :=
  RigidShapeUniqNS.piUniq henv hsu h.rigidShapeUniqNS

end VEnv

/-! ## §9 The in-place edit, stated and NOT made

`docs/handoff-shapevar.md` §7 measured the ripple of putting a variable entry into
`RigidShape` itself: **86** declarations mention `RigidShape`, **9** hand-written ones eliminate it.
The spine entry's ripple is the same 9 declarations plus `ShapeVar.lean`'s own `RigidShapeV`
eliminators, and it is deliberately not made here.  The edit, if it is ever sequenced, is:

1. `inductive RigidShape` (`Injectivity.lean:918`) — add `| varApp (i : Nat) (as : List VExpr)`;
   this **replaces** `ShapeVar.lean`'s proposed `| var (i : Nat)`, since `varApp i []` is that.
2. `RigidShape.toExpr` — add `| .varApp i as => (VExpr.bvar i).mkApp as`.
3. `RigidShape.RuleFree` — add `| .varApp _ _ => True`.  **No** side condition, and the reason is
   `SpineVarClosed.lean` §2, whose natural home is next to `WF.instL_lhs_ne_sort` /
   `instL_lhs_ne_forallE` in `DeclRules.lean:234,240`.
4. `RigidShape.Compat` — nine explicit rows become sixteen: `varApp/varApp => True` (§7.3 forbids
   `i = j`) and the six off-diagonal rows `False`; or restructure with a `| _, _ => False`
   catch-all, as `RigidShapeVS.Compat` does.
5. `RigidShape.BothSort` — already has a catch-all; **no edit**.

The five theorems that `cases s₁ <;> cases s₂` gain four rows each and need the three
disjointness facts as hypotheses.  `SPShape` is again untouched: none of its consumers ranges over
a variable.
-/

section Audit
-- §0-§1: the gap, and the spine/spineHead bridge
#print axioms Lean4Lean.VExpr.spine_fst_eq_spineHead
#print axioms Lean4Lean.VExpr.spineHead_ne_app
#print axioms Lean4Lean.VExpr.eq_bvar_mkApp_of_spineHead
#print axioms Lean4Lean.VEnv.RigidShapeV.toExpr_bvar_mkApp_nil
#print axioms Lean4Lean.VEnv.RigidShapeV.toExpr_ne_bvar_app
#print axioms Lean4Lean.VEnv.RigidShape.toExpr_ne_bvar_app
-- §3: the collapses
#print axioms Lean4Lean.VEnv.RigidShapeVSUniq.rigidShapeVUniq
#print axioms Lean4Lean.VEnv.RigidShapeVSUniqNS.rigidShapeVUniqNS
#print axioms Lean4Lean.VEnv.RigidShapeVSUniq.rigidShapeUniq
#print axioms Lean4Lean.VEnv.RigidShapeVSUniqNS.rigidShapeUniqNS
-- §4: the firing test
#print axioms Lean4Lean.VEnv.spineVarPiDisj_of_rigidShapeVSUniq
#print axioms Lean4Lean.VEnv.not_rigidShapeVSUniq_of_not_spineVarPiDisj
-- §5: the row deletion
#print axioms Lean4Lean.VEnv.codLift_spineVar_absurd
#print axioms Lean4Lean.VEnv.PiCodLiftNeutral.of_noSpineVar
#print axioms Lean4Lean.VEnv.PiCodLiftNeutralNV.toNVS
#print axioms Lean4Lean.VEnv.piDescend_iff_neutralNVS_sortConv
#print axioms Lean4Lean.VEnv.spineHead_cases_of_noSpineVar
-- §6: the price
#print axioms Lean4Lean.VEnv.rigidShapeVSUniq_of_family
#print axioms Lean4Lean.VEnv.RigidShapeVSUniq.spineVarSortDisj
#print axioms Lean4Lean.VEnv.RigidShapeVSUniq.spineVarAppDisj
#print axioms Lean4Lean.VEnv.rigidShapeVSUniq_iff
-- §7: anti-vacuity
#print axioms Lean4Lean.VEnv.spineVarPiDisj_nil
#print axioms Lean4Lean.VEnv.spineVar_row_reachable
#print axioms Lean4Lean.VEnv.spineVar_row_unexpressible
#print axioms Lean4Lean.VEnv.spDiagCtx_conv
#print axioms Lean4Lean.VEnv.spineVarNoConf_false
#print axioms Lean4Lean.VEnv.spDiagCtx_isProof
#print axioms Lean4Lean.VEnv.spAppCtx_conv
#print axioms Lean4Lean.VEnv.spineVarAppDisjNaive_false
#print axioms Lean4Lean.VEnv.spAppCtx_isProof
-- §8 regression: these two must match the originals printed immediately after them
#print axioms Lean4Lean.VEnv.RigidShapeVSUniqNS.rigidShapeUniq'
#print axioms Lean4Lean.VEnv.rigidShapeUniq_of_sortUniq
#print axioms Lean4Lean.VEnv.RigidShapeVSUniqNS.piUniq
#print axioms Lean4Lean.VEnv.RigidShapeUniqNS.piUniq
-- the theorems this file refines, for the side-by-side
#print axioms Lean4Lean.VEnv.piDescend_iff_neutralNV_sortConv
#print axioms Lean4Lean.VEnv.piDescend_iff_neutral_sortConv
end Audit

end Lean4Lean
