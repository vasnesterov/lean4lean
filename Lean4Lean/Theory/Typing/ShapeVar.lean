import Lean4Lean.Theory.Typing.PiDescendFstCod
import Lean4Lean.Theory.Typing.InjOneFact

/-!
# `ShapeVar`: the variable entry the shape vocabulary never had

The injectivity corner reads conversion classes back through a **shape lattice**:
`VEnv.RigidShape` (`Theory/Typing/Injectivity.lean:918`) with three entries — `sort u`,
`pi A B`, `app c ls as` — and `VEnv.SPShape` (`Theory/Typing/InjOneFact.lean:170`) with two.
**Neither has a variable entry.**  Verified here, and not by grep: §1 proves
`RigidShape.toExpr_ne_bvar` and `SPShape.toExpr_ne_bvar`, i.e. *no* shape in either vocabulary
denotes a `.bvar`, as theorems.

That is why the `.bvar` row of `PiCodLiftNeutral`'s residual (`Theory/Typing/PiDescendFstCod.lean`
§6-§7) could not be *stated*, let alone discharged: §7 of that file records the gap and stops.

## What this file does

* **§2-§3** define `RigidShapeV` — `RigidShape` plus a `var i` entry — and prove the collapse
  `RigidShapeVUniq → RigidShapeUniq` (and the `NS` form), hole-free.  So no existing consumer
  changes; **§9** re-derives two of them through the new vocabulary and the `#print axioms` are
  identical to the originals', measured in the audit block.
* **§4** `WF.instL_lhs_ne_bvar`: no rule rewrites a variable.  The exact sibling of
  `DeclRules.WF.instL_lhs_ne_sort` / `instL_lhs_ne_forallE`, from the same `lhs_shape`.  This is
  why the `var` entry carries **no** `RuleFree` side condition, where the spine entry needs
  `RuleFreeHead`.
* **§5, the firing test.** `VarPiDisj` — "a variable is not convertible to a Π" — stated, and
  reduced to the extended bridge by the *same* thirteen-case `IsDefEqStrong` induction that
  `IsDefEqU.const_forallE_inv` runs.  Twelve cases close outright; the thirteenth is `trans`,
  discharged at the shapes `.var i` / `.pi A B` — an appeal that **cannot be written** in
  `RigidShape`.  Every premise is discharged except that bridge.
* **§6** uses it: `codLift_bvar_absurd` and `PiCodLiftNeutral.of_noVar` delete the variable row
  from `PiDescendFstCod`'s residual, and `piDescend_iff_neutralNV_sortConv` is
  `piDescend_iff_neutral_sortConv` with **two** neutral heads instead of three.
* **§7** prices it: `rigidShapeVUniq_iff` — the extension is `RigidShapeUniq` conjoined with
  **exactly three** disjointness rows (var/Π, var/sort, var/app) and nothing else.
* **§8** and **§10** are the anti-vacuity apparatus, including two refutations.

## What this is NOT

**It is not a strength gain, and it is not a reduction.**  §7 is an `iff`: `RigidShapeVUniq` *is*
the old bridge plus the three variable rows, the same way `rigidShapeUniq_of_family` says the
old bridge *is* the five conclusions it packages.  So §5 is a **localisation** of the `.bvar`
row into the corner's existing shared node, not a proof of it.  That is the honest headline, and
it is the same reading `SortPiDisjPrice.lean` §2 forced for a shape-class weakening.  What is
gained is that the `.bvar` row stops being an *unnamed* gap outside the machinery and becomes a
named row of the one statement all nine — now sixteen — `trans` residuals already share.

**Does the new entry constrain a `trans` midpoint?  No** — and this is the question
`docs/vacuity-ledger.md` rows 94/94a make mandatory.  `RigidShapeV` values occur in
`RigidShapeVUniq` only as the two **endpoints** `s₁`, `s₂`; the middle term `e` is bound by `∀`
with typing premises only and carries no syntactic condition, exactly as in `RigidShapeUniq`.
`VarPiDisj`, `VarSortDisj` and `VarAppDisj` mention no midpoint at all — they are
`¬ IsDefEqU` statements between two explicit endpoints, character for character the shape of
`IsDefEqU.const_forallE_inv`.  `midShapeless_vacuous` (`InjOneFact.lean:320`) is about a
predicate on the midpoint and has nothing to bite on here.  [read off the definitions in §2 and
§5, not machine-checked — there is no formal statement of "is not a midpoint restriction".]

## Two things that were wrong on the first draft, both now theorems

1. The naive **diagonal** `i = j` — "variables are told apart by their index" — is **false at a
   `VEnv.WF` environment** (`varNoConf_false`, §8): proof irrelevance identifies two distinct
   variables inhabiting one proposition, over `VEnv.empty`, in a three-entry context.  The
   diagonal is therefore `True`, which is also the right value on its own terms: a bare variable
   has no subterms to compare.
2. The naive **var/app off-diagonal**, unguarded, is **false at a `VEnv.WF` environment**
   (`varAppDisjNaive_false`, §10): a variable and a rule-free constant spine can both be proofs
   of one proposition.  My first `rigidShapeVUniq_of_family` took that hypothesis and was
   therefore **vacuous**; `VarAppDisj` now carries `¬ IsProof`, which is what the bridge's own
   premise supplies.

## Holes

`varPiDisj_of_rigidShapeVUniq`, `RigidShapeVUniq.varSortDisj` and `RigidShapeVUniq.varAppDisj`
carry `sorryAx` through **`IsDefEqU.forallE_inv_stratified`** only (via `IsDefEqStrong`);
`piDescend_iff_neutralNV_sortConv` carries `forallE_inv_stratified` **and**
`WF.rigidShapeUniqNS`, the same two as the `piDescend_iff_neutral_sortConv` it refines.
`IsDefEqU.weakN_iff` is in **no** cone here.  **That is not hole-freeness**, and there is a
second, bigger caveat the cone cannot see: the extended bridge is carried as a **hypothesis**,
and a hypothesis is not a dependency (`docs/vacuity-ledger.md` §0, third instrument).  The
hole-free declarations are the collapse (§3), `instL_lhs_ne_bvar` (§4), the row deletion
mechanics (§6), the price tag `rigidShapeVUniq_of_family` (§7) and the whole of §8 and §10.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 The gap, as two theorems rather than two greps -/

/-- **The old vocabulary cannot denote a variable.**  Every `RigidShape` denotes a term whose
spine head is a `.sort`, a `.forallE` or a `.const`; none is a `.bvar`.  This is the
"cannot express" half of the firing test, machine-checked rather than grepped. -/
theorem RigidShape.toExpr_ne_bvar (s : RigidShape) (i : Nat) : s.toExpr ≠ .bvar i := by
  cases s with
  | sort u => exact nofun
  | pi A B => exact nofun
  | app c ls as =>
    intro h
    have hs := congrArg VExpr.spineHead h
    simp only [RigidShape.toExpr, VExpr.spineHead_mkApp] at hs
    exact absurd hs nofun

/-- The same for `SPShape` (`InjOneFact.lean`), the corner's two-entry vocabulary. -/
theorem SPShape.toExpr_ne_bvar (s : SPShape) (i : Nat) : s.toExpr ≠ .bvar i := by
  cases s <;> exact nofun

/-! ## §2 The extended vocabulary -/

/-- `RigidShape` (`Injectivity.lean:918`) with a **variable** entry added. -/
inductive RigidShapeV where
  | sort (u : VLevel)
  | pi (A B : VExpr)
  | app (c : Lean.Name) (ls : List VLevel) (as : List VExpr)
  | var (i : Nat)

/-- The term a shape denotes. -/
def RigidShapeV.toExpr : RigidShapeV → VExpr
  | .sort u => .sort u
  | .pi A B => .forallE A B
  | .app c ls as => (VExpr.const c ls).mkApp as
  | .var i => .bvar i

@[simp] theorem RigidShapeV.toExpr_var {i : Nat} : (RigidShapeV.var i).toExpr = .bvar i := rfl

/-- The side condition.  The variable entry carries **none**: a variable heads no rule
(`WF.instL_lhs_ne_bvar`, §4), so there is no `RuleFreeHead` analogue to ask for. -/
def RigidShapeV.RuleFree (env : VEnv) : RigidShapeV → Prop
  | .sort _ => True
  | .pi _ _ => True
  | .app c _ _ => env.RuleFreeHead c
  | .var _ => True

/-- **What two shapes in one conversion class have in common**, with the three new variable
rows.  The three off-diagonal variable rows are disjointness; the **diagonal is `True`**, and
that is not laziness: a bare variable has no subterms, so `i = j → (nothing)` is `True`, and
the unguarded `i = j` is *false* at a `VEnv.WF` environment (§6). -/
def RigidShapeV.Compat (env : VEnv) (U : Nat) (Γ : List VExpr) :
    RigidShapeV → RigidShapeV → Prop
  | .sort u, .sort v => u ≈ v
  | .pi A B, .pi A' B' =>
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧ env.IsDefEq U (A'::Γ) B B' (.sort u)
  | .app c ls as, .app c' ls' as' =>
    c = c' → List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as'
  | .var _, .var _ => True
  | _, _ => False

/-- The two shapes are both sorts — `RigidShape.BothSort` transported. -/
def RigidShapeV.BothSort : RigidShapeV → RigidShapeV → Prop
  | .sort _, .sort _ => True
  | _, _ => False

/-- **The extended bridge.**  Identical to `RigidShapeUniq` except that `s₁`, `s₂` range over
`RigidShapeV`.  Note what is *not* touched: the middle term `e` is still bound by `∀` with only
typing premises on it, so this is not a midpoint restriction (see §7). -/
def RigidShapeVUniq (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T : VExpr} {s₁ s₂ : RigidShapeV},
    OnCtx Γ (env.IsType U) → ¬ env.IsProof U Γ e →
    s₁.RuleFree env → s₂.RuleFree env →
    env.IsDefEq U Γ e s₁.toExpr T → env.IsDefEq U Γ e s₂.toExpr T →
    s₁.Compat env U Γ s₂

/-- `RigidShapeVUniq` minus its `sort`/`sort` entry, mirroring `RigidShapeUniqNS`. -/
def RigidShapeVUniqNS (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T : VExpr} {s₁ s₂ : RigidShapeV},
    OnCtx Γ (env.IsType U) → ¬ env.IsProof U Γ e →
    s₁.RuleFree env → s₂.RuleFree env → ¬ s₁.BothSort s₂ →
    env.IsDefEq U Γ e s₁.toExpr T → env.IsDefEq U Γ e s₂.toExpr T →
    s₁.Compat env U Γ s₂

/-! ## §3 The collapse: nothing the old vocabulary said is lost or changed -/

/-- The embedding of the old vocabulary. -/
def RigidShape.toV : RigidShape → RigidShapeV
  | .sort u => .sort u
  | .pi A B => .pi A B
  | .app c ls as => .app c ls as

@[simp] theorem RigidShape.toExpr_toV (s : RigidShape) : s.toV.toExpr = s.toExpr := by
  cases s <;> rfl

@[simp] theorem RigidShape.ruleFree_toV (s : RigidShape) :
    s.toV.RuleFree env ↔ s.RuleFree env := by
  cases s <;> exact Iff.rfl

@[simp] theorem RigidShape.compat_toV {Γ : List VExpr} (s₁ s₂ : RigidShape) :
    s₁.toV.Compat env U Γ s₂.toV ↔ s₁.Compat env U Γ s₂ := by
  cases s₁ <;> cases s₂ <;> exact Iff.rfl

@[simp] theorem RigidShape.bothSort_toV (s₁ s₂ : RigidShape) :
    s₁.toV.BothSort s₂.toV ↔ s₁.BothSort s₂ := by
  cases s₁ <;> cases s₂ <;> exact Iff.rfl

/-- **The extension is at least as strong: every existing consumer still gets its bridge.** -/
theorem RigidShapeVUniq.rigidShapeUniq (H : RigidShapeVUniq env U) : RigidShapeUniq env U := by
  intro Γ e T s₁ s₂ hΓ hnp hr₁ hr₂ h₁ h₂
  have h₁' : env.IsDefEq U Γ e s₁.toV.toExpr T := by rw [RigidShape.toExpr_toV]; exact h₁
  have h₂' : env.IsDefEq U Γ e s₂.toV.toExpr T := by rw [RigidShape.toExpr_toV]; exact h₂
  exact (RigidShape.compat_toV s₁ s₂).1
    (H hΓ hnp ((RigidShape.ruleFree_toV s₁).2 hr₁) ((RigidShape.ruleFree_toV s₂).2 hr₂) h₁' h₂')

@[inherit_doc RigidShapeVUniq.rigidShapeUniq]
theorem RigidShapeVUniqNS.rigidShapeUniqNS (H : RigidShapeVUniqNS env U) :
    RigidShapeUniqNS env U := by
  intro Γ e T s₁ s₂ hΓ hnp hr₁ hr₂ hbs h₁ h₂
  have h₁' : env.IsDefEq U Γ e s₁.toV.toExpr T := by rw [RigidShape.toExpr_toV]; exact h₁
  have h₂' : env.IsDefEq U Γ e s₂.toV.toExpr T := by rw [RigidShape.toExpr_toV]; exact h₂
  exact (RigidShape.compat_toV s₁ s₂).1
    (H hΓ hnp ((RigidShape.ruleFree_toV s₁).2 hr₁) ((RigidShape.ruleFree_toV s₂).2 hr₂)
      (fun h => hbs ((RigidShape.bothSort_toV s₁ s₂).1 h)) h₁' h₂')

/-! ## §4 The rule-table fact the variable row needs, and it is free -/

/-- **No rule rewrites a variable.**  The exact sibling of `WF.instL_lhs_ne_sort` /
`WF.instL_lhs_ne_forallE` (`Theory/Typing/DeclRules.lean:234,240`), from the same
`IsDeclRule.lhs_shape`: a rule's left-hand side is a `.const`, an `.app` or a `.lam`, and
`instL` preserves each head, so it is never a `.bvar`.

This is why `RigidShapeV.RuleFree` has no side condition on the variable entry: the
`RuleFreeHead` the spine entry carries exists because a δ-rule can reduce a constant spine to
anything, and no rule can do that to a variable.  **Stated here rather than in `DeclRules.lean`
only because that file is not mine**; the natural home is next to its two siblings. -/
theorem WF.instL_lhs_ne_bvar {df : VDefEq} (henv : env.WF) (h : env.defeqs df)
    (ls : List VLevel) (i : Nat) : df.lhs.instL ls ≠ .bvar i := by
  rcases (henv.defeq_isDeclRule h).lhs_shape with ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;>
    rw [e] <;> exact nofun

/-! ## §5 The firing test: the variable row, stated and reduced to the extended bridge

`PiDescendFstCod.lean` §7 records the gap and stops there, because the statement it wants
cannot be *written* in `RigidShape`'s vocabulary (§1 above proves that).  With the `var` entry
it can be written, and the same thirteen-case `IsDefEqStrong` induction that
`IsDefEqU.const_forallE_inv` runs closes twelve of the thirteen; the thirteenth is `trans`, and
it is discharged by the **new** `var`/`pi` row of `RigidShapeV.Compat`.

So the entry *fires*: every premise is discharged except the extended bridge itself, and the
bridge is the same node the other four members of the family already sit on. -/

/-- **A variable is not convertible to a Π.**  The `.bvar` row of `PiCodLiftNeutral`'s
residual, in the corner's own idiom (compare `IsDefEqU.const_forallE_inv`).  Unstatable in
`RigidShape`: `RigidShape.toExpr_ne_bvar`. -/
def VarPiDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {i : Nat} {A B : VExpr}, OnCtx Γ (env.IsType U) →
    ¬ env.IsDefEqU U Γ (.bvar i) (.forallE A B)

/-- **The firing test.**  Twelve of thirteen `IsDefEqStrong` cases close outright; the
thirteenth is `trans`, discharged at the shapes `.var i` and `.pi A B`, whose
`RigidShapeV.Compat` entry is `False` — an appeal that **cannot be written at all** without the
new entry.

Case by case, and the list is worth having because it is what makes the entry cheap:
`extra` by `WF.instL_lhs_ne_bvar` (§4) and `WF.instL_lhs_ne_forallE`; `proofIrrel` by "a Π is
not a proof" (`forallE_not_proof` from `WF.sortUniq'`, so it costs the statement no
hypothesis); `bvar` is vacuous because that constructor's *other* endpoint is the same
variable, not a Π; `beta` and `eta` are vacuous on their left endpoint, which is an `.app` and
a `.lam`; `sortDF`/`constDF`/`appDF`/`lamDF`/`forallEDF` on endpoint heads; `symm` and
`defeqDF` are bookkeeping. -/
theorem varPiDisj_of_rigidShapeVUniq (henv : VEnv.WF env) (H : RigidShapeVUniq env U) :
    VarPiDisj env U := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      OnCtx Γ (env.IsType U) → ∀ (i : Nat) (A B : VExpr),
        (e₁ = .bvar i ∧ e₂ = .forallE A B) ∨ (e₂ = .bvar i ∧ e₁ = .forallE A B) → False := by
    intro Γ e₁ e₂ T HH
    induction HH with
    | symm _ ih => exact fun hΓ' i A B h => ih hΓ' i A B h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans hd1 hd2 ih1 ih2 =>
      rintro hΓ' i A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact H (s₁ := .var i) (s₂ := .pi A B) hΓ'
          (not_isProof_of_defeqU_forallE henv hΓ' ⟨_, hd2.defeq⟩) trivial trivial
          hd1.defeq.symm hd2.defeq
      · exact H (s₁ := .pi A B) (s₂ := .var i) hΓ'
          (not_isProof_of_defeqU_forallE henv hΓ' ⟨_, hd1.defeq.symm⟩) trivial trivial
          hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 h3 _ _ _ =>
      rintro hΓ' i A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact forallE_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h3.defeq.hasType.1
      · exact forallE_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h2.defeq.hasType.1
    | extra h1 =>
      rintro _ i A B (⟨he, -⟩ | ⟨-, hf⟩)
      · exact henv.instL_lhs_ne_bvar h1 _ _ he
      · exact henv.instL_lhs_ne_forallE h1 _ _ _ hf
    | bvar _ _ _ => rintro _ i A B (⟨-, hf⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
    | sortDF _ _ _ | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _
    | lamDF _ _ _ _ _ _ _ =>
      rintro _ i A B (⟨hf, -⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
    | forallEDF _ _ _ _ _ =>
      rintro _ i A B (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact absurd hf nofun
    | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      rintro _ i A B (⟨hf, -⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
  intro Γ i A B hΓ hc
  obtain ⟨_, hd⟩ := hc
  exact aux (hd.strong henv.ordered hΓ) hΓ i A B (.inl ⟨rfl, rfl⟩)

/-! ## §6 …and it closes the `.bvar` row of `PiCodLiftNeutral` -/

/-- A lift of a variable is a variable. -/
theorem liftN_bvar_eq (n i k : Nat) : (VExpr.bvar i).liftN n k = .bvar (liftVar n i k) := rfl

/-- **`PiCodLiftNeutral`'s variable row is closed** — the exact analogue of
`codLift_const_ruleFree` (`PiDescendFstCod.lean` §7) for the head that had no shape slot. -/
theorem codLift_bvar_absurd (H : VarPiDisj env U) {Γ' : List VExpr}
    (hΓ' : OnCtx Γ' (env.IsType U)) {i n k : Nat} {S B : VExpr}
    (hconv : env.IsDefEqU U Γ' ((VExpr.bvar i).liftN n k)
      (.forallE (S.liftN n k) B)) : False :=
  H hΓ' (liftN_bvar_eq n i k ▸ hconv)

/-- **`PiCodLiftNeutral` with the variable row deleted.**  Three neutral heads become two. -/
def PiCodLiftNeutralNV (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {f a T S B : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) → T.PiDescendNeutral →
    (∀ i, T ≠ .bvar i) →
    env.HasType U Γ f T → env.HasType U Γ a S →
    env.IsDefEqU U Γ' (T.liftN n k) (.forallE (S.liftN n k) B) →
    ∃ B₀ : VExpr, env.IsDefEqU U (S.liftN n k :: Γ') B (B₀.liftN n (k+1))

/-- The row deletion, as a reduction. -/
theorem PiCodLiftNeutral.of_noVar (H : VarPiDisj env U) (h : PiCodLiftNeutralNV env U) :
    PiCodLiftNeutral env U := by
  intro n k Γ Γ' f a T S B W hΓ hΓ' hne hfT haS hconv
  cases T with
  | bvar i => exact (codLift_bvar_absurd H hΓ' hconv).elim
  | sort u => exact h W hΓ hΓ' hne nofun hfT haS hconv
  | const c ls => exact h W hΓ hΓ' hne nofun hfT haS hconv
  | app g x => exact h W hΓ hΓ' hne nofun hfT haS hconv
  | lam A' b => exact h W hΓ hΓ' hne nofun hfT haS hconv
  | forallE A' B' => exact h W hΓ hΓ' hne nofun hfT haS hconv

/-- The converse half, which is free: deleting a row only weakens. -/
theorem PiCodLiftNeutral.toNV (h : PiCodLiftNeutral env U) : PiCodLiftNeutralNV env U :=
  fun W hΓ hΓ' hne _ hfT haS hconv => h W hΓ hΓ' hne hfT haS hconv

variable! (henv : VEnv.WF env) in
/-- **`PiDescend`'s residual with the variable row gone.**  Compare
`piDescend_iff_neutral_sortConv`: the same equivalence, with one of the three neutral heads
removed, at the price of `VarPiDisj` — which §5 reduces to the extended bridge. -/
theorem piDescend_iff_neutralNV_sortConv (H : VarPiDisj env U) :
    PiDescend env U ↔ PiCodLiftNeutralNV env U ∧ SortConvStrengthening env U := by
  refine ⟨fun HP => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · obtain ⟨hn, hs⟩ := (piDescend_iff_neutral_sortConv henv).1 HP
    exact ⟨hn.toNV, hs⟩
  · exact (piDescend_iff_neutral_sortConv henv).2 ⟨PiCodLiftNeutral.of_noVar H h1, h2⟩

/-! ## §7 The price tag: the extension is the old bridge plus exactly three disjointness facts

`rigidShapeUniq_of_family` (`Injectivity.lean`) bounds the old bridge above by the five
conclusions it packages, so that hoisting it neither weakened nor strengthened anything.  §7 is
that measurement for the extension, and it is the answer to "is a vocabulary change buying
strength it has not paid for?": **no.**  `RigidShapeVUniq` follows from `RigidShapeUniq`
together with the **three** new off-diagonal variable rows, and nothing else — no new
`trans`-level demand, no new side condition, and the variable *diagonal* costs nothing at all
(it is `True`). -/

/-- The var/sort row. -/
def VarSortDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {i : Nat} {u : VLevel}, OnCtx Γ (env.IsType U) →
    ¬ env.IsDefEqU U Γ (.bvar i) (.sort u)

/-- The var/app row, guarded by `RuleFreeHead` (as the app entry is) **and by `¬ IsProof`**.

The second guard is not prudence: §10 **refutes** the unguarded form at a `VEnv.WF`
environment.  This is the one place the variable rows differ from the sort and Π rows: those
close their own `proofIrrel` case for free, because a sort and a Π are not proofs
(`sort_not_proof` / `forallE_not_proof`), whereas *both* a variable and a rule-free constant
spine can be proofs of one proposition, and then proof irrelevance identifies them.  Without
the guard this hypothesis is unsatisfiable and every theorem taking it is vacuous — which the
first draft of §7 was. -/
def VarAppDisj (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {i : Nat} {c : Lean.Name} {ls : List VLevel} {as : List VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c → ¬ env.IsProof U Γ (.bvar i) →
    ¬ env.IsDefEqU U Γ (.bvar i) ((VExpr.const c ls).mkApp as)

/-- **Bounded above.**  The extended bridge is the old one plus the three variable rows: so the
entry adds exactly three disjointness facts to the open statement, and nothing else.  Read with
`RigidShapeVUniq.rigidShapeUniq` (§3), which is the other direction on the old rows. -/
theorem rigidShapeVUniq_of_family (htr : env.ProofTransport U) (hold : env.RigidShapeUniq U)
    (hvp : VarPiDisj env U) (hvs : VarSortDisj env U) (hva : VarAppDisj env U) :
    env.RigidShapeVUniq U := by
  intro Γ e T s₁ s₂ hΓ hnp hr₁ hr₂ h₁ h₂
  have hs : env.IsDefEqU U Γ s₁.toExpr s₂.toExpr := ⟨T, h₁.symm.trans h₂⟩
  cases s₁ with
  | var i =>
    cases s₂ with
    | var j => trivial
    | sort u => exact hvs hΓ hs
    | pi A B => exact hvp hΓ hs
    | app c ls as => exact hva hΓ hr₂ (fun hp => hnp (htr hΓ ⟨_, h₁.symm⟩ hp)) hs
  | sort u =>
    cases s₂ with
    | var j => exact hvs hΓ hs.symm
    | sort v => exact hold (s₁ := .sort u) (s₂ := .sort v) hΓ hnp hr₁ hr₂ h₁ h₂
    | pi A B => exact hold (s₁ := .sort u) (s₂ := .pi A B) hΓ hnp hr₁ hr₂ h₁ h₂
    | app c ls as => exact hold (s₁ := .sort u) (s₂ := .app c ls as) hΓ hnp hr₁ hr₂ h₁ h₂
  | pi A B =>
    cases s₂ with
    | var j => exact hvp hΓ hs.symm
    | sort v => exact hold (s₁ := .pi A B) (s₂ := .sort v) hΓ hnp hr₁ hr₂ h₁ h₂
    | pi A' B' => exact hold (s₁ := .pi A B) (s₂ := .pi A' B') hΓ hnp hr₁ hr₂ h₁ h₂
    | app c ls as => exact hold (s₁ := .pi A B) (s₂ := .app c ls as) hΓ hnp hr₁ hr₂ h₁ h₂
  | app c ls as =>
    cases s₂ with
    | var j => exact hva hΓ hr₁ (fun hp => hnp (htr hΓ ⟨_, h₂.symm⟩ hp)) hs.symm
    | sort v => exact hold (s₁ := .app c ls as) (s₂ := .sort v) hΓ hnp hr₁ hr₂ h₁ h₂
    | pi A B => exact hold (s₁ := .app c ls as) (s₂ := .pi A B) hΓ hnp hr₁ hr₂ h₁ h₂
    | app c' ls' as' =>
      exact hold (s₁ := .app c ls as) (s₂ := .app c' ls' as') hΓ hnp hr₁ hr₂ h₁ h₂

/-- All three new rows come out of the extended bridge, so §7 is an equivalence on the nose. -/
theorem RigidShapeVUniq.varSortDisj (henv : VEnv.WF env) (H : RigidShapeVUniq env U) :
    VarSortDisj env U := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      OnCtx Γ (env.IsType U) → ∀ (i : Nat) (u : VLevel),
        (e₁ = .bvar i ∧ e₂ = .sort u) ∨ (e₂ = .bvar i ∧ e₁ = .sort u) → False := by
    intro Γ e₁ e₂ T HH
    induction HH with
    | symm _ ih => exact fun hΓ' i u h => ih hΓ' i u h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans hd1 hd2 ih1 ih2 =>
      rintro hΓ' i u (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact H (s₁ := .var i) (s₂ := .sort u) hΓ'
          (not_isProof_of_defeqU_sort henv hΓ' ⟨_, hd2.defeq⟩) trivial trivial
          hd1.defeq.symm hd2.defeq
      · exact H (s₁ := .sort u) (s₂ := .var i) hΓ'
          (not_isProof_of_defeqU_sort henv hΓ' ⟨_, hd1.defeq.symm⟩) trivial trivial
          hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 h3 _ _ _ =>
      rintro hΓ' i u (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact sort_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h3.defeq.hasType.1
      · exact sort_not_proof (WF.sortUniq' henv) henv.ordered hΓ'
          h1.defeq.hasType.1 h2.defeq.hasType.1
    | extra h1 =>
      rintro _ i u (⟨he, -⟩ | ⟨-, hf⟩)
      · exact henv.instL_lhs_ne_bvar h1 _ _ he
      · exact henv.instL_lhs_ne_sort h1 _ _ hf
    | bvar _ _ _ => rintro _ i u (⟨-, hf⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
    | sortDF _ _ _ => rintro _ i u (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact absurd hf nofun
    | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _ | lamDF _ _ _ _ _ _ _
    | forallEDF _ _ _ _ _ =>
      rintro _ i u (⟨hf, -⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
    | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      rintro _ i u (⟨hf, -⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
  intro Γ i u hΓ hc
  obtain ⟨_, hd⟩ := hc
  exact aux (hd.strong henv.ordered hΓ) hΓ i u (.inl ⟨rfl, rfl⟩)

/-! ## §8 Anti-vacuity

Five checks, in the order `docs/vacuity-ledger.md` §0 asks for them. -/

/-- **Degenerate instance (ledger blindness 7, in its dual form).**  `VarPiDisj` is a
*negation*, so the risk at the degenerate instance is not emptiness but triviality — and at
`Γ = []` it is indeed a **theorem**, at every `Ordered` environment and every `U`, by the scope
invariant `IsDefEq.closedN` — so this control is itself hole-free, unlike the route through
`HasType.bvar_inv`, which goes via `.strong` and carries `sorryAx`.  So all of `VarPiDisj`'s
content lives at a non-empty context, and the reachability check below is at a context of length
two, deliberately. -/
theorem varPiDisj_nil (henv : Ordered env) {i : Nat} {A B : VExpr} :
    ¬ env.IsDefEqU U [] (.bvar i) (.forallE A B) := by
  intro hc
  obtain ⟨T, h⟩ := hc
  have hΓ : CtxClosed ([] : List VExpr) := trivial
  exact absurd (h.closedN henv hΓ) (Nat.not_lt_zero i)

/-! ### The witness contexts

Both live over `VEnv.empty`, which is `VEnv.WF` (`⟨[], .empty⟩`) — so neither is an
`Ordered`-but-not-`WF` artefact, and no inconsistent axiom is declared anywhere in them.  The
whole construction is `Lookup`s and one `proofIrrel`. -/

/-- `Γ₂ = [.bvar 0, Prop]`: the shortest context in which a **variable is a type**. -/
def varCtx2 : List VExpr := [.bvar 0, .sort .zero]

/-- `Γ₃ = [.bvar 1, .bvar 0, Prop]`: `Γ₂` extended by a second inhabitant of the same
proposition. -/
def varCtx3 : List VExpr := [.bvar 1, .bvar 0, .sort .zero]

theorem varCtx2_onCtx : OnCtx varCtx2 ((∅ : VEnv).IsType 0) :=
  ⟨⟨trivial, _, .sort trivial⟩, _, .bvar (Lookup.zero' rfl)⟩

/-- **The `.bvar` row of `PiCodLiftNeutral` is reachable**: over `VEnv.empty`, in `varCtx2`, the
term `.bvar 0` is well-typed at the **variable** type `.bvar 1`, which is itself a type and is
`PiDescendNeutral`.  So §6 deleted a row with live instances on its type side, not an empty one.

What this does *not* exhibit is the row's conversion premise — and it cannot: by
`PiDescendFstCod.piDescend_of_no_neutral_pi`, an absolute inhabitation witness for the residual
would refute the target.  That is the same situation `ForallInvPrice.hyp_inhabited_iff` records,
and it is why this check is about the type side only. -/
theorem bvar_row_reachable :
    (∅ : VEnv).WF ∧ OnCtx varCtx2 ((∅ : VEnv).IsType 0) ∧
      (∅ : VEnv).IsType 0 varCtx2 (.bvar 1) ∧
      (∅ : VEnv).HasType 0 varCtx2 (.bvar 0) (.bvar 1) ∧
      (VExpr.bvar 1).PiDescendNeutral ∧
      ∀ s : RigidShape, s.toExpr ≠ .bvar 1 :=
  ⟨⟨[], .empty⟩, varCtx2_onCtx, ⟨_, .bvar (.succ (Lookup.zero' rfl))⟩,
   .bvar (Lookup.zero' rfl), trivial, fun s => s.toExpr_ne_bvar 1⟩

/-! ### The negative control

The naive reading of a "variable entry" is that the diagonal should say **`i = j`** — variables
are distinguished by their index.  That is **false at a `VEnv.WF` environment**, and this is the
control: proof irrelevance identifies two *distinct* variables whenever they inhabit one and the
same proposition, and `varCtx3` is the shortest context where that happens.

The second half — what makes it a control rather than a refutation of the target
(`ForallInvPrice`'s `rogueSortPiEnv` / `not_wf_sortPiEnv` discipline) — is `varCtx3_compat` and
`varCtx3_isProof`: the row this file actually declares is **satisfied** at the witness, and the
bridge's `¬ IsProof` premise fails there, so the witness is outside its scope. -/

/-- The naive var/var no-confusion row. -/
def VarNoConf (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {i j : Nat}, OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.bvar i) (.bvar j) → i = j

theorem varCtx3_onCtx : OnCtx varCtx3 ((∅ : VEnv).IsType 0) :=
  ⟨varCtx2_onCtx, _, .bvar (.succ (Lookup.zero' rfl))⟩

/-- `.bvar 2` is the proposition; `.bvar 0` and `.bvar 1` both inhabit it. -/
theorem varCtx3_prop : (∅ : VEnv).HasType 0 varCtx3 (.bvar 2) (.sort .zero) :=
  .bvar (.succ (.succ (Lookup.zero' rfl)))

theorem varCtx3_h0 : (∅ : VEnv).HasType 0 varCtx3 (.bvar 0) (.bvar 2) :=
  .bvar (Lookup.zero' rfl)

theorem varCtx3_h1 : (∅ : VEnv).HasType 0 varCtx3 (.bvar 1) (.bvar 2) :=
  .bvar (.succ (Lookup.zero' rfl))

/-- **Two distinct variables are convertible**, over `VEnv.empty`, in a context every entry of
which is a type. -/
theorem varCtx3_conv : (∅ : VEnv).IsDefEqU 0 varCtx3 (.bvar 0) (.bvar 1) :=
  ⟨_, .proofIrrel varCtx3_prop varCtx3_h0 varCtx3_h1⟩

/-- **The control fires**: the unguarded variable diagonal is false at a `VEnv.WF`
environment. -/
theorem varNoConf_false : ¬ VarNoConf (∅ : VEnv) 0 :=
  fun h => absurd (h varCtx3_onCtx varCtx3_conv) nofun

/-- …and **the control is a control**: the row this file declares, `RigidShapeV.Compat` at
`.var 0` / `.var 1`, holds at the witness, so nothing here refutes `RigidShapeVUniq`. -/
theorem varCtx3_compat : RigidShapeV.Compat (∅ : VEnv) 0 varCtx3 (.var 0) (.var 1) := trivial

/-- …and the bridge's own premise fails there: `.bvar 0` **is** a proof in `varCtx3`, so the
witness is outside `RigidShapeVUniq`'s scope even before `Compat` is consulted. -/
theorem varCtx3_isProof : (∅ : VEnv).IsProof 0 varCtx3 (.bvar 0) :=
  ⟨_, varCtx3_prop, varCtx3_h0⟩

/-- Finally, the witness is silent on `VarPiDisj` for the dullest possible reason, stated so
that it is on the record: both its endpoints are variables, and a variable is not a Π. -/
theorem varCtx3_not_pi (i : Nat) (A B : VExpr) : VExpr.bvar i ≠ .forallE A B := nofun

/-! ## §8.5 The third row, and the exact price in both directions

This is §7's other half; it sits here because `VarAppDisj`'s `¬ IsProof` guard is what §8's and
§10's refutations force, and it reads better after them. -/

/-- **The guarded var/app row comes out of the extended bridge too**, so with §3, §5 and §7 the
extension *is* the old bridge conjoined with the three variable rows — an equivalence, not a
reduction.  Say that plainly: this file buys **vocabulary**, not strength (see the module
header).

The induction is easier than `const_app_inv`'s, and for a reason worth recording: one endpoint
is a **bare** variable, so `appDF` is vacuous on it (a variable is never an `.app`) and no
spine-peeling invariant is needed.  Only `beta` and `eta` need the spine-head argument, on
their *other* endpoint. -/
theorem RigidShapeVUniq.varAppDisj (henv : VEnv.WF env) (H : RigidShapeVUniq env U) :
    VarAppDisj env U := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      OnCtx Γ (env.IsType U) → ∀ (i : Nat) (c : Lean.Name) (ls : List VLevel) (as : List VExpr),
        env.RuleFreeHead c → ¬ env.IsProof U Γ (.bvar i) →
        (e₁ = .bvar i ∧ e₂ = (VExpr.const c ls).mkApp as) ∨
        (e₂ = .bvar i ∧ e₁ = (VExpr.const c ls).mkApp as) → False := by
    intro Γ e₁ e₂ T HH
    induction HH with
    | symm _ ih => exact fun hΓ' i c ls as hrf hnp h => ih hΓ' i c ls as hrf hnp h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans hd1 hd2 ih1 ih2 =>
      rintro hΓ' i c ls as hrf hnp (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact H (s₁ := .var i) (s₂ := .app c ls as) hΓ'
          (fun hp => hnp (hp.defeqU henv hΓ' ⟨_, hd1.defeq.symm⟩)) trivial hrf
          hd1.defeq.symm hd2.defeq
      · exact H (s₁ := .app c ls as) (s₂ := .var i) hΓ'
          (fun hp => hnp (hp.defeqU henv hΓ' ⟨_, hd2.defeq⟩)) hrf trivial
          hd1.defeq.symm hd2.defeq
    | proofIrrel h1 h2 h3 _ _ _ =>
      rintro hΓ' i c ls as hrf hnp (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hnp ⟨_, h1.defeq.hasType.1, h2.defeq.hasType.1⟩
      · exact hnp ⟨_, h1.defeq.hasType.1, h3.defeq.hasType.1⟩
    | extra h1 =>
      rintro _ i c ls as hrf _ (⟨he, -⟩ | ⟨-, he⟩)
      · exact henv.instL_lhs_ne_bvar h1 _ _ he
      · exact hrf _ h1 (by rw [← VExpr.headConst?_instL, he, VExpr.headConst?_mkApp]; rfl)
    | bvar _ _ _ =>
      rintro _ i c ls as _ _ (⟨-, he⟩ | ⟨-, he⟩) <;>
        (have hs := congrArg VExpr.spineHead he
         rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun)
    | sortDF _ _ _ | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _
    | lamDF _ _ _ _ _ _ _ | forallEDF _ _ _ _ _ =>
      rintro _ i c ls as _ _ (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact absurd hf nofun
    | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      rintro _ i c ls as _ _ (⟨hf, -⟩ | ⟨-, he⟩)
      · exact absurd hf nofun
      · have hs := congrArg VExpr.spineHead he
        rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun
  intro Γ i c ls as hΓ hrf hnp hc
  obtain ⟨_, hd⟩ := hc
  exact aux (hd.strong henv.ordered hΓ) hΓ i c ls as hrf hnp (.inl ⟨rfl, rfl⟩)

/-- **The exact price, both ways.**  `RigidShapeVUniq` is `RigidShapeUniq` plus exactly the
three variable rows — no more, no less. -/
theorem rigidShapeVUniq_iff (henv : VEnv.WF env) (htr : env.ProofTransport U) :
    env.RigidShapeVUniq U ↔
      env.RigidShapeUniq U ∧ VarPiDisj env U ∧ VarSortDisj env U ∧ VarAppDisj env U :=
  ⟨fun H => ⟨H.rigidShapeUniq, varPiDisj_of_rigidShapeVUniq henv H, H.varSortDisj henv,
      H.varAppDisj henv⟩,
   fun ⟨h1, h2, h3, h4⟩ => rigidShapeVUniq_of_family htr h1 h2 h3 h4⟩

/-! ## §9 Regression: every existing consumer comes out identical

The extension is only useful if nothing downstream notices it.  These two re-derive existing
consumers *through* `RigidShapeVUniqNS` instead of `RigidShapeUniqNS`; their `#print axioms` and
hole cones are the originals' (see the audit block, and `docs/handoff-shapevar.md` §4 for the
side-by-side).  Because `RigidShapeVUniqNS.rigidShapeUniqNS` is hole-free, composing with it
cannot change an axiom set — which is the point. -/

/-- `rigidShapeUniq_of_sortUniq`, through the extended vocabulary. -/
theorem RigidShapeVUniqNS.rigidShapeUniq' (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (h : env.RigidShapeVUniqNS U) : env.RigidShapeUniq U :=
  rigidShapeUniq_of_sortUniq henv hsu h.rigidShapeUniqNS

/-- `RigidShapeUniqNS.piUniq`, through the extended vocabulary. -/
theorem RigidShapeVUniqNS.piUniq (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (h : env.RigidShapeVUniqNS U) : env.RigidPiUniq U :=
  RigidShapeUniqNS.piUniq henv hsu h.rigidShapeUniqNS

/-! ## §10 The var/app row is FALSE without its `¬ IsProof` guard, at a `VEnv.WF` environment

The naive variable rows are two, and **both** naive readings are wrong, for two different
reasons — this is the second.  §8's control shows the *diagonal* may not say `i = j`; this one
shows the *var/app off-diagonal* may not be an unguarded disjointness.

`svEnv` is `VEnv.empty` plus one axiom `svC : ∀ X : Prop, X`, a **proposition**.  It has no
`defeqs` at all, so every head is rule-free, and it is `VEnv.WF` by an `.axiom` step — the same
one-axiom construction `RigidConstPrice.wf_rcEnv0` uses, rebuilt here rather than imported
because that file is a different stream's.  In the context `[svC's type]` the variable `.bvar 0`
and the spine `svC` are both proofs of the same proposition, so proof irrelevance identifies
them.

Read this the way `ForallInvPrice`'s control has to be read, in two halves: it **refutes** the
unguarded row (`varAppDisjNaive_false`), and it is **silent** on what this file declares — the
bridge's own `¬ IsProof` premise fails at the witness (`svEnv_isProof_bvar0`), so the witness is
outside `RigidShapeVUniq`'s scope, and `RigidShapeV.Compat` is not even consulted.  Unlike
`rogueSortPiEnv`, the witness here **is** `VEnv.WF`, so no `not_wf_…` half is needed or
possible: that is what makes this a hard constraint on the vocabulary rather than a control. -/

/-- `∀ X : Prop, X` — a closed proposition, `False`. -/
def svFalse : VExpr := .forallE (.sort .zero) (.bvar 0)

theorem svFalse_lift : svFalse.lift = svFalse := rfl

/-- `svFalse` is a type at `Sort (imax 1 0)`, over any environment and any `Γ`. -/
theorem svFalse_type {Γ : List VExpr} :
    env.HasType U Γ svFalse (.sort (.imax (.succ .zero) .zero)) :=
  .forallEDF (.sortDF trivial trivial rfl) (.bvar .zero)

/-- …and `imax _ 0 ≈ 0`, so it is a **proposition**. -/
theorem svFalse_prop {Γ : List VExpr} : env.HasType U Γ svFalse (.sort .zero) := by
  have hw : (VLevel.imax (.succ .zero) .zero).WF U := ⟨trivial, trivial⟩
  exact .defeqDF (.sortDF hw trivial VLevel.imax_zero) svFalse_type

/-- The axiom's name and signature. -/
def svC : Lean.Name := `Lean4Lean.shapeVarPropAxiom
def svCi : VConstant := ⟨0, svFalse⟩

/-- `VEnv.empty` plus the single axiom `svC : svFalse`, and **no rules**. -/
def svEnv : VEnv where
  constants n := if svC = n then some svCi else none
  defeqs _ := False

theorem svEnv_constants : svEnv.constants svC = some svCi := by simp [svEnv]

theorem addConst_svEnv : VEnv.empty.addConst svC svCi = some svEnv := by
  simp [VEnv.addConst, VEnv.empty, svEnv]

/-- **`svEnv` is `VEnv.WF`** — one `.axiom` step over the empty environment. -/
theorem wf_svEnv : VEnv.WF svEnv :=
  ⟨[.axiom ⟨svCi, svC⟩], .decl (.axiom ⟨_, svFalse_type⟩ addConst_svEnv) .empty⟩

/-- There are no rules, so every head is rule-free. -/
theorem ruleFreeHead_svEnv (c : Lean.Name) : svEnv.RuleFreeHead c :=
  fun _ h => absurd h not_false

theorem svCtx_onCtx : OnCtx [svFalse] (svEnv.IsType 0) := ⟨trivial, _, svFalse_type⟩

theorem svEnv_bvar0 : svEnv.HasType 0 [svFalse] (.bvar 0) svFalse :=
  .bvar (Lookup.zero' svFalse_lift)

theorem svEnv_const : svEnv.HasType 0 [svFalse] (.const svC []) svFalse :=
  .constDF svEnv_constants nofun nofun rfl .nil

/-- **A variable and a rule-free constant spine are convertible**, at a `VEnv.WF`
environment. -/
theorem svEnv_conv :
    svEnv.IsDefEqU 0 [svFalse] (.bvar 0) ((VExpr.const svC []).mkApp []) :=
  ⟨_, .proofIrrel svFalse_prop svEnv_bvar0 svEnv_const⟩

/-- The unguarded var/app row: `VarAppDisj` with the `¬ IsProof` premise deleted. -/
def VarAppDisjNaive (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {i : Nat} {c : Lean.Name} {ls : List VLevel} {as : List VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
    ¬ env.IsDefEqU U Γ (.bvar i) ((VExpr.const c ls).mkApp as)

/-- **Refuted.** -/
theorem varAppDisjNaive_false : ¬ VarAppDisjNaive svEnv 0 :=
  fun h => h svCtx_onCtx (ruleFreeHead_svEnv svC) svEnv_conv

/-- The control's second half: the bridge's own premise fails at the witness, so nothing here
touches `RigidShapeVUniq` or the guarded `VarAppDisj`. -/
theorem svEnv_isProof_bvar0 : svEnv.IsProof 0 [svFalse] (.bvar 0) :=
  ⟨_, svFalse_prop, svEnv_bvar0⟩

/-- …and it does not touch the var/**Π** row either: the witness's right endpoint is a constant
spine, and `VarPiDisj` at `svEnv` is not in question here. -/
theorem svEnv_witness_right_not_pi (A B : VExpr) :
    (VExpr.const svC []).mkApp [] ≠ .forallE A B := nofun

section Audit
#print axioms Lean4Lean.VEnv.RigidShape.toExpr_ne_bvar
#print axioms Lean4Lean.VEnv.SPShape.toExpr_ne_bvar
#print axioms Lean4Lean.VEnv.RigidShapeVUniq.rigidShapeUniq
#print axioms Lean4Lean.VEnv.RigidShapeVUniqNS.rigidShapeUniqNS
#print axioms Lean4Lean.VEnv.WF.instL_lhs_ne_bvar
#print axioms Lean4Lean.VEnv.varPiDisj_of_rigidShapeVUniq
#print axioms Lean4Lean.VEnv.codLift_bvar_absurd
#print axioms Lean4Lean.VEnv.PiCodLiftNeutral.of_noVar
#print axioms Lean4Lean.VEnv.piDescend_iff_neutralNV_sortConv
#print axioms Lean4Lean.VEnv.rigidShapeVUniq_of_family
#print axioms Lean4Lean.VEnv.RigidShapeVUniq.varSortDisj
#print axioms Lean4Lean.VEnv.varPiDisj_nil
#print axioms Lean4Lean.VEnv.bvar_row_reachable
#print axioms Lean4Lean.VEnv.varNoConf_false
#print axioms Lean4Lean.VEnv.varCtx3_conv
#print axioms Lean4Lean.VEnv.varCtx3_compat
#print axioms Lean4Lean.VEnv.varCtx3_isProof
#print axioms Lean4Lean.VEnv.wf_svEnv
#print axioms Lean4Lean.VEnv.svEnv_conv
#print axioms Lean4Lean.VEnv.varAppDisjNaive_false
#print axioms Lean4Lean.VEnv.svEnv_isProof_bvar0
#print axioms Lean4Lean.VEnv.RigidShapeVUniq.varAppDisj
#print axioms Lean4Lean.VEnv.rigidShapeVUniq_iff
-- §9 regression: these two must match the originals printed immediately after them
#print axioms Lean4Lean.VEnv.RigidShapeVUniqNS.rigidShapeUniq'
#print axioms Lean4Lean.VEnv.rigidShapeUniq_of_sortUniq
#print axioms Lean4Lean.VEnv.RigidShapeVUniqNS.piUniq
#print axioms Lean4Lean.VEnv.RigidShapeUniqNS.piUniq
end Audit

end VEnv
end Lean4Lean
