import Lean4Lean.Theory.Typing.SpineVar
import Lean4Lean.Theory.Typing.SortInvIndep

/-!
# `SpineVarVacuity`: §7 of the variable-headed **spine** entry, finished

`SpineVar.lean` states the `varApp i as` entry, reduces the variable slice of `PiCodLiftNeutral`'s
`.app` row to it (§4-§5), and prices it (§6, an `iff`).  Its §7 carries four of the checks
`docs/vacuity-ledger.md` §0 asks for.  **This file carries the rest**, and it is the part the
corner has already been burned on: one day before this file was written a draft shape entry in
this same corner was *vacuous* while printing a clean `[propext]` and measuring an empty hole
cone, and it was caught only because its author tried to **refute** his own row.

So the order here is: refute first, and only then report.

## What is here

* **§7.5** the check `SpineVar.lean` §7 does not run and which the vacuous draft failed: a
  **non-empty** variable spine, at a `VEnv.WF` environment, in an `OnCtx` context, that is
  **not a proof**.  Without it every non-empty spine could have been a proof, `SpineVarAppDisj`'s
  `¬ IsProof` guard would exclude the whole slice the entry adds, and the entry would be
  `ShapeVar.lean`'s bare-variable entry under a new name.  Two routes: one tainted and
  unconditional, one hole-free and conditional on `PropAgreeOn` — **the second matters**, because
  the unconditional route runs through `IsType.not_isProof`, i.e. through
  `forallE_inv_stratified`, which is the very hole §4's reduction is measured against.
* **§7.6** the consumer-side firing test: a concrete instance of the row §5 deletes with **six of
  its seven premises discharged** — the seventh is the conversion, which is what the deletion
  refutes — and the deletion firing on it.
* **§7.7** the refutation attempt, per row, as theorems: the three mechanisms that have actually
  killed rows in this corner (proof irrelevance, δ, β/η) are each shown blocked or shown to be
  exactly what a guard pays for.  What is left is `trans`, for all three rows.
* **§7.8** what that residual *is*, machine-checked: **any** counterexample to the Π row factors
  through a midpoint that is neither variable-spine-headed nor a Π.  This is a derived property
  of an existentially quantified midpoint, **not** a syntactic condition imposed on one — see the
  note in §7.8 on ledger rows 94/94a.
* **§7.9** the two hard constraints, checked properly: at *both* refuting witnesses, **every**
  midpoint of the offending conversion is a proof, so neither witness refutes the extended bridge
  — the bridge's premise fails not merely at the midpoint the witness picked but at all of them.
  `SpineVar.lean` §7.3/§7.4 check one midpoint each; this is the general statement.
* **§7.10** the midpoint question, answered with a **term** instead of a read-off: a β-redex
  midpoint at a `varApp` endpoint, with every premise that mentions the midpoint satisfied.
* **§7.11** the **fourth** thing the entry adds — the `RuleFree` entry `varApp _ _ => True`, which
  is a theorem here and not a convention — and the grade, as one statement.
* **§7.12** what the witness environments actually contain, machine-checked, including a proof
  (not an assertion) that `svEnv` is inconsistent and that no witness here declares `univInhab`.

## Inhabitation and hole-freeness, stated separately

*Inhabitation.*  §7.5, §7.6 and §7.9 exhibit typed terms in `OnCtx` contexts at `VEnv.WF`
environments; §7.6's instance discharges six of the seven premises of the deleted row.

*Hole-freeness.*  Measured in the audit block, not asserted.  Every declaration here is
`[propext]`, `[propext, Quot.sound]`, `[propext, Classical.choice, Quot.sound]` or no axioms at
all — **hole-free** —
**except exactly four**: `spineVar_not_isProof` (via `IsType.not_isProof`), `spineVarPi_midpoint`
(via `IsDefEq.strong`), `not_isProof_fun_of_not_isProof_app` (via `IsProof.app'`) and
`spineVar_grade` (via §6's `iff`, i.e. §4's reduction).  All four reach the same single hole,
`IsDefEqU.forallE_inv_stratified`.  Two of the four have hole-free doubles here:
`spineVar_not_isProof_of_propAgreeOn` and `spineVarPi_midpoint_aux` — and getting the second of
those hole-free took hypothesising `SortUniq` after the audit showed the draft printing `sorryAx`
through `WF.sortUniq'`.  Hole-freeness is *not* discharge: the extended bridge
`RigidShapeVSUniq` is a **hypothesis** everywhere it appears, and a hypothesis is invisible to
both `#print axioms` and the hole cone (`docs/vacuity-ledger.md` §0, third instrument).

*Witness environments.*  Two are used.  `VEnv.empty` (§7.5, §7.6, §7.8's corollary) declares
nothing.  `svEnv` (`ShapeVar.lean` §10, used in §7.9) is `VEnv.empty` plus the single **axiom**
`svC : ∀ X : Prop, X` — a proof of every proposition, so `svEnv` is `VEnv.WF` **and logically
inconsistent**.  That is deliberate and harmless in a refutation: a row that must hold at every
`VEnv.WF` environment is refuted by any `VEnv.WF` counterexample, consistent or not.  It is worth
being exact about which inconsistency this is: `svEnv`'s axiom is *propositional*, and no witness
in this file or in `SpineVar.lean` or `ShapeVar.lean` declares the corner's other inconsistent
witness `univInhab : ∀ (α : Sort u), α` (`docs/handoff-weakn.md` §…, `handoff-gatebody.md`) — that
one belongs to the weakening/strengthening stream, not to this one.  §7.3's context assumes
`∀ X : Prop, X` twice, but as a **context hypothesis** over `VEnv.empty`, so the *environment*
there is consistent.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §7.5 A non-empty variable spine that is not a proof

`SpineVar.lean` §7.3 and §7.4 both exhibit non-empty variable spines that **are** proofs — that is
what makes them refutations.  Nothing there exhibits one that is not, and without such a witness
the entry is indistinguishable from a rename: `SpineVarAppDisj`'s guard and the bridge's own
`¬ IsProof` premise would exclude every non-empty spine, leaving only `varApp i []`, which *is*
`RigidShapeV.var i`.

The witness is §7.2's: over `VEnv.empty`, in `spCtx = [f a, Prop, Prop → Prop]`, the spine
`f a = .app (.bvar 2) (.bvar 1)` is a **type**, and a type is not a proof. -/

/-- The witness spine is typed at `Prop`, i.e. it is a type. -/
theorem spineVar_hasType_prop :
    (∅ : VEnv).HasType 0 spCtx (.app (.bvar 2) (.bvar 1)) (.sort .zero) :=
  HasType.app (.bvar (.succ (.succ (Lookup.zero' propFn_lift)))) (.bvar (.succ (Lookup.zero' rfl)))

theorem spineVar_isType : (∅ : VEnv).IsType 0 spCtx (.app (.bvar 2) (.bvar 1)) :=
  ⟨_, spineVar_hasType_prop⟩

/-- **A non-empty variable spine that is not a proof.**  Unconditional, but *tainted*: it goes
through `IsType.not_isProof`, whose cone contains `IsDefEqU.forallE_inv_stratified` — the same
hole §4's reduction is measured against, so this route alone would make the non-vacuity check
circular.  §7.5's second route removes that. -/
theorem spineVar_not_isProof : ¬ (∅ : VEnv).IsProof 0 spCtx (.app (.bvar 2) (.bvar 1)) :=
  IsType.not_isProof ⟨[], .empty⟩ spCtx_onCtx spineVar_isType

/-- **The same, hole-free, from an independent node.**  `PropAgreeOn` (`SortInvIndep.lean` §1) is
the "propositionhood of a term's type is invariant" node of the *other* axis of this corner; it
is not the bridge and not `forallE_inv_stratified`.  Given it, the witness's non-proofhood is
four lines and carries no `sorryAx`: the spine's type is `Prop`, `Prop`'s type is `Sort 1`, a
proof's type would be at `Sort 0`, and `1 = 0` is false. -/
theorem spineVar_not_isProof_of_propAgreeOn (hT : PropAgreeOn (∅ : VEnv) 0) :
    ¬ (∅ : VEnv).IsProof 0 spCtx (.app (.bvar 2) (.bvar 1)) := by
  rintro ⟨p, hp0, hep⟩
  have h := hT (ls := []) (u := .succ .zero) (u' := .zero) spCtx_onCtx trivial trivial
    spineVar_hasType_prop hep (HasType.sort trivial) hp0
  simp [VLevel.eval] at h

/-- **So the guard does not eat the slice.**  Assembled: the spine is non-empty, its head is a
variable, it is a type, something is convertible to it (itself), and it is not a proof — so
`SpineVarAppDisj`'s `¬ IsProof` guard and the bridge's `¬ IsProof` premise are both satisfiable
at a **non-empty** spine.  Conditional on the independent node, hence hole-free. -/
theorem spineVar_guard_not_vacuous (hT : PropAgreeOn (∅ : VEnv) 0) :
    (∅ : VEnv).WF ∧ OnCtx spCtx ((∅ : VEnv).IsType 0) ∧
      (RigidShapeVS.varApp 2 [.bvar 1]).toExpr = .app (VExpr.bvar 2) (.bvar 1) ∧
      (∀ as : List VExpr, (RigidShapeVS.varApp 2 as).toExpr = .app (VExpr.bvar 2) (.bvar 1) →
        as ≠ []) ∧
      (∅ : VEnv).HasType 0 spCtx (.app (.bvar 2) (.bvar 1)) (.sort .zero) ∧
      ¬ (∅ : VEnv).IsProof 0 spCtx (.app (.bvar 2) (.bvar 1)) :=
  ⟨⟨[], .empty⟩, spCtx_onCtx, rfl, fun as h => by
      rintro rfl; exact absurd h nofun,
   spineVar_hasType_prop, spineVar_not_isProof_of_propAgreeOn hT⟩

/-! ## §7.6 The consumer fires, with every premise but the conversion discharged

`SpineVar.lean` §7.2 shows the deleted slice is *reachable* on its type side.  That is not yet a
firing test for the deletion: `PiCodLiftNeutral`'s row has seven premises, and a slice deletion is
only worth something if the other seven are simultaneously satisfiable at a type whose spine head
is a variable and whose spine is **non-empty**.  They are.  The seventh premise is the conversion, and
the conversion is exactly what the deletion refutes — so it is the one premise that is named
rather than discharged, as a firing test is allowed exactly one. -/

/-- `Γ'` for the lift: one extra `Prop` in front of `spCtx`. -/
def spCtx' : List VExpr := .sort .zero :: spCtx

theorem spCtx'_onCtx : OnCtx spCtx' ((∅ : VEnv).IsType 0) := ⟨spCtx_onCtx, _, .sort trivial⟩

/-- **Six of the seven premises of the deleted row, at one instance.**  `n = 1`, `k = 0`,
`Γ = spCtx`, `Γ' = Prop :: spCtx`, `T = f a` (a **non-empty** variable spine), `f = .bvar 0`,
`a = .bvar 1`, `S = Prop`.  The seventh premise — the conversion `T.liftN 1 0 ≡ Π …` — is
`spineVar_row_fires`'s subject.

The last two conjuncts are the discrimination: `PiCodLiftNeutralNV`'s guard (`ShapeVar.lean` §6)
**admits** this row, `PiCodLiftNeutralNVS`'s rejects it. -/
theorem spineVar_row_premises :
    Ctx.LiftN 1 0 spCtx spCtx' ∧ OnCtx spCtx ((∅ : VEnv).IsType 0) ∧
      OnCtx spCtx' ((∅ : VEnv).IsType 0) ∧
      (VExpr.app (.bvar 2) (.bvar 1)).PiDescendNeutral ∧
      (∅ : VEnv).HasType 0 spCtx (.bvar 0) (.app (.bvar 2) (.bvar 1)) ∧
      (∅ : VEnv).HasType 0 spCtx (.bvar 1) (.sort .zero) ∧
      (VExpr.app (.bvar 2) (.bvar 1) = (VExpr.bvar 2).mkApp [.bvar 1]) ∧
      (∀ i, VExpr.app (.bvar 2) (.bvar 1) ≠ .bvar i) ∧
      (VExpr.app (.bvar 2) (.bvar 1)).spineHead = .bvar 2 :=
  ⟨.one, spCtx_onCtx, spCtx'_onCtx, trivial, .bvar (Lookup.zero' rfl),
   .bvar (.succ (Lookup.zero' rfl)), rfl, nofun, rfl⟩

/-- **…and the deletion fires on it.**  Given the row §4 reduces to the extended bridge, the
eighth premise is impossible at this instance, for **every** codomain `B`.  Hole-free
(`codLift_spineVar_absurd` is `[propext]`); the hypothesis `H` is the bridge's price. -/
theorem spineVar_row_fires (H : SpineVarPiDisj (∅ : VEnv) 0) (B : VExpr) :
    ¬ (∅ : VEnv).IsDefEqU 0 spCtx' ((VExpr.app (.bvar 2) (.bvar 1)).liftN 1 0)
        (.forallE ((VExpr.sort .zero).liftN 1 0) B) :=
  fun hconv => codLift_spineVar_absurd H spCtx'_onCtx (i := 2) rfl hconv

/-! ## §7.7 The refutation attempt, per row

Three mechanisms have actually falsified rows in this corner: **proof irrelevance** (it killed the
bare diagonal, `ShapeVar.lean` §8, and the unguarded var/app row, §10, and their spine versions,
`SpineVar.lean` §7.3/§7.4), **δ** (a rule rewriting one of the two shapes), and **β/η** (a redex
masquerading as a rigid shape — `docs/vacuity-ledger.md` rows 94/94a and 100-103, eleven
collapses).  For each row the extension adds, here is what happened when they were tried.

| row | proof irrelevance | δ | β/η | left |
| --- | --- | --- | --- | --- |
| `varApp`/`varApp` (diagonal) | **fires** — refutes `i = j`, §7.3; entry is `True` | — | — | nothing |
| `varApp`/`pi` | blocked: a Π is not a proof | blocked: no rule side has a variable spine head | blocked: a variable spine is not a redex and not a λ | `trans` |
| `varApp`/`sort` | blocked: a sort is not a proof | blocked, same | blocked, same | `trans` |
| `varApp`/`app` | **fires** unguarded (§7.4); the `¬ IsProof` guard is what buys it | blocked, both sides | blocked, same | `trans` |

So: **no row of the extension was refuted, and two of the four naive readings of them were.**
What is left, for all three off-diagonal rows, is the `trans` case — §7.8 says what that is. -/

/-- **Proof irrelevance cannot refute the Π row**: a Π is never a proof.  (`SortUniq` is a
hypothesis rather than `WF.sortUniq'` so that this stays hole-free.) -/
theorem forallE_not_isProof (hsu : env.SortUniq U) (hord : Ordered env) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {A B : VExpr} : ¬ env.IsProof U Γ (.forallE A B) :=
  fun ⟨_, hp, hf⟩ => forallE_not_proof hsu hord hΓ hp hf

/-- **…nor the sort row**: a sort is never a proof. -/
theorem sort_not_isProof (hsu : env.SortUniq U) (hord : Ordered env) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {u : VLevel} : ¬ env.IsProof U Γ (.sort u) :=
  fun ⟨_, hp, hf⟩ => sort_not_proof hsu hord hΓ hp hf

/-- **What the app row's guard buys, exactly.**  Proof irrelevance *does* fire there (§7.4), and
the only thing that blocks it is the guard: the `proofIrrel` constructor's premises for a term
*are* a proof of `IsProof` of it. -/
theorem isProof_of_proofIrrel_premises {Γ : List VExpr} {p e : VExpr}
    (hp : env.HasType U Γ p (.sort .zero)) (he : env.HasType U Γ e p) : env.IsProof U Γ e :=
  ⟨_, hp, he⟩

/-- **δ cannot refute any of the three rows**, on either side of the rule.  This is
`SpineVarClosed.lean` §2 assembled as the mechanism check. -/
theorem spineVar_delta_blocked (henv : env.WF) {df : VDefEq} (h : env.defeqs df)
    (ls : List VLevel) (i : Nat) :
    (df.lhs.instL ls).spineHead ≠ .bvar i ∧ (df.rhs.instL ls).spineHead ≠ .bvar i :=
  ⟨henv.instL_lhs_spineHead_ne_bvar h ls i, henv.instL_rhs_spineHead_ne_bvar h ls i⟩

/-- **β cannot refute any of them either**: a term whose spine head is a variable is not a
β-redex.  Note this is a statement about the *spine head*, and it is where `spineHead` earns its
place over a head-constructor test — a β-redex's head constructor **is** `.app`, exactly like a
variable spine's. -/
theorem spineHead_bvar_ne_beta {e : VExpr} {i : Nat} (h : e.spineHead = .bvar i)
    (A b a : VExpr) : e ≠ .app (.lam A b) a := by
  rintro rfl; exact absurd h nofun

/-- **…and η cannot**: nor is it a λ. -/
theorem spineHead_bvar_ne_lam {e : VExpr} {i : Nat} (h : e.spineHead = .bvar i)
    (A b : VExpr) : e ≠ .lam A b := by
  rintro rfl; exact absurd h nofun

/-- **The attempt, assembled, for the Π and sort rows.**  All three mechanisms blocked at once,
at any `VEnv.WF` environment with `SortUniq` (which `WF.sortUniq'` supplies, at the cost of the
hole — hence the hypothesis form). -/
theorem spineVar_mechanisms_blocked (henv : env.WF) (hsu : env.SortUniq U) {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {e : VExpr} {i : Nat} (h : e.spineHead = .bvar i)
    {A B : VExpr} {u : VLevel} :
    ¬ env.IsProof U Γ (.forallE A B) ∧ ¬ env.IsProof U Γ (.sort u) ∧
      (∀ (df : VDefEq), env.defeqs df → ∀ ls j, (df.lhs.instL ls).spineHead ≠ .bvar j ∧
        (df.rhs.instL ls).spineHead ≠ .bvar j) ∧
      (∀ A' b a, e ≠ .app (.lam A' b) a) ∧ (∀ A' b, e ≠ .lam A' b) :=
  ⟨forallE_not_isProof hsu henv.ordered hΓ, sort_not_isProof hsu henv.ordered hΓ,
   fun _ hdf ls j => spineVar_delta_blocked henv hdf ls j,
   fun A' b a => spineHead_bvar_ne_beta h A' b a, fun A' b => spineHead_bvar_ne_lam h A' b⟩

/-! ## §7.8 What the residual is: the midpoint of any counterexample, machine-checked

§7.7 leaves one mechanism unblocked for each of the three off-diagonal rows: `trans`.  That is not
a confession of ignorance — it can be said exactly what a counterexample would have to look like,
and here it is for the Π row.  Every case of the thirteen-case `IsDefEqStrong` induction except
`trans` is *closed*, so any counterexample factors through a `trans`, and at a `trans` the two
inductive hypotheses force the midpoint to be neither a variable-headed spine nor a Π: if it were
the first, the right half is a smaller counterexample; if the second, the left half is.

**This is a derived property of an existentially quantified midpoint, not a syntactic condition
imposed on one.**  `docs/vacuity-ledger.md` rows 94/94a and 100-103 (eleven collapses) say no
syntactic *hypothesis* on a `trans` midpoint can localise anything, because β manufactures a
midpoint of any shape.  Nothing here hypothesises anything about a midpoint: the statement
*concludes* that the midpoint of a hypothetical counterexample avoids two shapes, and the shape
the ledger says β can always manufacture — a redex, whose spine head is a `.lam` — is precisely
one of the shapes this conclusion **permits**.  So this theorem is consistent with those eleven
collapses by construction, and it is not a twelfth: it constrains no midpoint and localises
nothing; it names where a refutation would have to live. -/

/-- **The `trans`-residual of the Π row, as a theorem.**  Hole-free — but only with `SortUniq`
hypothesised.  Measured, not assumed: the first draft of this lemma called `WF.sortUniq' henv` in
the `proofIrrel` case and printed `sorryAx`, because that theorem's cone reaches
`forallE_inv_stratified`; taking `SortUniq` as a hypothesis (the discipline `PiLevelPin.lean` and
`Injectivity.not_isProof_of_forallE'` use) removes it.  Nothing else here calls `IsDefEq.strong`,
so the statement over `IsDefEqStrong` really is the hole-free content.  `Classical.choice` enters
only through the two `by_cases`. -/
theorem spineVarPi_midpoint_aux (henv : env.WF) (hsu : env.SortUniq U) :
    ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr},
    env.IsDefEqStrong U Γ e₁ e₂ T → OnCtx Γ (env.IsType U) → ∀ (i : Nat) (P Q : VExpr),
      ((e₁.spineHead = .bvar i ∧ e₂ = .forallE P Q) ∨
        (e₂.spineHead = .bvar i ∧ e₁ = .forallE P Q)) →
      ∃ m : VExpr, env.IsDefEq U Γ e₁ m T ∧ env.IsDefEq U Γ m e₂ T ∧
        (∀ j, m.spineHead ≠ .bvar j) ∧ (∀ P' Q', m ≠ .forallE P' Q') := by
  intro Γ e₁ e₂ T HH
  induction HH with
  | symm _ ih =>
    intro hΓ' i P Q h
    obtain ⟨m, h1, h2, hp1, hp2⟩ := ih hΓ' i P Q h.symm
    exact ⟨m, h2.symm, h1.symm, hp1, hp2⟩
  | defeqDF _ hAB _ _ ih =>
    intro hΓ' i P Q h
    obtain ⟨m, h1, h2, hp1, hp2⟩ := ih hΓ' i P Q h
    exact ⟨m, .defeqDF hAB.defeq h1, .defeqDF hAB.defeq h2, hp1, hp2⟩
  | @trans Γ' a mid T' b hd1 hd2 ih1 ih2 =>
    rintro hΓ' i P Q (⟨hsh, rfl⟩ | ⟨hsh, rfl⟩)
    · by_cases hb : ∃ j, mid.spineHead = .bvar j
      · obtain ⟨j, hj⟩ := hb
        obtain ⟨m, h1, h2, hp1, hp2⟩ := ih2 hΓ' j P Q (.inl ⟨hj, rfl⟩)
        exact ⟨m, hd1.defeq.trans h1, h2, hp1, hp2⟩
      · by_cases hf : ∃ P' Q', mid = .forallE P' Q'
        · obtain ⟨P', Q', rfl⟩ := hf
          obtain ⟨m, h1, h2, hp1, hp2⟩ := ih1 hΓ' i P' Q' (.inl ⟨hsh, rfl⟩)
          exact ⟨m, h1, h2.trans hd2.defeq, hp1, hp2⟩
        · exact ⟨mid, hd1.defeq, hd2.defeq, fun j hj => hb ⟨j, hj⟩,
            fun P' Q' h => hf ⟨P', Q', h⟩⟩
    · by_cases hb : ∃ j, mid.spineHead = .bvar j
      · obtain ⟨j, hj⟩ := hb
        obtain ⟨m, h1, h2, hp1, hp2⟩ := ih1 hΓ' j P Q (.inr ⟨hj, rfl⟩)
        exact ⟨m, h1, h2.trans hd2.defeq, hp1, hp2⟩
      · by_cases hf : ∃ P' Q', mid = .forallE P' Q'
        · obtain ⟨P', Q', rfl⟩ := hf
          obtain ⟨m, h1, h2, hp1, hp2⟩ := ih2 hΓ' i P' Q' (.inr ⟨hsh, rfl⟩)
          exact ⟨m, hd1.defeq.trans h1, h2, hp1, hp2⟩
        · exact ⟨mid, hd1.defeq, hd2.defeq, fun j hj => hb ⟨j, hj⟩,
            fun P' Q' h => hf ⟨P', Q', h⟩⟩
  | proofIrrel h1 h2 h3 _ _ _ =>
    rintro hΓ' i P Q (⟨-, rfl⟩ | ⟨-, rfl⟩)
    · exact (forallE_not_proof hsu henv.ordered hΓ'
        h1.defeq.hasType.1 h3.defeq.hasType.1).elim
    · exact (forallE_not_proof hsu henv.ordered hΓ'
        h1.defeq.hasType.1 h2.defeq.hasType.1).elim
  | extra h1 =>
    rintro _ i P Q (⟨he, -⟩ | ⟨-, hf⟩)
    · exact (henv.instL_lhs_spineHead_ne_bvar h1 _ _ he).elim
    · exact (henv.instL_lhs_ne_forallE h1 _ _ _ hf).elim
  | bvar _ _ _ | sortDF _ _ _ | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _
  | lamDF _ _ _ _ _ _ _ =>
    rintro _ i P Q (⟨-, hf⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
  | forallEDF _ _ _ _ _ =>
    rintro _ i P Q (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact absurd hf nofun
  | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
    rintro _ i P Q (⟨hf, -⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun

/-- **Any counterexample to `SpineVarPiDisj` has a midpoint that is neither a variable-headed
spine nor a Π** — the `IsDefEqU` form, which is the form the row is stated in.  Carries
`sorryAx` through `IsDefEq.strong` only (`forallE_inv_stratified`), exactly like §4's reduction;
`spineVarPi_midpoint_aux` above is the hole-free content. -/
theorem spineVarPi_midpoint (henv : env.WF) {Γ : List VExpr} {e A B : VExpr} {i : Nat}
    (hΓ : OnCtx Γ (env.IsType U)) (hsh : e.spineHead = .bvar i)
    (h : env.IsDefEqU U Γ e (.forallE A B)) :
    ∃ (m T : VExpr), env.IsDefEq U Γ e m T ∧ env.IsDefEq U Γ m (.forallE A B) T ∧
      (∀ j, m.spineHead ≠ .bvar j) ∧ (∀ A' B', m ≠ .forallE A' B') := by
  obtain ⟨T, hd⟩ := h
  obtain ⟨m, h1, h2, hp1, hp2⟩ :=
    spineVarPi_midpoint_aux henv (WF.sortUniq' henv) (hd.strong henv.ordered hΓ) hΓ i A B
      (.inl ⟨hsh, rfl⟩)
  exact ⟨m, T, h1, h2, hp1, hp2⟩

/-- **The same residual for the sort row.**  A near-copy: `sort_not_proof` replaces
`forallE_not_proof` and `instL_lhs_ne_sort` replaces `instL_lhs_ne_forallE`.  It is spelled out
rather than claimed, because "the same proof works" is how a row gets committed unchecked. -/
theorem spineVarSort_midpoint_aux (henv : env.WF) (hsu : env.SortUniq U) :
    ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr},
    env.IsDefEqStrong U Γ e₁ e₂ T → OnCtx Γ (env.IsType U) → ∀ (i : Nat) (u : VLevel),
      ((e₁.spineHead = .bvar i ∧ e₂ = .sort u) ∨ (e₂.spineHead = .bvar i ∧ e₁ = .sort u)) →
      ∃ m : VExpr, env.IsDefEq U Γ e₁ m T ∧ env.IsDefEq U Γ m e₂ T ∧
        (∀ j, m.spineHead ≠ .bvar j) ∧ (∀ v, m ≠ .sort v) := by
  intro Γ e₁ e₂ T HH
  induction HH with
  | symm _ ih =>
    intro hΓ' i u h
    obtain ⟨m, h1, h2, hp1, hp2⟩ := ih hΓ' i u h.symm
    exact ⟨m, h2.symm, h1.symm, hp1, hp2⟩
  | defeqDF _ hAB _ _ ih =>
    intro hΓ' i u h
    obtain ⟨m, h1, h2, hp1, hp2⟩ := ih hΓ' i u h
    exact ⟨m, .defeqDF hAB.defeq h1, .defeqDF hAB.defeq h2, hp1, hp2⟩
  | @trans Γ' a mid T' b hd1 hd2 ih1 ih2 =>
    rintro hΓ' i u (⟨hsh, rfl⟩ | ⟨hsh, rfl⟩)
    · by_cases hb : ∃ j, mid.spineHead = .bvar j
      · obtain ⟨j, hj⟩ := hb
        obtain ⟨m, h1, h2, hp1, hp2⟩ := ih2 hΓ' j u (.inl ⟨hj, rfl⟩)
        exact ⟨m, hd1.defeq.trans h1, h2, hp1, hp2⟩
      · by_cases hf : ∃ v, mid = .sort v
        · obtain ⟨v, rfl⟩ := hf
          obtain ⟨m, h1, h2, hp1, hp2⟩ := ih1 hΓ' i v (.inl ⟨hsh, rfl⟩)
          exact ⟨m, h1, h2.trans hd2.defeq, hp1, hp2⟩
        · exact ⟨mid, hd1.defeq, hd2.defeq, fun j hj => hb ⟨j, hj⟩, fun v h => hf ⟨v, h⟩⟩
    · by_cases hb : ∃ j, mid.spineHead = .bvar j
      · obtain ⟨j, hj⟩ := hb
        obtain ⟨m, h1, h2, hp1, hp2⟩ := ih1 hΓ' j u (.inr ⟨hj, rfl⟩)
        exact ⟨m, h1, h2.trans hd2.defeq, hp1, hp2⟩
      · by_cases hf : ∃ v, mid = .sort v
        · obtain ⟨v, rfl⟩ := hf
          obtain ⟨m, h1, h2, hp1, hp2⟩ := ih2 hΓ' i v (.inr ⟨hsh, rfl⟩)
          exact ⟨m, hd1.defeq.trans h1, h2, hp1, hp2⟩
        · exact ⟨mid, hd1.defeq, hd2.defeq, fun j hj => hb ⟨j, hj⟩, fun v h => hf ⟨v, h⟩⟩
  | proofIrrel h1 h2 h3 _ _ _ =>
    rintro hΓ' i u (⟨-, rfl⟩ | ⟨-, rfl⟩)
    · exact (sort_not_proof hsu henv.ordered hΓ' h1.defeq.hasType.1 h3.defeq.hasType.1).elim
    · exact (sort_not_proof hsu henv.ordered hΓ' h1.defeq.hasType.1 h2.defeq.hasType.1).elim
  | extra h1 =>
    rintro _ i u (⟨he, -⟩ | ⟨-, hf⟩)
    · exact (henv.instL_lhs_spineHead_ne_bvar h1 _ _ he).elim
    · exact (henv.instL_lhs_ne_sort h1 _ _ hf).elim
  | bvar _ _ _ | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _
  | lamDF _ _ _ _ _ _ _ | forallEDF _ _ _ _ _ =>
    rintro _ i u (⟨-, hf⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
  | sortDF _ _ _ =>
    rintro _ i u (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact absurd hf nofun
  | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
    rintro _ i u (⟨hf, -⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun

/-- **The app row's residual is *not* just `trans`, and that is worth saying.**  For the Π and sort
rows every case but `trans` closes outright.  For the variable-spine / constant-spine row `appDF`
does **not**: both endpoints are `.app`s there, so it closes only by peeling one argument off each
spine and recursing, threading `¬ IsProof` down with `IsProof.app'`
(`SpineVar.lean` §6, `RigidShapeVSUniq.spineVarAppDisj`).  So the app row's residual is
`trans` **plus** that recursion — which terminates, but on the spine, not on the derivation.
Recorded here rather than in prose because the two rows really are not the same shape of argument;
`ShapeVar.lean`'s bare-variable row escaped `appDF` entirely.  Three theorems: `appDF` is
*vacuous* on the Π and sort rows, because a Π and a sort are not applications; it is *reachable*
on the app row, because a non-empty constant spine is one; and what closes it there is the guard
descending the spine. -/
theorem forallE_sort_ne_app (P Q f a : VExpr) (u : VLevel) :
    (VExpr.forallE P Q ≠ .app f a) ∧ (VExpr.sort u ≠ .app f a) := ⟨nofun, nofun⟩

/-- …but a **non-empty constant spine is** an `.app`, so `appDF` is reachable for the app row. -/
theorem mkApp_cons_eq_app : ∀ (as : List VExpr) (f a : VExpr),
    ∃ g b, f.mkApp (a :: as) = .app g b
  | [], f, a => ⟨f, a, rfl⟩
  | c :: cs, f, a => mkApp_cons_eq_app cs (.app f a) c

/-- …and this is the step that closes it: the guard **descends the spine**.  Contrapositive of
`IsProof.app'`, which is what `RigidShapeVSUniq.spineVarAppDisj`'s `appDF` case threads.  Carries
`IsProof.app'`'s taint (`WF.uniq'`), which is why the app row is the expensive one. -/
theorem not_isProof_fun_of_not_isProof_app {Γ : List VExpr} {A B f a : VExpr} {u v : VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.HasType U Γ A (.sort u)) (hB : env.HasType U (A::Γ) B (.sort v))
    (hf : env.HasType U Γ f (.forallE A B)) (ha : env.HasType U Γ a A)
    (h : ¬ env.IsProof U Γ (.app f a)) : ¬ env.IsProof U Γ f :=
  fun hp => h (hp.app' henv hΓ hA hB hf ha)

/-! ## §7.9 The two hard constraints, checked at **every** midpoint

`SpineVar.lean` §7.3 and §7.4 refute the naive diagonal and the unguarded app row, and then check
that the extended bridge is not refuted *by exhibiting one midpoint at which its premise fails*
(`spDiagCtx_isProof`, `spAppCtx_isProof`).  That is the weaker check: the bridge quantifies over
the midpoint, so a witness refutes it as soon as **some** admissible midpoint is not a proof.
Here is the full check — at both witnesses every term convertible to the offending variable spine
is a proof, so the bridge's `¬ IsProof` premise fails at all of them at once.

Both are hole-free given `ProofTransport`, which is this corner's named hypothesis form for
"proof-ness travels along a conversion" (`Injectivity.lean:717`); its only in-tree inhabitant,
`WF.proofTransport`, is tainted by `forallE_inv_stratified`, which is exactly why the hypothesis
form exists. -/

/-- **Hard constraint 1 does not refute the bridge**: at §7.3's witness, *every* term convertible
to `F P` is a proof. -/
theorem spDiagCtx_isProof_of_conv (htr : (∅ : VEnv).ProofTransport 0) {e : VExpr}
    (h : (∅ : VEnv).IsDefEqU 0 spDiagCtx e (.app (.bvar 1) (.bvar 2))) :
    (∅ : VEnv).IsProof 0 spDiagCtx e :=
  htr spDiagCtx_onCtx h.symm spDiagCtx_isProof

/-- **Hard constraint 2 does not refute the bridge**: at §7.4's witness, likewise — so no choice
of midpoint turns that refutation of the *unguarded* row into a refutation of the bridge. -/
theorem spAppCtx_isProof_of_conv (htr : svEnv.ProofTransport 0) {e : VExpr}
    (h : svEnv.IsDefEqU 0 spAppCtx e (.app (.bvar 0) (.bvar 1))) :
    svEnv.IsProof 0 spAppCtx e :=
  htr spAppCtx_onCtx h.symm spAppCtx_isProof

/-- **The bridge instance at §7.4's shapes has no admissible midpoint at all.**  Spelled out in
the bridge's own vocabulary: for every `e` and `T`, if `e` is convertible to the variable spine at
type `T` then `e` is a proof, i.e. `RigidShapeVSUniq`'s premise `¬ IsProof e` is unsatisfiable
there.  The `varApp`/`app` row of `RigidShapeVS.Compat` is therefore never *invoked* at this
witness, refuted or otherwise. -/
theorem spAppCtx_no_bridge_instance (htr : svEnv.ProofTransport 0) {e T : VExpr}
    (h : svEnv.IsDefEq 0 spAppCtx e (RigidShapeVS.varApp 0 [.bvar 1]).toExpr T) :
    svEnv.IsProof 0 spAppCtx e :=
  spAppCtx_isProof_of_conv htr ⟨T, h⟩

/-- **And the diagonal entry really is unconditional**: `Compat` on two `varApp` shapes is `True`
for *all* heads and *all* spines, which is what §7.3 forces.  Stated so that the value of the
entry is on the record next to the refutation that pins it. -/
theorem rigidShapeVS_compat_varApp_diag {Γ : List VExpr} (i j : Nat) (as as' : List VExpr) :
    RigidShapeVS.Compat env U Γ (.varApp i as) (.varApp j as') := trivial

/-! ## §7.10 Does the entry constrain a `trans` midpoint?  No — and here is the redex

The question `docs/vacuity-ledger.md` rows 94/94a and 100-103 make mandatory.  `SpineVar.lean`'s
answer is a read-off of the definitions: `RigidShapeVS` values occur in `RigidShapeVSUniq` only as
the endpoints `s₁`, `s₂`.  That is correct but unmeasured, so here is the measured version: **the
midpoint of a bridge instance whose endpoint is a non-empty variable spine can be a β-redex**, at
`VEnv.WF`, with every premise that mentions the midpoint satisfied.

That is the ledger's own mechanism, exhibited rather than argued: β manufactures a midpoint of any
shape, so no syntactic condition on the midpoint could have survived — and the entry imposes none,
which is why it is not the twelfth collapse. -/

/-- `(λ x : Prop, x) (f a)` in `spCtx` — a β-redex whose spine head is a `.lam`. -/
def spRedex : VExpr := .app (.lam (.sort .zero) (.bvar 0)) (.app (.bvar 2) (.bvar 1))

theorem spRedex_spineHead : spRedex.spineHead = .lam (.sort .zero) (.bvar 0) := rfl

/-- **The redex is convertible to the variable spine**, at `VEnv.empty`, by β. -/
theorem spRedex_conv : (∅ : VEnv).IsDefEq 0 spCtx spRedex (.app (.bvar 2) (.bvar 1))
    (.sort .zero) :=
  .beta (.bvar (Lookup.zero' rfl)) spineVar_hasType_prop

theorem spRedex_hasType : (∅ : VEnv).HasType 0 spCtx spRedex (.sort .zero) :=
  spRedex_conv.hasType.1

/-- **A `trans` midpoint of any shape is available at a `varApp` endpoint.**  Every premise of
`RigidShapeVSUniq` that mentions the midpoint `e` is satisfied by the redex — the context is
`OnCtx`, the redex is not a proof, the shape `varApp 2 [.bvar 1]` is `RuleFree`, and the redex is
convertible to it at a common type — while the redex's spine head is a `.lam`, i.e. neither of the
two shapes §7.8 excludes for a *counterexample's* midpoint.

So the entry constrains **no** midpoint, and §7.8's conclusion is exactly compatible with the
ledger: the shape it leaves open for a hypothetical counterexample's midpoint is the shape β
actually produces. -/
theorem spineVar_midpoint_unconstrained (hT : PropAgreeOn (∅ : VEnv) 0) :
    OnCtx spCtx ((∅ : VEnv).IsType 0) ∧ ¬ (∅ : VEnv).IsProof 0 spCtx spRedex ∧
      RigidShapeVS.RuleFree (∅ : VEnv) (.varApp 2 [.bvar 1]) ∧
      (∅ : VEnv).IsDefEq 0 spCtx spRedex (RigidShapeVS.varApp 2 [.bvar 1]).toExpr (.sort .zero) ∧
      spRedex.spineHead = .lam (.sort .zero) (.bvar 0) ∧
      (∀ j, spRedex.spineHead ≠ .bvar j) := by
  refine ⟨spCtx_onCtx, ?_, trivial, spRedex_conv, rfl, nofun⟩
  rintro ⟨p, hp0, hep⟩
  have h := hT (ls := []) (u := .succ .zero) (u' := .zero) spCtx_onCtx trivial trivial
    spRedex_hasType hep (HasType.sort trivial) hp0
  simp [VLevel.eval] at h

/-! ## §7.11 The fourth thing the entry adds, and the grade

The extension adds four things, not three: the three `Compat` rows §7.7 tabulates, **and** the
`RuleFree` entry `varApp _ _ => True`.  A `True` side condition is exactly the kind of thing that
hides a vacuity — it is an assumption that the rule table can never interfere with a variable
spine — so it gets checked too, and it is a theorem rather than a convention. -/

/-- **The `RuleFree` entry is justified, not assumed.**  No rule's instantiated side, on either
side, is a term a `varApp` shape denotes — so the `varApp` entry could not have carried a useful
side condition, and `True` costs nothing.  (`SpineVarClosed.lean` §2, in the `mkApp` form the
shape's `toExpr` has.) -/
theorem rigidShapeVS_varApp_ruleFree_justified (henv : env.WF) {df : VDefEq}
    (h : env.defeqs df) (ls : List VLevel) (i : Nat) (as : List VExpr) :
    df.lhs.instL ls ≠ (RigidShapeVS.varApp i as).toExpr ∧
      df.rhs.instL ls ≠ (RigidShapeVS.varApp i as).toExpr ∧
      RigidShapeVS.RuleFree env (.varApp i as) :=
  ⟨henv.instL_lhs_ne_bvar_mkApp h ls i as, henv.instL_rhs_ne_bvar_mkApp h ls i as, trivial⟩

/-- **The grade, as one statement.**  Four conjuncts, in the order the grading question is asked:

1. the extension **is** the old bridge conjoined with exactly the three rows (`SpineVar.lean` §6) —
   so this is a **localisation into the corner's existing shared node**, not new strength;
2. it is at least as strong as `ShapeVar.lean`'s bridge, so nothing is lost;
3. and 4. the *vocabulary* is properly extended: no `RigidShapeV` and no `RigidShape` denotes a
   variable-headed spine with a non-empty argument list, so the three rows cannot even be **stated**
   downstairs.

What is **not** proved, in either direction, is whether the three rows follow from
`RigidShapeUniq` alone.  If they did, the extension would be a **rename** rather than a
localisation.  Conjuncts 3 and 4 make that unlikely-looking — the rows are not expressible in the
old vocabulary — but expressibility is not derivability, and this is left open and flagged, not
assumed away. -/
theorem spineVar_grade (henv : env.WF) (htr : env.ProofTransport U) :
    (env.RigidShapeVSUniq U ↔ env.RigidShapeUniq U ∧ SpineVarPiDisj env U ∧
        SpineVarSortDisj env U ∧ SpineVarAppDisj env U) ∧
      (env.RigidShapeVSUniq U → env.RigidShapeVUniq U) ∧
      (∀ (s : RigidShapeV) (i : Nat) (a : VExpr) (as : List VExpr),
        s.toExpr ≠ (VExpr.bvar i).mkApp (a :: as)) ∧
      (∀ (s : RigidShape) (i : Nat) (a : VExpr) (as : List VExpr),
        s.toExpr ≠ (VExpr.bvar i).mkApp (a :: as)) :=
  ⟨rigidShapeVSUniq_iff henv htr, fun H => H.rigidShapeVUniq,
   fun s i a as => s.toExpr_ne_bvar_app i a as, fun s i a as => s.toExpr_ne_bvar_app i a as⟩

/-! ## §7.12 Which witness environments these are, machine-checked

Requirement: say what the witnesses assume, and do not let a docstring do it.  So:

* `VEnv.empty` declares **no** constant and **no** rule (§7.5, §7.6, §7.10 and `SpineVar.lean`
  §7.2/§7.3 live here);
* `svEnv` (`SpineVar.lean` §7.4, §7.9) declares **exactly one** constant, the axiom
  `svC : ∀ X : Prop, X`, and no rules;
* that axiom makes `svEnv` **logically inconsistent**, and here is the proof rather than the
  assertion: every proposition of every context is inhabited there, and the closed proposition
  `svFalse` is inhabited in the **empty** context.

Two consequences worth being explicit about.  First, an inconsistent `VEnv.WF` environment is a
*legitimate* refutation witness — the rows quantify over all `VEnv.WF` environments — but it is not
a legitimate *satisfaction* witness, and nothing here uses it as one: `svEnv` appears only under
`¬` (`spineVarAppDisjNaive_false`) or in a premise-failure statement (§7.9).  Second, the corner's
*other* inconsistent witness, `univInhab : ∀ (α : Sort u), α` (the weakening/strengthening
stream's, `docs/handoff-weakn.md`, `docs/handoff-gatebody.md`), is **not** used here or in
`SpineVar.lean` or `ShapeVar.lean`: `svEnv`'s single axiom is *propositional*, and the theorem below
pins the constant table exactly, so this is a checked absence and not a grep. -/

/-- **The witness environments' whole content.**  `VEnv.empty` is empty; `svEnv`'s constant table
is the single entry `svC ↦ ⟨0, ∀ X : Prop, X⟩` and nothing else — in particular no `univInhab`,
because there is no second entry to hold one — and neither has a rule. -/
theorem spineVar_witness_envs :
    (∀ n, (∅ : VEnv).constants n = none) ∧ (∀ df, ¬ (∅ : VEnv).defeqs df) ∧
      (∀ n, n ≠ svC → svEnv.constants n = none) ∧ svEnv.constants svC = some svCi ∧
      svCi = ⟨0, svFalse⟩ ∧ svFalse = .forallE (.sort .zero) (.bvar 0) ∧
      (∀ df, ¬ svEnv.defeqs df) := by
  refine ⟨fun _ => rfl, fun _ h => h, fun n hn => ?_, svEnv_constants, rfl, rfl, fun _ h => h⟩
  simp [svEnv, Ne.symm hn]

/-- **`svEnv` is inconsistent, as a theorem.**  Every proposition in every context is inhabited by
one application of the axiom. -/
theorem svEnv_every_prop_inhabited {Γ : List VExpr} {P : VExpr}
    (hP : svEnv.HasType 0 Γ P (.sort .zero)) :
    svEnv.HasType 0 Γ (.app (.const svC []) P) P := by
  have h := HasType.app
    (.constDF svEnv_constants (ls := []) nofun nofun rfl .nil : svEnv.HasType 0 Γ _ svFalse) hP
  simpa [svFalse, VExpr.instL, VExpr.inst] using h

/-- …and the closed proposition `∀ X : Prop, X` is inhabited in the **empty** context, which is
the sharpest form of the disclosure. -/
theorem svEnv_false_inhabited : svEnv.HasType 0 [] (.const svC []) svFalse :=
  .constDF svEnv_constants (ls := []) nofun nofun rfl .nil

end VEnv

section Audit
-- §7.5 the non-proof witness: the tainted route, then the hole-free one
#print axioms Lean4Lean.VEnv.spineVar_hasType_prop
#print axioms Lean4Lean.VEnv.spineVar_isType
#print axioms Lean4Lean.VEnv.spineVar_not_isProof
#print axioms Lean4Lean.VEnv.spineVar_not_isProof_of_propAgreeOn
#print axioms Lean4Lean.VEnv.spineVar_guard_not_vacuous
-- §7.6 the consumer firing test
#print axioms Lean4Lean.VEnv.spCtx'_onCtx
#print axioms Lean4Lean.VEnv.spineVar_row_premises
#print axioms Lean4Lean.VEnv.spineVar_row_fires
-- §7.7 the refutation attempt, mechanism by mechanism
#print axioms Lean4Lean.VEnv.forallE_not_isProof
#print axioms Lean4Lean.VEnv.sort_not_isProof
#print axioms Lean4Lean.VEnv.isProof_of_proofIrrel_premises
#print axioms Lean4Lean.VEnv.spineVar_delta_blocked
#print axioms Lean4Lean.VEnv.spineHead_bvar_ne_beta
#print axioms Lean4Lean.VEnv.spineHead_bvar_ne_lam
#print axioms Lean4Lean.VEnv.spineVar_mechanisms_blocked
-- §7.8 the residual, hole-free core then the applied form
#print axioms Lean4Lean.VEnv.spineVarPi_midpoint_aux
#print axioms Lean4Lean.VEnv.spineVarPi_midpoint
#print axioms Lean4Lean.VEnv.spineVarSort_midpoint_aux
#print axioms Lean4Lean.VEnv.forallE_sort_ne_app
#print axioms Lean4Lean.VEnv.mkApp_cons_eq_app
#print axioms Lean4Lean.VEnv.not_isProof_fun_of_not_isProof_app
-- §7.9 the two hard constraints at every midpoint
#print axioms Lean4Lean.VEnv.spDiagCtx_isProof_of_conv
#print axioms Lean4Lean.VEnv.spAppCtx_isProof_of_conv
#print axioms Lean4Lean.VEnv.spAppCtx_no_bridge_instance
#print axioms Lean4Lean.VEnv.rigidShapeVS_compat_varApp_diag
-- §7.10 the redex midpoint
#print axioms Lean4Lean.VEnv.spRedex_conv
#print axioms Lean4Lean.VEnv.spineVar_midpoint_unconstrained
-- §7.12 the witness environments, and svEnv's inconsistency
#print axioms Lean4Lean.VEnv.spineVar_witness_envs
#print axioms Lean4Lean.VEnv.svEnv_every_prop_inhabited
#print axioms Lean4Lean.VEnv.svEnv_false_inhabited
-- §7.11 the fourth row, and the grade
#print axioms Lean4Lean.VEnv.rigidShapeVS_varApp_ruleFree_justified
#print axioms Lean4Lean.VEnv.spineVar_grade
end Audit

end Lean4Lean
