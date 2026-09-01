import Lean4Lean.Theory.SetModel.InterpSubst
import Lean4Lean.Theory.SetModel.PropUniqFromFalse
import Lean4Lean.Theory.Typing.Strengthen

/-!
# The satisfiability audit for `PropSplit.Stable`

`SetModel/PropSplitAudit.lean` audits `PropSplit`.  It does **not** audit
`PropSplit.Stable`, which is a *separate* hypothesis of `soundAbove`
(`SetModel/SoundInduction.lean`) and of everything downstream of it, and which
nothing in the tree has ever proved for any `PropSplit`.

This is the same omission the `LevelAssign` family was caught by twice
(`SetModel/LevelAssignUnsat.lean`): a structure whose producers all consume the
same structure has never had its fields tested.  `PropSplit` got the test;
`PropSplit.Stable` did not.

## What the audit finds

`propSplitOf` (`PropSplitAudit.lean`) is the tree's **only** construction of a
`PropSplit`.  For it, `Stable` splits cleanly:

* the four `←` directions — from the smaller context to the larger, from the
  unsubstituted body to the substituted one — are **weakening and substitution**,
  and are proved below from `env.Ordered` alone;
* the four `→` directions are **descent**: a term that is typeable *after*
  weakening or substitution must already have been typeable before.  Those are
  not available, and `PropDescend` below states exactly what they need.

`propSplitOf_stable_iff` proves the reduction is **tight**: for `propSplitOf`,
`Stable ↔ PropDescend`.  So this is not a residual that could be discharged by
a cleverer proof against the same construction — it is what the construction
costs.

## Consequence for the standing label

`docs/model-interface.md`'s standing label says the model's residual syntactic
import is `PropTypeAgree` **alone**.  That is measured against `PropSplit` and
overlooks `PropSplit.Stable`.  As the tree stands the import is

```
PropTypeAgree  ∧  PropDescend
```

with `PropUniq` discharged from the goal's own `hfalse`
(`PropUniqFromFalse.lean`) as before.

## Why `PropDescend` is not free

`PropDescend.sort_lift` is a **strengthening** statement, and strengthening is
open: `Theory/Typing/Strengthen.lean` reduces it to `PiDescend` and records that
the general form is `sorryAx`-tainted through Π-injectivity.  §1 of that file
(`IsDefEqU.strengthen_of_instN`) proves strengthening whenever the stripped
context entry is *inhabited*, which is not available here — `Ctx.LiftN` inserts
arbitrary entries.

`PropDescend.sort_inst` is worse: it asks that `B` be typeable whenever
`B.inst e₀ k` is.  Substitution can create typeability that the unsubstituted
body does not have, because `e₀` can carry structure that its *type* `A₀` does
not.  The candidate witness, stated but **not** machine-checked:

```
Γ₀ = [],  A₀ = Prop → Prop,  e₀ = fun p : Prop => p,  k = 0
Γ₁ = [Prop → Prop],  Γ = []
B  = (bvar 0) falseProp falseProp        -- two arguments
```

**UPDATE (2026-09-01): the witness above does not work, and this paragraph was wrong.**
`SetModel/InstDescendAudit.lean` §1 machine-checks it.  The claim was that
`B.inst e₀ 0`'s inner head `(fun p => p) falseProp` has type `falseProp`, a
Π-type, so the outer application types while the `Γ₁` side does not.  It does
not: `(fun p : Prop => p) falseProp` has type **`Prop`**, exactly like
`(bvar 0) falseProp` at `Γ₁` (`w_head_unsubst`, `w_head_subst`,
`w_head_type_agree`), and the two terms are `inst`-related on the nose.  So the
outer application needs a term of type `Prop` to be applied on *both* sides:
`w_types_of_sortPiConv` derives **both** typings from one `Prop ≡ Π`
hypothesis.  The witness is symmetric and cannot refute `sort_inst`, whatever
the disposition of `IsDefEqU.sort_forallE_inv`.

`sort_inst` is still **open** — what is gone is the recorded reason for
believing it refutable, and with it the attribution of the blockage to
`sort_forallE_inv`.  `InstDescendAudit.lean` §2 removes the level condition from
the residual (`sortInstDescend_iff`, given `Ordered` + `PropUniq`, which the
model side already assumes), so the whole content is typeability descent; §3
walks its cases and finds the real shared residual to be **uniqueness of typing
plus inversion at a sort**, not `Prop ≡ Π`.

## Scope

Everything here is about `propSplitOf`.  A *different* `PropSplit` — one built
as a syntactic recursion mirroring `inferType`, which is what
`SetModel/InterpSubst.lean`'s note on `Stable` has in mind — would satisfy
`Stable` by construction and pay for `prop_sound` instead.  No such construction
exists in the tree.
-/

namespace Lean4Lean

namespace VEnv

/-- **Descent of propositionhood along weakening and substitution.**

Four statements, one per `PropSplit.Stable` field, each the `→` direction that
weakening/substitution does not supply.  All four are restricted to the case the
consumer actually needs — a sort that *evaluates to zero* — so the reduction
below is an equivalence rather than a sufficient condition. -/
structure PropDescend (env : VEnv) (nv : ℕ) : Prop where
  /-- A type that is a proposition after weakening was one before. -/
  sort_lift : ∀ {n k : ℕ} {Γ Γ' : List VExpr} {A : VExpr} {u : VLevel} {ls : List ℕ},
    Ctx.LiftN n k Γ Γ' → u.WF nv → env.HasType nv Γ' (A.liftN n k) (.sort u) →
    u.eval ls = 0 → ∃ v : VLevel, v.WF nv ∧ env.HasType nv Γ A (.sort v) ∧ v.eval ls = 0
  /-- A term that is a proof after weakening was one before. -/
  proof_lift : ∀ {n k : ℕ} {Γ Γ' : List VExpr} {e A : VExpr} {u : VLevel} {ls : List ℕ},
    Ctx.LiftN n k Γ Γ' → u.WF nv → env.HasType nv Γ' (e.liftN n k) A →
    env.HasType nv Γ' A (.sort u) → u.eval ls = 0 →
    ∃ (B : VExpr) (v : VLevel), v.WF nv ∧ env.HasType nv Γ e B ∧
      env.HasType nv Γ B (.sort v) ∧ v.eval ls = 0
  /-- A type that is a proposition after substitution was one before. -/
  sort_inst : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr}
    {B : VExpr} {u : VLevel} {ls : List ℕ},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ → u.WF nv →
    env.HasType nv Γ (B.inst e₀ k) (.sort u) → u.eval ls = 0 →
    ∃ v : VLevel, v.WF nv ∧ env.HasType nv Γ₁ B (.sort v) ∧ v.eval ls = 0
  /-- A term that is a proof after substitution was one before. -/
  proof_inst : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr}
    {e A : VExpr} {u : VLevel} {ls : List ℕ},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ → u.WF nv →
    env.HasType nv Γ (e.inst e₀ k) A → env.HasType nv Γ A (.sort u) → u.eval ls = 0 →
    ∃ (B : VExpr) (v : VLevel), v.WF nv ∧ env.HasType nv Γ₁ e B ∧
      env.HasType nv Γ₁ B (.sort v) ∧ v.eval ls = 0

end VEnv

namespace SetModel

variable {env : VEnv} {nv : ℕ}

/-! ## The four `←` directions: weakening and substitution -/

section Easy

variable {hU : env.PropUniq nv} {hT : env.PropTypeAgree nv}

/-- Weakening: a proposition stays a proposition in a larger context. -/
theorem propSplitOf_isPropAt_lift (henv : env.Ordered) {n k : ℕ} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ')
    {ls : List ℕ} {A : VExpr} (h : (propSplitOf env nv hU hT).IsPropAt ls Γ A) :
    (propSplitOf env nv hU hT).IsPropAt ls Γ' (A.liftN n k) :=
  let ⟨u, hu, hA, h0⟩ := h
  ⟨u, hu, hA.weakN henv W, h0⟩

/-- Weakening: a proof stays a proof in a larger context. -/
theorem propSplitOf_isProofAt_lift (henv : env.Ordered) {n k : ℕ} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ')
    {ls : List ℕ} {e : VExpr} (h : (propSplitOf env nv hU hT).IsProofAt ls Γ e) :
    (propSplitOf env nv hU hT).IsProofAt ls Γ' (e.liftN n k) :=
  let ⟨A, u, hu, he, hA, h0⟩ := h
  ⟨A.liftN n k, u, hu, he.weakN henv W, hA.weakN henv W, h0⟩

/-- Substitution: a proposition stays a proposition after a well-typed
substitution. -/
theorem propSplitOf_isPropAt_inst (henv : env.Ordered) {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ}
    {Γ₁ Γ : List VExpr} (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    {ls : List ℕ} {B : VExpr} (h : (propSplitOf env nv hU hT).IsPropAt ls Γ₁ B) :
    (propSplitOf env nv hU hT).IsPropAt ls Γ (B.inst e₀ k) :=
  let ⟨u, hu, hB, h0⟩ := h
  ⟨u, hu, hB.instN henv W h₀, h0⟩

/-- Substitution: a proof stays a proof after a well-typed substitution. -/
theorem propSplitOf_isProofAt_inst (henv : env.Ordered) {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ}
    {Γ₁ Γ : List VExpr} (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType nv Γ₀ e₀ A₀)
    {ls : List ℕ} {e : VExpr} (h : (propSplitOf env nv hU hT).IsProofAt ls Γ₁ e) :
    (propSplitOf env nv hU hT).IsProofAt ls Γ (e.inst e₀ k) :=
  let ⟨A, u, hu, he, hA, h0⟩ := h
  ⟨A.inst e₀ k, u, hu, he.instN henv W h₀, hA.instN henv W h₀, h0⟩

end Easy

/-! ## The reduction, and its tightness -/

variable {hU : env.PropUniq nv} {hT : env.PropTypeAgree nv}

/-- **`PropDescend` is exactly what `propSplitOf` needs to be `Stable`.**

The `←` directions are `propSplitOf_isPropAt_lift` and friends; the `→`
directions are `PropDescend`'s four fields, applied verbatim. -/
theorem propSplitOf_stable (henv : env.Ordered) (hD : env.PropDescend nv) :
    (propSplitOf env nv hU hT).Stable where
  prop_liftN W ls A :=
    ⟨fun ⟨u, hu, hA, h0⟩ => hD.sort_lift W hu hA h0,
     fun h => propSplitOf_isPropAt_lift henv W h⟩
  proof_liftN W ls e :=
    ⟨fun ⟨A, u, hu, he, hA, h0⟩ => hD.proof_lift W hu he hA h0,
     fun h => propSplitOf_isProofAt_lift henv W h⟩
  prop_instN W h₀ ls B :=
    ⟨fun ⟨u, hu, hB, h0⟩ => hD.sort_inst W h₀ hu hB h0,
     fun h => propSplitOf_isPropAt_inst henv W h₀ h⟩
  proof_instN W h₀ ls e :=
    ⟨fun ⟨A, u, hu, he, hA, h0⟩ => hD.proof_inst W h₀ hu he hA h0,
     fun h => propSplitOf_isProofAt_inst henv W h₀ h⟩

/-- **The converse: the reduction does not overshoot.**  `Stable` for
`propSplitOf` *is* `PropDescend` — the four `→` directions unfold to it on the
nose.  So `PropDescend` passes the collapse test: its premises cannot be
instantiated to make it weaker than the thing it is reducing. -/
theorem propDescend_of_stable (hS : (propSplitOf env nv hU hT).Stable) :
    env.PropDescend nv where
  sort_lift W hu hA h0 := (hS.prop_liftN W _ _).mp ⟨_, hu, hA, h0⟩
  proof_lift W hu he hA h0 := (hS.proof_liftN W _ _).mp ⟨_, _, hu, he, hA, h0⟩
  sort_inst W h₀ hu hB h0 := (hS.prop_instN W h₀ _ _).mp ⟨_, hu, hB, h0⟩
  proof_inst W h₀ hu he hA h0 := (hS.proof_instN W h₀ _ _).mp ⟨_, _, hu, he, hA, h0⟩

/-- **The audit's conclusion, as an equivalence.** -/
theorem propSplitOf_stable_iff (henv : env.Ordered) :
    (propSplitOf env nv hU hT).Stable ↔ env.PropDescend nv :=
  ⟨propDescend_of_stable, propSplitOf_stable henv⟩

/-! ## The assembled export

`PropUniqFromFalse.propSplitOfAgree` builds the `PropSplit` the model runs on
from `PropTypeAgree` plus the goal's own `hfalse`.  This is that construction
with `Stable` attached, which is what `soundAbove` actually consumes. -/

/-- **A `Stable` `PropSplit`, from the hypotheses the goal supplies.**

`propSplitOfAgree` unfolds to `propSplitOf`, so `propSplitOf_stable` applies to
it directly.  The list of syntactic imports is therefore
`PropTypeAgree env 0` together with `PropDescend env nv`; `PropUniq` is
discharged from `hf`. -/
theorem propSplitOfAgree_stable {env : VEnv} (nv : ℕ) (henv : env.Ordered)
    (hf : ∃ e, env.HasType 0 [] e falseProp) (hT : env.PropTypeAgree 0)
    (hD : env.PropDescend nv) : (propSplitOfAgree env nv henv hf hT).Stable :=
  propSplitOf_stable (hU := VEnv.PropUniq.of_zero (VEnv.PropUniq.of_propTypeAgree henv hf hT) nv)
    (hT := VEnv.PropTypeAgree.of_zero hT nv) henv hD

/-- The existence form: everything `soundAbove`'s `L`/`hS` pair needs, from
`Ordered`, the goal's `hfalse`, `PropTypeAgree` and `PropDescend`. -/
theorem exists_stable_propSplit {env : VEnv} (nv : ℕ) (henv : env.Ordered)
    (hf : ∃ e, env.HasType 0 [] e falseProp) (hT : env.PropTypeAgree 0)
    (hD : env.PropDescend nv) : ∃ L : PropSplit env nv, L.Stable :=
  ⟨_, propSplitOfAgree_stable nv henv hf hT hD⟩

/-! ## Connecting the two `lift` fields to the strengthening stream

`Theory/Typing/Strengthen.lean` already names the statements `PropDescend`'s two
`lift` fields are made of: `TypingStrengthening` (a lifted term typeable upstairs
is typeable downstairs) and `SortDescend` (…and at a sort, if it was at a sort
upstairs).  Both are importable alongside `SetModel/` — checked.

**But they carry two hypotheses `PropSplit.Stable` does not have**:
`OnCtx Γ (env.IsType nv)` and `OnCtx Γ' (env.IsType nv)`.  `Stable.prop_liftN` is
stated for *arbitrary* `Γ`, `Γ'`, because its consumers (`interp_liftN`,
`interp_inst`) recurse over raw syntax and assume only `ClosedN`.  So what is
proved below is the `OnCtx`-guarded half of `PropDescend`, and the gap between it
and `PropDescend` is exactly a junk-context gap — the same shape that refuted the
unguarded `LevelAssign` (`SetModel/LevelAssignUnsat.lean`).

**This is the actionable next step for the model side**: thread
`OnCtx Γ (env.IsType nv)` through `interp_liftN`/`interp_inst` and into
`PropSplit.Stable`'s fields.  It is available where soundness is used —
`sound` already takes `OnCtx Γ (env₀.IsType nv)` — and if it can be threaded,
`PropDescend`'s two `lift` fields become `TypingStrengthening ∧ SortDescend`
verbatim, i.e. work the strengthening stream is already doing. -/

section Guarded

variable {env : VEnv} {nv : ℕ}

/-- **The `OnCtx`-guarded `sort_lift`, from the strengthening stream's two
statements.**  `TypingStrengthening` supplies typeability downstairs,
`SortDescend` upgrades it to a sort, and `PropUniq` transports "evaluates to
zero" back across the weakening. -/
theorem sort_lift_of_strengthening (henv : env.Ordered) (hU : env.PropUniq nv)
    (hTS : env.TypingStrengthening nv) (hSD : env.SortDescend nv)
    {n k : ℕ} {Γ Γ' : List VExpr} {A : VExpr} {u : VLevel} {ls : List ℕ}
    (W : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType nv))
    (hΓ' : OnCtx Γ' (env.IsType nv)) (hu : u.WF nv)
    (hA : env.HasType nv Γ' (A.liftN n k) (.sort u)) (h0 : u.eval ls = 0) :
    ∃ v : VLevel, v.WF nv ∧ env.HasType nv Γ A (.sort v) ∧ v.eval ls = 0 := by
  obtain ⟨v, hAv⟩ := hSD W hΓ hΓ' hA (hTS W hΓ hΓ' hA)
  have hv : v.WF nv := hAv.sort_r henv hΓ
  refine ⟨v, hv, hAv, ?_⟩
  exact ((hU hu hv hA (hAv.weakN henv W)).mp h0)

/-- **The `OnCtx`-guarded `proof_lift`.**  Only `TypingStrengthening` is needed —
no `SortDescend` — because validity (`IsDefEq.isType`) supplies the descended
term's type-of-type, and `PropTypeAgree` transports propositionhood between the
two types the term has upstairs. -/
theorem proof_lift_of_strengthening (henv : env.Ordered) (hT : env.PropTypeAgree nv)
    (hTS : env.TypingStrengthening nv)
    {n k : ℕ} {Γ Γ' : List VExpr} {e A : VExpr} {u : VLevel} {ls : List ℕ}
    (W : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType nv))
    (hΓ' : OnCtx Γ' (env.IsType nv)) (hu : u.WF nv)
    (he : env.HasType nv Γ' (e.liftN n k) A) (hA : env.HasType nv Γ' A (.sort u))
    (h0 : u.eval ls = 0) :
    ∃ (B : VExpr) (v : VLevel), v.WF nv ∧ env.HasType nv Γ e B ∧
      env.HasType nv Γ B (.sort v) ∧ v.eval ls = 0 := by
  obtain ⟨B, heB⟩ := hTS W hΓ hΓ' he
  obtain ⟨v, hBv⟩ := heB.isType henv hΓ
  have hv : v.WF nv := hBv.sort_r henv hΓ
  refine ⟨B, v, hv, heB, hBv, ?_⟩
  exact (hT hu hv he (heB.weakN henv W) hA (hBv.weakN henv W)).mp h0

end Guarded

/-! ## The other route, and the trade-off it exposes

`LevelAssign.toPropSplit` (`SetModel/Interp.lean`) is the tree's *other* map into
`PropSplit`.  Its `IsPropAt` is a **function** of the syntax — `(L.lvl Γ A).eval
ls = 0` — rather than an existential over typings, and for a function `Stable` is
just the statement that the function commutes with lifting and substitution.
`toPropSplit_stable` below proves that, and it is three lines.

So the two routes pay in different currencies, and this is the point of the
audit:

| route | `prop_sound`/`proof_sound` | `Stable` |
|---|---|---|
| `propSplitOf` (from `PropTypeAgree`) | free | `PropDescend` — **open**, strengthening-shaped |
| `LevelAssign.toPropSplit` | needs `LevelAssign`, i.e. `sort_inv` + `srt_uniq` (unique typing) | `Commutes` — plausible for a syntactic recursion |

`PropSplit` was introduced to weaken the model's syntactic import from
`sort_inv`/`SortUniq` to `PropTypeAgree`.  Measured against `PropSplit` alone
that succeeds.  Measured against `PropSplit` **together with `Stable`**, which is
what `soundAbove` consumes, the import is not removed but relocated: it leaves
`prop_sound` and reappears in `Stable`.  Whether the relocation is a net gain is
an open question about `PropDescend` versus `sort_inv`, and this file does not
claim it is one. -/

/-- The four commutation statements a `LevelAssign` needs for its induced
`PropSplit` to be `Stable`.  Stated with `≈`, which is what a syntactic
recursion mirroring `inferType` would deliver. -/
structure LevelAssign.Commutes {env : VEnv} {nv : ℕ} (L : LevelAssign env nv) : Prop where
  lvl_liftN : ∀ {n k : ℕ} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
    ∀ A : VExpr, L.lvl Γ' (A.liftN n k) ≈ L.lvl Γ A
  srt_liftN : ∀ {n k : ℕ} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
    ∀ e : VExpr, L.srt Γ' (e.liftN n k) ≈ L.srt Γ e
  lvl_instN : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
    ∀ B : VExpr, L.lvl Γ (B.inst e₀ k) ≈ L.lvl Γ₁ B
  srt_instN : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
    ∀ e : VExpr, L.srt Γ (e.inst e₀ k) ≈ L.srt Γ₁ e

/-- **For the level-assignment route, `Stable` is free once the assignment
commutes.**  Contrast `propSplitOf_stable_iff`.  (`LevelAssign` itself is still
unconstructed in this tree; this says nothing about its existence.) -/
theorem toPropSplit_stable {L : LevelAssign env nv} (hc : L.Commutes) :
    L.toPropSplit.Stable where
  prop_liftN W ls A := by
    show (L.lvl _ _).eval ls = 0 ↔ (L.lvl _ _).eval ls = 0
    rw [VLevel.equiv_def.mp (hc.lvl_liftN W A) ls]
  proof_liftN W ls e := by
    show (L.srt _ _).eval ls = 0 ↔ (L.srt _ _).eval ls = 0
    rw [VLevel.equiv_def.mp (hc.srt_liftN W e) ls]
  prop_instN W h₀ ls B := by
    show (L.lvl _ _).eval ls = 0 ↔ (L.lvl _ _).eval ls = 0
    rw [VLevel.equiv_def.mp (hc.lvl_instN W h₀ B) ls]
  proof_instN W h₀ ls e := by
    show (L.srt _ _).eval ls = 0 ↔ (L.srt _ _).eval ls = 0
    rw [VLevel.equiv_def.mp (hc.srt_instN W h₀ e) ls]

end SetModel

end Lean4Lean
