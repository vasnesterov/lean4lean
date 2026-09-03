import Lean4Lean.Theory.Typing.StrengthenNarrow
import Lean4Lean.Theory.Typing.StrengthenVerdict
import Lean4Lean.Theory.Inductive.Lemmas

/-!
# The projection corner's appeal to `IsDefEqU.weakN_iff`, priced without a new hole

Round 7 of the attack on `VEnv.IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean:172`).
See `docs/handoff-weakn.md` for rounds 1-6 and for the routes that are foreclosed.

## Why this file exists

Measured this round (script reproduced in `docs/handoff-weakn.md` §7.1): the whole projection
corner -- `TrProj.wf`, `VEnv.IsStructureG.projTermG_hasType` (wall 2) and its witness -- reaches
this hole through **one** direct user, `VEnv.IsDefEq.weakN_iff'`, and reaches *that* only through
the *typing* wrappers `VEnv.HasType.weakN_iff` / `IsType.weakN_iff` / `OnCtx.weakN_inv`.  Cut
those and the corner no longer reaches the hole at all: 29 of the corner's 32 hole-reaching
declarations are freed, the remaining 3 being the `constRigid` line of `ProjWeakInv{,Split}.lean`,
which is a different residual.  So the corner needs only the **typing half**
(`VEnv.TypingStrengthening`, equivalently `PiDescend`), not the `trans` residual.

`StrengthenNarrow.lean` §5 already reproves those wrappers from `TypingStrengthening`.  But its
versions go through `TypingStrengthening.typed`, whose cone contains `IsDefEqU.forallE_inv` and
therefore the hole `WF.rigidShapeUniqNS` -- so substituting them into the corner would trade the
hole `weakN_iff` for the hole `rigidShapeUniqNS` (measured, §7.2 of the handoff).  This file
avoids that trade:

* §1 `IsType`/`OnCtx` descent from `TypingStrengthening`, **with no hole in its cone at all** --
  it goes through `SortDescend` (which `TypingStrengthening.sortDescend` supplies hole-free)
  instead of through `typed`.
* §2 sort-typed `HasType` descent *with the level preserved*.  Pinning the level costs
  `IsDefEqU.sort_inv`, i.e. `IsDefEqU.forallE_inv_stratified` -- which is **already** in the
  corner's cone, so this is not a new hole.
* §3 the context-swap lemma `ProjSkip.lean`'s `VEnv.HasType.swapSkipped` needs, at the
  sort-typed generality its own crux `ftype_hasType_swapped` uses it at.
* §4 the general (non-sort) swap, for the corner's remaining sites; this one *does* pay
  `rigidShapeUniqNS`, and the difference between §3 and §4 is the point of the file.
* §5 anti-vacuity: the hypothesis is inhabited at a `VEnv.WF` environment, and §3 fires there
  with no hypotheses left.
* §6 negative controls.

Nothing here closes the hole, and nothing here removes a `sorry`.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## 1. `IsType` and `OnCtx` descent, hole-free from the typing half

`StrengthenNarrow.lean` §5's `TypingStrengthening.isType_inv` calls
`TypingStrengthening.typed`, which upgrades an existential type to the given one by the
ascription-redex trick of `Strengthen.lean` §3 and so consumes `IsDefEqU.forallE_inv`.  For a
judgement whose type is a **sort** none of that is needed: `SortDescend` produces a sort type
downstairs directly, and `IsType` leaves the level existential, which is exactly what
`SortDescend` returns. -/

theorem onCtx_of_appendL {P : List VExpr → VExpr → Prop} :
    ∀ {As Γ : List VExpr}, OnCtx (As ++ Γ) P → OnCtx Γ P
  | [], _, h => h
  | _::_, _, h => onCtx_of_appendL h.1

variable! (henv : VEnv.WF env) in
/-- **`OnCtx.weakN_inv` and `IsType.weakN_iff`'s forward direction, together, from the typing
half -- with no hole in the cone.**  They are proved together because the `IsType` step needs
`OnCtx` of the smaller context, which the induction supplies. -/
theorem TypingStrengthening.onCtx_isType_inv (HT : TypingStrengthening env U) :
    ∀ {n k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
      OnCtx Γ' (env.IsType U) →
      OnCtx Γ (env.IsType U) ∧
        ∀ {A : VExpr}, env.IsType U Γ' (A.liftN n k) → env.IsType U Γ A := by
  intro n k Γ Γ' W
  induction W with
  | zero As h =>
    intro hΓ'
    refine ⟨onCtx_of_appendL hΓ', fun {A} ⟨u, hu⟩ => ?_⟩
    have hΓ := onCtx_of_appendL (P := fun Γ A => env.IsType U Γ A) hΓ'
    exact HT.sortDescend henv (.zero As h) hΓ hΓ' hu (HT (.zero As h) hΓ hΓ' hu)
  | @succ k Γ Γ' A W ih =>
    intro hΓ'
    have ⟨hΓ'0, hstep⟩ := ih hΓ'.1
    have hA : env.IsType U Γ A := hstep hΓ'.2
    refine ⟨⟨hΓ'0, hA⟩, fun {B} ⟨u, hu⟩ => ?_⟩
    exact HT.sortDescend henv W.succ ⟨hΓ'0, hA⟩ hΓ' hu (HT W.succ ⟨hΓ'0, hA⟩ hΓ' hu)

variable! (henv : VEnv.WF env) in
/-- `OnCtx.weakN_inv` from the typing half, hole-free. -/
theorem TypingStrengthening.onCtx_inv' (HT : TypingStrengthening env U)
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) :=
  (HT.onCtx_isType_inv henv W hΓ').1

variable! (henv : VEnv.WF env) in
/-- `IsType.weakN_iff`'s forward direction from the typing half, hole-free. -/
theorem TypingStrengthening.isType_inv' (HT : TypingStrengthening env U)
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (H : env.IsType U Γ' (A.liftN n k)) : env.IsType U Γ A :=
  (HT.onCtx_isType_inv henv W hΓ').2 H

variable! (henv : VEnv.WF env) in
/-- …and as the `iff` that `IsType.weakN_iff` states. -/
theorem TypingStrengthening.isType_weakN_iff' (HT : TypingStrengthening env U)
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U)) :
    env.IsType U Γ' (A.liftN n k) ↔ env.IsType U Γ A :=
  ⟨HT.isType_inv' henv W hΓ', fun h => h.weakN henv W⟩

/-! ## 2. Sort-typed `HasType` descent, with the level preserved

`SortDescend` returns *some* sort; the projection corner needs the **stored** level
(`ftype_hasType_swapped`'s conclusion is at `.sort ((C.fields.getD i default).lvl.inst us)`), so
the level has to be pinned.  That step is unique typing at a sort, i.e. `IsDefEqU.sort_inv`,
whose cone contains `IsDefEqU.forallE_inv_stratified` -- **already** in the corner's cone
(measured: `TrProj.wf`'s hole set is `{weakN_iff, forallE_inv_stratified}`), so no new hole. -/

variable! (henv : VEnv.WF env) in
/-- `HasType.weakN_iff`'s forward direction at a **sort** type, from the typing half.  Cone:
`IsDefEqU.forallE_inv_stratified` only -- in particular not `WF.rigidShapeUniqNS`, which
`StrengthenNarrow.lean` §5's general `hasType_inv` pays. -/
theorem TypingStrengthening.hasType_sort_inv (HT : TypingStrengthening env U)
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (H : env.HasType U Γ' (e.liftN n k) (.sort u)) : env.HasType U Γ e (.sort u) := by
  have hΓ := HT.onCtx_inv' henv W hΓ'
  have ⟨u₀, h₀⟩ := HT.sortDescend henv W hΓ hΓ' H (HT W hΓ hΓ' H)
  have h₀' : env.HasType U Γ' (e.liftN n k) (.sort u₀) := h₀.weakN henv W
  have hu : u₀ ≈ u := IsDefEqU.sort_inv henv hΓ' (h₀'.uniqU henv hΓ' H)
  have hu₀wf : u₀.WF U := (h₀.isType henv hΓ).sort_inv henv.ordered
  have huwf : u.WF U := (H.isType henv hΓ').sort_inv henv.ordered
  exact (IsDefEq.sortDF hu₀wf huwf hu).defeqDF h₀

/-! ## 3. The swap `ProjSkip.lean` runs on, at its crux's generality

`VEnv.HasType.swapSkipped` (`Verify/Typing/ProjSkip.lean:156`) is
`((HasType.weakN_iff henv hΓ W).1 H).weakN henv.ordered W'` -- strengthen, then weaken along a
second lift out of the same context.  It is the **only** declaration in the projection corner
whose route to the hole is not a context-well-formedness step (measured, §7.1 of the handoff:
the corner's direct gate call sites are `ProjSkip.OnCtx.of_appendTele` and
`ProjSkip.VEnv.HasType.swapSkipped`, plus three in `Verify/Typing/Lemmas.lean` that
`TrProj.wf`'s route does not use).  Here it is, from the typing half, at the sort-typed
generality `ftype_hasType_swapped` uses it at. -/

variable! (henv : VEnv.WF env) in
/-- **The sort-typed context swap from the typing half.**  If a judgement's subject is a lift
through a hole and its type is a sort, the material in the hole may be replaced wholesale. -/
theorem TypingStrengthening.hasType_sort_swapSkipped (HT : TypingStrengthening env U)
    {Γ₀ Γ Γ' : List VExpr} {b : VExpr} {u : VLevel} {n k : Nat}
    (hΓ : OnCtx Γ (env.IsType U)) (W : Ctx.LiftN n k Γ₀ Γ) (W' : Ctx.LiftN n k Γ₀ Γ')
    (H : env.HasType U Γ (b.liftN n k) (.sort u)) :
    env.HasType U Γ' (b.liftN n k) (.sort u) :=
  (HT.hasType_sort_inv henv W hΓ H).weakN henv W'

variable! (henv : VEnv.WF env) in
/-- The one-binder instance, which is what the telescope recursion applies. -/
theorem TypingStrengthening.hasType_sort_swapSkipped_one (HT : TypingStrengthening env U)
    {Γ : List VExpr} {A A' b : VExpr} {u : VLevel} (hΓ : OnCtx (A :: Γ) (env.IsType U))
    (H : env.HasType U (A :: Γ) (b.liftN 1 0) (.sort u)) :
    env.HasType U (A' :: Γ) (b.liftN 1 0) (.sort u) :=
  HT.hasType_sort_swapSkipped henv hΓ Ctx.LiftN.one Ctx.LiftN.one H

/-- **One of the corner's two gate call sites is spurious.**  `ProjSkip.lean`'s
`OnCtx.of_appendTele` is `OnCtx.weakN_inv henv (Ctx.LiftN.zero As.reverse rfl)` -- but at
`k = 0` the lift only *appends* a block, and dropping an appended block from an `OnCtx` is a
two-line list induction.  So that call site needs **no** strengthening, no `VEnv.WF`, and no
hypothesis: this is `onCtx_of_appendL` with the statement `ProjSkip.lean` uses. -/
theorem onCtx_of_appendTele_free {P : List VExpr → VExpr → Prop} {As Γ : List VExpr}
    (h : OnCtx (As.reverse ++ Γ) P) : OnCtx Γ P := onCtx_of_appendL h

variable! (henv : VEnv.WF env) in
/-- **`VEnv.HasType.swapTele` at a sort type, from the typing half.**  This is the
middle-of-the-telescope swap `ProjSkip.lean:245` states, restricted to the sort-typed judgements
its two callers (`ftype_hasType_swapped`, `ftype_hasType_swappedG`) actually use it at.  Cone:
`IsDefEqU.forallE_inv_stratified` only. -/
theorem TypingStrengthening.hasType_sort_swapTele (HT : TypingStrengthening env U)
    {Γ As : List VExpr} {A A' b : VExpr} {u : VLevel}
    (hΓ : OnCtx ((VExpr.liftTele 1 As 0).reverse ++ A :: Γ) (env.IsType U))
    (H : env.HasType U ((VExpr.liftTele 1 As 0).reverse ++ A :: Γ)
      (b.liftN 1 As.length) (.sort u)) :
    env.HasType U ((VExpr.liftTele 1 As 0).reverse ++ A' :: Γ) (b.liftN 1 As.length) (.sort u) := by
  have W : Ctx.LiftN 1 As.length (As.reverse ++ Γ)
      ((VExpr.liftTele 1 As 0).reverse ++ A :: Γ) := by
    have := Ctx.LiftN.tele (As := As) (n := 1) (k := 0) (Γ := Γ) (Γ' := A :: Γ) Ctx.LiftN.one
    rwa [Nat.zero_add] at this
  have W' : Ctx.LiftN 1 As.length (As.reverse ++ Γ)
      ((VExpr.liftTele 1 As 0).reverse ++ A' :: Γ) := by
    have := Ctx.LiftN.tele (As := As) (n := 1) (k := 0) (Γ := Γ) (Γ' := A' :: Γ) Ctx.LiftN.one
    rwa [Nat.zero_add] at this
  exact HT.hasType_sort_swapSkipped henv hΓ W W' H

/-! ## 4. The general (non-sort) swap, and what it costs

The corner also swaps at judgements whose type is not a sort (`projMotiveTerm_hasType_swapped`,
`projGen_hiota`).  There the type cannot be recovered from `SortDescend`, and the ascription
trick of `Strengthen.lean` §3 -- hence `IsDefEqU.forallE_inv`, hence the hole
`WF.rigidShapeUniqNS` -- is needed.  Stated here so the two prices sit side by side. -/

variable! (henv : VEnv.WF env) in
/-- The general swap from the typing half.  **Cone**: `IsDefEqU.forallE_inv_stratified` *and*
`WF.rigidShapeUniqNS`, the second inherited from `TypingStrengthening.hasType_inv`. -/
theorem TypingStrengthening.hasType_swapSkipped (HT : TypingStrengthening env U)
    {Γ₀ Γ Γ' : List VExpr} {b B : VExpr} {n k : Nat}
    (hΓ : OnCtx Γ (env.IsType U)) (W : Ctx.LiftN n k Γ₀ Γ) (W' : Ctx.LiftN n k Γ₀ Γ')
    (H : env.HasType U Γ (b.liftN n k) (B.liftN n k)) :
    env.HasType U Γ' (b.liftN n k) (B.liftN n k) :=
  (HT.hasType_inv henv W hΓ H).weakN henv W'

/-! ## 5. Anti-vacuity: the hypothesis is inhabited, and §3 fires with nothing left over

`docs/vacuity-ledger.md` §0: a result whose hypothesis is unsatisfiable is worthless.
`TypingStrengthening` has an inhabitant -- `StrengthenVerdict.lean`'s `exists_univInhabEnv`
supplies a `VEnv.WF` environment satisfying `StrengtheningTarget` at every `U`, and the target
implies the typing half.  **Read the scope statement with it**: that environment declares
`univInhab : ∀ (α : Sort u), α`, so it is inconsistent, and
`univInhab_no_uninhabited_entry` says its contexts have no uninhabited entry.  So this is a
*satisfiability* witness -- it shows the hypothesis is not contradictory -- and it is **not**
evidence that the hypothesis is easy, nor that the conclusion has content at that environment
(where the proved inhabited-entry half of `Strengthen.lean` §1 already covers everything). -/

/-- **The hypothesis of §1-§4 is inhabited**, at a `VEnv.WF` environment, for every `U`. -/
theorem exists_typingStrengthening_env :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ U, TypingStrengthening env U := by
  obtain ⟨env, hwf, h⟩ := exists_univInhabEnv
  exact ⟨env, hwf, fun U => Strengthening.typing (StrengtheningTarget.strengthening (h U))⟩

/-- …and there §3's swap holds **unconditionally**, quantified over the universe count, the
context, both binder types, the subject and the level. -/
theorem exists_env_hasType_sort_swapSkipped_one :
    ∃ env : VEnv, VEnv.WF env ∧
      ∀ (U : Nat) (Γ : List VExpr) (A A' b : VExpr) (u : VLevel),
        OnCtx (A :: Γ) (env.IsType U) →
        env.HasType U (A :: Γ) (b.liftN 1 0) (.sort u) →
        env.HasType U (A' :: Γ) (b.liftN 1 0) (.sort u) := by
  obtain ⟨env, hwf, h⟩ := exists_typingStrengthening_env
  exact ⟨env, hwf, fun U _ _ _ _ _ hΓ H =>
    TypingStrengthening.hasType_sort_swapSkipped_one hwf (h U) hΓ H⟩

/-! ## 6. Negative controls

Three, in increasing strength. -/

/-- **(a) The lift restriction is proper.**  `.bvar 0` is not in the image of `liftN 1 · 0`, so
there are judgements over `A :: Γ` that §3 does not apply to -- the lemma is not the (false)
claim that every judgement transports across a binder change. -/
theorem bvar0_not_liftN_one (b : VExpr) : VExpr.bvar 0 ≠ b.liftN 1 0 := by
  cases b with
  | bvar i => simp [VExpr.liftN, liftVar]; omega
  | _ => simp [VExpr.liftN]

/-- **(b) The swap is not an instance of weakening.**  At `n = 0` a `Ctx.LiftN` is the identity,
so the two contexts of §3 are related by a lifting witness only when they are equal. -/
theorem liftN_zero_ctx_eq : ∀ {k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN 0 k Γ Γ' → Γ = Γ'
  | _, _, _, .zero As h => by
    cases List.eq_nil_of_length_eq_zero h; rfl
  | _, _, _, .succ W => by rw [liftN_zero_ctx_eq W, VExpr.liftN_zero]

/-- A `Ctx.LiftN n k` adds exactly `n` entries. -/
theorem liftN_ctx_length : ∀ {n k : Nat} {Γ Γ' : List VExpr},
    Ctx.LiftN n k Γ Γ' → Γ'.length = n + Γ.length
  | _, _, _, _, .zero As h => by simp [h]
  | _, _, _, _, .succ W => by simp [liftN_ctx_length W]; omega

/-- …hence the two contexts of the swap's own one-binder instance are related by **no** lifting
witness once the binders differ: the transport in §3 is genuinely not weakening, and no
composition of weakenings can replace it. -/
theorem not_liftN_swap {A A' : VExpr} {Γ : List VExpr} (hne : A ≠ A') {n k : Nat} :
    ¬ Ctx.LiftN n k (A :: Γ) (A' :: Γ) := by
  intro W
  have h := liftN_ctx_length W
  simp at h
  cases (by omega : n = 0)
  exact absurd (List.cons.inj (liftN_zero_ctx_eq W)).1 hne

/-- **(c) The `n = 0` degeneracy carries no content**: there the swap's conclusion *is* its
hypothesis, so §3's content lives entirely at `n ≥ 1`. -/
theorem hasType_sort_swapSkipped_zero {Γ₀ Γ Γ' : List VExpr} {b : VExpr} {u : VLevel} {k : Nat}
    (W : Ctx.LiftN 0 k Γ₀ Γ) (W' : Ctx.LiftN 0 k Γ₀ Γ')
    (H : env.HasType U Γ (b.liftN 0 k) (.sort u)) :
    env.HasType U Γ' (b.liftN 0 k) (.sort u) := by
  cases liftN_zero_ctx_eq W; cases liftN_zero_ctx_eq W'; exact H

end VEnv
end Lean4Lean
