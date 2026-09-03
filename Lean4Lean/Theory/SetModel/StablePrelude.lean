import Lean4Lean.Theory.SetModel.StableGuarded

/-!
# `PropSplit.Stable` at the prelude: the dependence factors, and only the `lift` half is used

`SetModel/EqIotaRule.lean` and `SetModel/IffIotaRule.lean` assemble `InductOracleOK` at the two
non-trivial `.induct` steps of `leanPrelude`, each under two hypotheses: an environment inequality
`hle` (discharged at `preludeEnv`) and `hS : L.Stable`, which is not discharged anywhere in this
tree.  `docs/handoff-setmodel.md` §24.9 item 1 prices removing `hS` at ~270 lines across both
blocks, on the model that the ι-rule's `rhs` must be recomputed at the ι-context.

**That model is wrong, and this file measures why.**  `PropSplit.Stable` has four fields, and they
split into two independent halves that no consumer mixes:

| half | fields | consumer |
|---|---|---|
| `StableLift` | `prop_liftN`, `proof_liftN` | `InterpSubst.interp_liftN` (lines 224, 239, 261) |
| `StableInst` | `prop_instN`, `proof_instN` | `InterpSubst.interp_inst` (lines 399, 419, 446) |

`InterpSound.interp_closed_ctx` — the *only* thing either ι-rule file takes `hS` for
(`EqIotaRule.lean:505`, `IffIotaRule.lean:814`; every other occurrence of `hS` in those two files
is pure threading) — is a corollary of `interp_liftN` alone.  So the two ι-rule results depend on
`StableLift` and **not** on `StableInst`.

And `StableLift` is **free** at the `L` the prelude consumer actually uses.
`UpperBound.OracleInput` fixes that `L` to be `propSplitUp env 0 henv hU hT`
(`SetModel/UpperBound.lean:98-101`), and §3 below proves
`(propSplitUp env nv henv hU hT).StableLift` from `env.Ordered` and nothing else — the same
`PropSplitUp.isPropUp_liftN` / `isProofUp_liftN` that `propSplitUp_stable` already uses for those
two fields.  No `InstDescendUp`, no `PropDescend`, no strengthening.

## What that buys, exactly

§5 restates `interp_liftN` and `interp_closed_ctx` under `StableLift` (`interp_liftN_lift`,
`interp_closed_ctx_lift`).  The proof of `interp_liftN_lift` is `InterpSubst.interp_liftN`'s
verbatim, because `StableLift`'s two fields carry the same names as `Stable`'s.  With those in
hand, the edit that removes `hS : L.Stable` from the two ι-rule files is:

* add `import Lean4Lean.Theory.SetModel.StablePrelude` to each;
* replace `hS : L.Stable` by `hS : L.StableLift` in six declarations of `EqIotaRule.lean`
  (lines 454, 735, 882, 901, 913, 1017) and six of `IffIotaRule.lean`
  (lines 734, 1187, 1385, 1402, 1413, 1497) — mechanically, `s/(hS : L\.Stable)/(hS : L.StableLift)/g`;
* replace `interp_closed_ctx M L hS` by `interp_closed_ctx_lift M L hS` at `EqIotaRule.lean:505`
  and `IffIotaRule.lean:814`.

**Sixteen lines, no new proof in either file, and this was compiled, not read off**: scratch
copies of both files with exactly those substitutions elaborate clean (`lake env lean`, no error,
no warning), and at `L := propSplitUp envF nv henv hU hT` the two headline results then discharge
`hS` from `propSplitUp_stableLift` and are left with `hle` alone, at
`[propext, Classical.choice, Quot.sound]`.  Nothing outside those two files calls any of the
twelve declarations (checked by grep over the whole repository: the only other mentions of
`inductOracleOK_Eq` / `inductOracleOK_Iff` are the import comments in
`Theory/Equiconsistency.lean` and one prose line in `SetModel/InductOracleAudit.lean:321`).

**I have not made that edit** — those two files are outside this stream's ownership;
`docs/handoff-stable.md` §3 states it as a diff for the orchestrator.  Not ~270 lines.

## What it does NOT buy — read this before quoting the above

1. `StableInst` is still needed by `InterpSubst.interp_inst`, hence by `ModelFits`, hence by
   `UpperBound.consistent_of_inputs` through `modelFits_of_propSplitUp_inputs`.  So
   **`InstDescendInput` (Input 2) does not leave the main theorem.**  What leaves is its
   appearance in the *three `.induct` steps of the prelude*, which is what §24.9 item 1 asks for
   and no more.
2. Outcome "supply `L.Stable` itself at the consumer's `L`" is **exactly Input 2**, not less:
   §4's `propSplitUp_stable_iff` proves
   `(propSplitUp env nv henv hU hT).Stable ↔ env.InstDescendUp nv`.
   So there is no cleverer proof of the full `Stable` against this split; that route is closed,
   and the `lift`/`inst` factoring is the only way through.
3. Nothing here is a claim *at* `preludeEnv` unconditionally.  `propSplitUp` needs the
   **unguarded** `PropTypeAgree env 0` as *data* (Input 1), which is open at `preludeEnv`.  The
   split that is data there — `InstDescendBvar.propSplitUpOnPreludeEnv`, built from the *guarded*
   imports — is **not** `StableLift`, and §6 refutes it rather than merely failing to prove it.
   (That object also carries `sorryAx`, through `PropAgreeWall.preludeEnv_propUniqOnCtx` /
   `preludeEnv_propTypeAgreeOnCtx` = `VEnv.WF.propUniqOn` / `WF.propTypeAgreeOn`; §6 says so.)
4. `StableGuarded.preludeEnv_stableOn_liftN` is **not** most of this: it is the two `lift` fields
   of `PropSplit.StableOn` — the *guarded* structure — and `Stable.stableOn` runs from `Stable` to
   `StableOn`, i.e. the wrong way for a consumer that needs `Stable`.  `StableGuarded` §4 further
   proves the guard **cannot** be threaded into `Stable` while `interp_liftN` keeps its
   hypotheses.  What replaces that route here is not a guard at all: it is dropping the two `inst`
   fields, which the consumer genuinely does not use.

## Negative control

§7 builds a genuine `PropSplit env 0` — all six fields, `prop_sound` and `proof_sound` included —
at **exactly §3's hypotheses**, that is **not** `StableLift` and hence not `Stable`.  So
`stableLift_is_a_real_restriction` says: those hypotheses give both a `StableLift` split and a
non-`StableLift` split, and §3's freeness result is therefore a genuine selection rather than an
everywhere-true statement.

§6 is a second, stronger negative: the *guarded* split `propSplitUpOn` — the one whose data is
cheapest at `preludeEnv` — is **provably never** `StableLift`, at every environment.  So §3's
reliance on the unguarded predicate (hence on Input 1 as data) is not laziness; the guarded route
is closed.
-/

namespace Lean4Lean

namespace SetModel

/-! ## 1. The two halves of `Stable` -/

variable {env : VEnv} {nv : ℕ}

/-- **The lift half of `PropSplit.Stable`.**  Field names deliberately identical to
`PropSplit.Stable`'s, so that a proof written against `Stable` and using only these two fields
compiles against `StableLift` unchanged. -/
structure PropSplit.StableLift (L : PropSplit env nv) : Prop where
  prop_liftN : ∀ {n k : ℕ} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
    ∀ (ls : List ℕ) (A : VExpr), (L.IsPropAt ls Γ' (A.liftN n k) ↔ L.IsPropAt ls Γ A)
  proof_liftN : ∀ {n k : ℕ} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
    ∀ (ls : List ℕ) (e : VExpr), (L.IsProofAt ls Γ' (e.liftN n k) ↔ L.IsProofAt ls Γ e)

/-- **The substitution half of `PropSplit.Stable`.** -/
structure PropSplit.StableInst (L : PropSplit env nv) : Prop where
  prop_instN : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
    ∀ (ls : List ℕ) (B : VExpr), (L.IsPropAt ls Γ (B.inst e₀ k) ↔ L.IsPropAt ls Γ₁ B)
  proof_instN : ∀ {Γ₀ : List VExpr} {e₀ A₀ : VExpr} {k : ℕ} {Γ₁ Γ : List VExpr},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.HasType nv Γ₀ e₀ A₀ →
    ∀ (ls : List ℕ) (e : VExpr), (L.IsProofAt ls Γ (e.inst e₀ k) ↔ L.IsProofAt ls Γ₁ e)

theorem PropSplit.Stable.stableLift {L : PropSplit env nv} (hS : L.Stable) : L.StableLift :=
  ⟨hS.prop_liftN, hS.proof_liftN⟩

theorem PropSplit.Stable.stableInst {L : PropSplit env nv} (hS : L.Stable) : L.StableInst :=
  ⟨hS.prop_instN, hS.proof_instN⟩

/-- **The factoring is exact**: `Stable` is the conjunction of its two halves, so nothing is lost
by working with them separately. -/
theorem PropSplit.stable_iff_lift_and_inst {L : PropSplit env nv} :
    L.Stable ↔ L.StableLift ∧ L.StableInst :=
  ⟨fun h => ⟨h.stableLift, h.stableInst⟩,
   fun ⟨h1, h2⟩ => ⟨h1.prop_liftN, h1.proof_liftN, h2.prop_instN, h2.proof_instN⟩⟩

end SetModel

end Lean4Lean

namespace Lean4Lean

/-! ## 3. `StableLift` is FREE at the split the prelude consumer uses -/

namespace SetModel

variable {env : VEnv} {nv : ℕ}

/-- **The headline of this file.**  `StableLift` for the lift-closed split, from `env.Ordered`
alone.

`hU` and `hT` occur only as *data* arguments of `propSplitUp` — they are the fields
`prop_sound`/`proof_sound`, and neither is consulted below.  Compare
`PropSplitUp.propSplitUp_stable`, which is this plus `hI : env.InstDescendUp nv`: the extra
hypothesis is spent entirely on the two `inst` fields (§4 shows it is spent *exactly* there). -/
theorem propSplitUp_stableLift (henv : env.Ordered) (hU : env.PropUniq nv)
    (hT : env.PropTypeAgree nv) : (propSplitUp env nv henv hU hT).StableLift where
  prop_liftN W _ _ := VEnv.isPropUp_liftN henv W
  proof_liftN W _ _ := VEnv.isProofUp_liftN henv W

/-- The same statement quantified over the split rather than fixing it: **some**
`PropSplit env nv` is `StableLift`, from `Ordered` + Input 1 + `PropUniq`.  Compare
`PropSplitUp.exists_stable_propSplitUp`, which additionally needs `InstDescendUp`. -/
theorem exists_stableLift_propSplit (henv : env.Ordered) (hU : env.PropUniq nv)
    (hT : env.PropTypeAgree nv) : ∃ L : PropSplit env nv, L.StableLift :=
  ⟨_, propSplitUp_stableLift henv hU hT⟩

/-- …and with `PropUniq` taken from the goal's own inconsistency witness, as
`UpperBound.consistent_of_inputs` does.  This is the exact counterpart of
`PropSplitUp.exists_stable_propSplitUp_of_agree` with `InstDescendUp` **deleted**. -/
theorem exists_stableLift_propSplit_of_agree {env : VEnv} (nv : ℕ) (henv : env.Ordered)
    (hf : ∃ e, env.HasType 0 [] e falseProp) (hT : env.PropTypeAgree 0) :
    ∃ L : PropSplit env nv, L.StableLift :=
  ⟨_, propSplitUp_stableLift henv
    (VEnv.PropUniq.of_zero (VEnv.PropUniq.of_propTypeAgree henv hf hT) nv)
    (VEnv.PropTypeAgree.of_zero hT nv)⟩

/-! ## 4. …and the other half is *exactly* Input 2, so the full `Stable` cannot be had cheaper -/

/-- **`StableInst` for the lift-closed split is `InstDescendUp` on the nose.**  The `←` direction
is `PropSplitUp.propSplitUp_stable`'s two `inst` fields; the `→` direction reads the descent half
of each `↔` off.  So the residual is not an artefact of how `propSplitUp_stable` is proved. -/
theorem propSplitUp_stableInst_iff (henv : env.Ordered) (hU : env.PropUniq nv)
    (hT : env.PropTypeAgree nv) :
    (propSplitUp env nv henv hU hT).StableInst ↔ env.InstDescendUp nv := by
  refine ⟨fun h => ⟨fun W h₀ hp => (h.prop_instN W h₀ _ _).mp hp,
      fun W h₀ hp => (h.proof_instN W h₀ _ _).mp hp⟩, fun hI => ⟨?_, ?_⟩⟩
  · exact fun W h₀ _ _ => ⟨hI.prop_inst W h₀, VEnv.isPropUp_instN_up henv W h₀⟩
  · exact fun W h₀ _ _ => ⟨hI.proof_inst W h₀, VEnv.isProofUp_instN_up henv W h₀⟩

/-- **Outcome "prove `L.Stable` at the consumer's `L`" is equivalent to Input 2.**

`UpperBound.InstDescendInput` is `∀ env, env.LeanWF → env.InstDescendUp 0`, and this says the
`Stable` the ι-rule files ask for, at the split `UpperBound.OracleInput` fixes, *is* its
conclusion.  So that outcome is not cheaper than Input 2 by any margin: it is Input 2. -/
theorem propSplitUp_stable_iff (henv : env.Ordered) (hU : env.PropUniq nv)
    (hT : env.PropTypeAgree nv) :
    (propSplitUp env nv henv hU hT).Stable ↔ env.InstDescendUp nv := by
  refine ⟨fun h => (propSplitUp_stableInst_iff henv hU hT).1 h.stableInst, fun hI => ?_⟩
  exact PropSplit.stable_iff_lift_and_inst.2
    ⟨propSplitUp_stableLift henv hU hT, (propSplitUp_stableInst_iff henv hU hT).2 hI⟩

end SetModel

end Lean4Lean

namespace Lean4Lean

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ## 5. `interp_liftN` and `interp_closed_ctx` under `StableLift`

`InterpSubst.interp_liftN`'s proof, verbatim.  The only change is the hypothesis' **type**:
`L.Stable` becomes `L.StableLift`.  Nothing else in the ninety lines moves, because the two
fields the proof uses (`InterpSubst.lean:224, 239, 261`) keep their names — which is why
`StableLift`'s fields were named as they were in §1.

This is a restatement, not new mathematics; its value is that it is the *measurement* proving the
`inst` fields are unused there.  If `InterpSubst.lean` is ever edited to take `StableLift`
directly, this section should be deleted rather than kept in parallel. -/

section Weakening

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {nv : ℕ} (M : ModelData V) (L : PropSplit env nv)

theorem interp_liftN_lift (hS : L.StableLift) {n j : ℕ} :
    ∀ (e : VExpr) {k : ℕ} {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' → Γ.length - k = j →
      e.ClosedN Γ.length → ∀ {ρ ρ' : V}, ρ ∈ interpCtx M L Γ → ρ' ∈ interpCtx M L Γ' →
      AgreePos n j Γ.length ρ' ρ →
      (interp M L Γ' (e.liftN n k)).toFun ρ' = (interp M L Γ e).toFun ρ
  | .bvar i, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    have hlen := Ctx.LiftN.length W
    have hkle := Ctx.LiftN.le W
    have hi : i < Γ.length := hcl
    rw [show (VExpr.bvar i).liftN n k = .bvar (liftVar n i k) from rfl,
      interp_bvar, interp_bvar]
    have hpos : Γ'.length - 1 - liftVar n i k = liftPos n j (Γ.length - 1 - i) := by
      simp only [liftPos, liftVar, hlen, ← hj]
      split <;> split <;> omega
    rw [hpos]
    exact hag _ (by omega)
  | .sort u, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    rw [show (VExpr.sort u).liftN n k = .sort u from rfl, interp_sort, interp_sort]
  | .const c us, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    rw [show (VExpr.const c us).liftN n k = .const c us from rfl, interp_const, interp_const]
  | .app f a, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    obtain ⟨hf, ha⟩ := hcl
    have hsplit : L.IsProof M Γ' (f.liftN n k) ↔ L.IsProof M Γ f := by
      exact hS.proof_liftN W M.ls f
    by_cases hp : L.IsProof M Γ f
    · rw [show (VExpr.app f a).liftN n k = .app (f.liftN n k) (a.liftN n k) from rfl,
        interp_app_proof M L (hsplit.mpr hp), interp_app_proof M L hp]
    · rw [show (VExpr.app f a).liftN n k = .app (f.liftN n k) (a.liftN n k) from rfl,
        interp_app_type M L (fun h => hp (hsplit.mp h)), interp_app_type M L hp,
        interp_liftN_lift hS f W hj hf hρ hρ' hag, interp_liftN_lift hS a W hj ha hρ hρ' hag]
  | .lam A b, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    obtain ⟨hA, hb⟩ := hcl
    have hlen := Ctx.LiftN.length W
    have hkle := Ctx.LiftN.le W
    have W' : Ctx.LiftN n (k + 1) (A :: Γ) (A.liftN n k :: Γ') := W.succ
    have hj' : (A :: Γ).length - (k + 1) = j := by simp; omega
    have hsplit : L.IsProof M (A.liftN n k :: Γ') (b.liftN n (k + 1)) ↔
        L.IsProof M (A :: Γ) b := by
      exact hS.proof_liftN W' M.ls b
    by_cases hp : L.IsProof M (A :: Γ) b
    · rw [show (VExpr.lam A b).liftN n k = .lam (A.liftN n k) (b.liftN n (k + 1)) from rfl,
        interp_lam_proof M L (hsplit.mpr hp), interp_lam_proof M L hp]
    · rw [show (VExpr.lam A b).liftN n k = .lam (A.liftN n k) (b.liftN n (k + 1)) from rfl,
        interp_lam_type M L (fun h => hp (hsplit.mp h)), interp_lam_type M L hp]
      have hAeq := interp_liftN_lift hS A W hj hA hρ hρ' hag
      ext y
      rw [mem_mkLam_iff, mem_mkLam_iff, hAeq]
      refine exists_congr fun v ↦ and_congr_right fun hv ↦ ?_
      rw [interp_liftN_lift hS b W' hj' hb
        ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, v, by rwa [← hAeq] at hv ⊢, rfl⟩)
        ((mem_interpCtx_cons M L).mpr ⟨ρ', hρ', v, by rwa [hAeq], rfl⟩)
        (AgreePos.snoc M L (by omega) rfl (by omega) hρ hρ' hag v)]
  | .forallE A B, k, Γ, Γ', W, hj, hcl, ρ, ρ', hρ, hρ', hag => by
    obtain ⟨hA, hB⟩ := hcl
    have hlen := Ctx.LiftN.length W
    have hkle := Ctx.LiftN.le W
    have W' : Ctx.LiftN n (k + 1) (A :: Γ) (A.liftN n k :: Γ') := W.succ
    have hj' : (A :: Γ).length - (k + 1) = j := by simp; omega
    have hsplit : L.IsProp M (A.liftN n k :: Γ') (B.liftN n (k + 1)) ↔
        L.IsProp M (A :: Γ) B := by
      exact hS.prop_liftN W' M.ls B
    have hAeq := interp_liftN_lift hS A W hj hA hρ hρ' hag
    have hBeq : ∀ v ∈ (interp M L Γ A).toFun ρ,
        (interp M L (A.liftN n k :: Γ') (B.liftN n (k + 1))).toFun (snoc ρ' v) =
          (interp M L (A :: Γ) B).toFun (snoc ρ v) := by
      intro v hv
      exact interp_liftN_lift hS B W' hj' hB
        ((mem_interpCtx_cons M L).mpr ⟨ρ, hρ, v, hv, rfl⟩)
        ((mem_interpCtx_cons M L).mpr ⟨ρ', hρ', v, by rwa [hAeq], rfl⟩)
        (AgreePos.snoc M L (by omega) rfl (by omega) hρ hρ' hag v)
    by_cases hp : L.IsProp M (A :: Γ) B
    · rw [show (VExpr.forallE A B).liftN n k
          = .forallE (A.liftN n k) (B.liftN n (k + 1)) from rfl,
        interp_forallE_prop M L (hsplit.mpr hp), interp_forallE_prop M L hp]
      ext z
      rw [mem_mkForallProp_iff, mem_mkForallProp_iff, hAeq]
      exact and_congr_right fun _ ↦ forall₂_congr fun v hv ↦ by rw [hBeq v hv]
    · rw [show (VExpr.forallE A B).liftN n k
          = .forallE (A.liftN n k) (B.liftN n (k + 1)) from rfl,
        interp_forallE_type M L (fun h => hp (hsplit.mp h)), interp_forallE_type M L hp]
      ext f
      rw [mem_mkForallType_iff, mem_mkForallType_iff, hAeq]
      refine and_congr ?_ ?_
      · congr! 2
        ext y
        rw [mem_mkFamUnion_iff, mem_mkFamUnion_iff, hAeq]
        exact exists_congr fun v ↦ and_congr_right fun hv ↦ by
          rw [hBeq v hv]
      · exact forall₂_congr fun v hv ↦ forall_congr' fun y ↦ imp_congr_right fun _ ↦ by
          rw [hBeq v hv]


/-- **`InterpSound.interp_closed_ctx` under `StableLift`.**  Its proof, verbatim, against
`interp_liftN_lift`.  This is the single fact `EqIotaRule.lean` and `IffIotaRule.lean` take
`hS : L.Stable` for. -/
theorem interp_closed_ctx_lift (hS : L.StableLift) {e : VExpr} (hcl : e.ClosedN 0)
    {Γ : List VExpr} {ρ : V} (hρ : ρ ∈ interpCtx M L Γ) :
    (interp M L Γ e).toFun ρ = (interp M L [] e).toFun ∅ := by
  have hW : Ctx.LiftN Γ.length 0 [] Γ := by
    have h0 := Ctx.LiftN.zero (n := Γ.length) (Γ := ([] : List VExpr)) Γ rfl
    rwa [List.append_nil] at h0
  have hnil : (∅ : V) ∈ interpCtx M L ([] : List VExpr) := by
    rw [interpCtx_nil]; exact mem_singleton_iff.2 rfl
  have := interp_liftN_lift M L hS (n := Γ.length) (j := 0) e (k := 0) hW rfl hcl
    (ρ := ∅) (ρ' := ρ) hnil hρ (fun _ h => absurd h (Nat.not_lt_zero _))
  rwa [hcl.liftN_eq (Nat.zero_le _)] at this

end Weakening

end SetModel

end Lean4Lean

namespace Lean4Lean

namespace SetModel

namespace StablePrelude

/-! ## 6. Where `StableLift` **cannot** be had: the *guarded* split is never `StableLift`

§3 delivers `StableLift` at `propSplitUp`, whose *data* needs the **unguarded** `PropTypeAgree
env 0` — `UpperBound.PropTypeAgreeInput`, open at `preludeEnv`.  The obvious hope is to use
`propSplitUpOn` instead, whose data needs only the *guarded* statements, and which
`InstDescendBvar` §8b instantiates at `preludeEnv` as `propSplitUpOnPreludeEnv`.

**That hope is refuted here, not merely unproved, and at every environment.**
`StableGuarded.isPropUpOn_liftN` needs `OnCtx` on the lift's target and
`StableGuarded.notOnCtx_lift_target` exhibits a target the guard excludes; what follows turns
that observation into `¬ (propSplitUpOn env 0 henv hU hT).StableLift`, for **every** `env` and
every choice of the two guarded inputs.

The witness is `Ctx.LiftN 1 0 [] [Sort (param 0)]`.  A sort is invariant under `lift'`, so the
junk entry survives into *every* context above the target and `not_isType_sort_param` kills the
guard there — no de Bruijn arithmetic is needed, which is why this entry rather than
`PropAgreeWall`'s `.bvar 0` is used. -/

variable {env : VEnv} {nv : ℕ}

/-- `StrengthenVerdict.onCtx_levelWF`, re-proved locally to avoid importing a `Theory/Typing`
module another stream is editing.  Three lines, `IsDefEq.levelWF` and nothing else. -/
theorem onCtx_levelWF {U : ℕ} :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → OnCtx Γ (fun _ A => A.LevelWF U)
  | [], _ => trivial
  | _ :: _, ⟨h1, _, h2⟩ => ⟨onCtx_levelWF h1, (VEnv.IsDefEq.levelWF h2 (onCtx_levelWF h1)).1⟩

/-- **No well-formed context types `Sort (param 0)` at `nv = 0`.**
`StableGuarded.not_isType_sort_param` with its `LevelWF` hypothesis discharged. -/
theorem not_isType_sortParam_of_onCtx {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType 0)) :
    ¬ env.IsType 0 Γ (.sort (.param 0)) :=
  StableGuarded.not_isType_sort_param (onCtx_levelWF hΓ)

/-- **No context above `[Sort (param 0)]` is well-formed**, at any environment, for any lift.
Induction on the lift derivation; the `cons` case uses that a sort is `lift'`-invariant. -/
theorem not_onCtx_of_lift'_sortParam : ∀ {l : Lift} {Γ Γ' : List VExpr},
    Ctx.Lift' l Γ Γ' → Γ = [(VExpr.sort (.param 0) : VExpr)] → ¬ OnCtx Γ' (env.IsType 0) := by
  intro l Γ Γ' W
  induction W with
  | refl => rintro rfl h; exact not_isType_sortParam_of_onCtx h.1 h.2
  | skip _ ih => exact fun hΓ h => ih hΓ h.1
  | cons _ _ =>
    rintro ⟨⟩ h
    refine not_isType_sortParam_of_onCtx h.1 ?_
    simpa only [VExpr.lift'] using h.2

/-- **The guarded predicate is empty above the junk target**, so one side of the `lift` field is
`False` there. -/
theorem not_isPropUpOn_sortParam_target {ls : List ℕ} {A : VExpr} :
    ¬ env.IsPropUpOn 0 ls [(VExpr.sort (.param 0) : VExpr)] A := by
  rintro ⟨l, Γ', u, W, hΓ', -, -, -⟩
  exact not_onCtx_of_lift'_sortParam W rfl hΓ'

/-- **REFUTED, at every environment: the guarded split is not `StableLift`.**

So the route "get `StableLift` from the inputs the tree already has at `preludeEnv`" is closed.
`propSplitUp` — which is `StableLift` (§3) — needs Input 1 as *data*, and that is the honest
boundary of §3.

Note what is **not** claimed: this does not say no `PropSplit preludeEnv 0` is `StableLift`.  It
says this one is not.  A split whose predicate is the *unguarded* up-closure is, and its
existence is exactly `PropTypeAgree preludeEnv 0`. -/
theorem not_stableLift_propSplitUpOn (henv : env.Ordered) (hU : env.PropUniqOnCtx 0)
    (hT : env.PropTypeAgreeOnCtx 0) : ¬ (propSplitUpOn env 0 henv hU hT).StableLift := by
  intro h
  have hW : Ctx.LiftN 1 0 ([] : List VExpr) [(VExpr.sort (.param 0) : VExpr)] := Ctx.LiftN.one
  exact not_isPropUpOn_sortParam_target
    ((h.prop_liftN hW [] (.forallE (.sort .zero) (.bvar 0))).mpr
      (VEnv.IsPropUpOn.of_hasType (u := .zero) (Γ := []) trivial trivial allProp_hasType rfl))

/-- …and therefore not `Stable` either.  Compare `StableGuarded.propSplitUpOn_stableOn`, which
gives the same split's two **guarded** `lift` fields for free: the guard is not decoration, it is
the whole difference between a theorem and a false statement here. -/
theorem not_stable_propSplitUpOn (henv : env.Ordered) (hU : env.PropUniqOnCtx 0)
    (hT : env.PropTypeAgreeOnCtx 0) : ¬ (propSplitUpOn env 0 henv hU hT).Stable :=
  fun h => not_stableLift_propSplitUpOn henv hU hT h.stableLift

/-- The `preludeEnv` instance.  **Carries `sorryAx`, and not from anything in this file**: the
*object* `InstDescendBvar.propSplitUpOnPreludeEnv` is built from
`PropAgreeWall.preludeEnv_propUniqOnCtx` / `preludeEnv_propTypeAgreeOnCtx`, both of which are
`VEnv.WF.propUniqOn` / `WF.propTypeAgreeOn` (`SetModel/NotProofNoModel.lean`) and both of which
print `sorryAx`.  `not_stableLift_propSplitUpOn` above is `sorryAx`-free and is where the content
lives; this corollary only names the object.

**So `InstDescendBvar` §8b's description of `propSplitUpOnPreludeEnv` as coming "from the two
guarded imports, both of which are theorems there" is true only of `sorryAx`-tainted theorems.**
Route B (`PropAgreeWall.preludeEnv_propTypeAgreeOnCtx_of_stratifiedN`) is the `sorryAx`-free
version and is conditional on `∀ n, PropTypeAgreeN` and `∀ n, PropUniqN`. -/
theorem not_stableLift_propSplitUpOnPreludeEnv :
    ¬ (InstDescendBvar.propSplitUpOnPreludeEnv).StableLift :=
  not_stableLift_propSplitUpOn _ _ _

/-! ## 7. Negative control: `StableLift` is a real restriction on `PropSplit`

§3 proves a `StableLift` freeness result, so the vacuity question is whether `StableLift` is a
restriction at all.  It is, and the control is stated at **exactly §3's hypotheses**, so the two
sit side by side: from `Ordered ∧ PropUniq 0 ∧ PropTypeAgree 0` one gets both a `PropSplit env 0`
that is `StableLift` (§3) and one that is not (`junkSplitOf` below).  No `sorryAx`, no fixed
environment.

The doctoring is confined to contexts `prop_sound` cannot see: `IsPropAt` is the lift-closed
predicate conjoined with `Γ ≠ [Sort (param 0)]`, and `[Sort (param 0)]` is not `OnCtx`
(§6), which is exactly why `prop_sound` survives.  `Stable`, being stated over raw contexts, does
see it. -/

/-- A genuine `PropSplit env 0` — all six fields — that is not `StableLift`. -/
noncomputable def junkSplitOf (env : VEnv) (henv : env.Ordered) (hU : env.PropUniq 0)
    (hT : env.PropTypeAgree 0) : PropSplit env 0 where
  IsPropAt ls Γ A := env.IsPropUp 0 ls Γ A ∧ Γ ≠ [.sort (.param 0)]
  IsProofAt := env.IsProofUp 0
  decProp _ _ _ := Classical.propDecidable _
  decProof _ _ _ := Classical.propDecidable _
  prop_sound := by
    intro ls Γ A u hΓ hw ht
    have hne : Γ ≠ [(VExpr.sort (.param 0) : VExpr)] := by
      rintro rfl
      exact not_isType_sortParam_of_onCtx (env := env) (Γ := []) trivial hΓ.2
    rw [and_iff_left hne]
    exact VEnv.isPropUp_iff henv hU hw ht
  proof_sound := fun _ hw he hA => VEnv.isProofUp_iff henv hT hw he hA

/-- **The negative control.**  `junkSplitOf` is not `StableLift`: at the lift
`Ctx.LiftN 1 0 [] [Sort (param 0)]`, the right side of `prop_liftN` holds at `∀ p : Prop, p`
(`PropSplitUp.isPropUp_falseProp`) and the left side is `False` by construction. -/
theorem junkSplitOf_not_stableLift (henv : env.Ordered) (hU : env.PropUniq 0)
    (hT : env.PropTypeAgree 0) : ¬ (junkSplitOf env henv hU hT).StableLift := by
  intro h
  have hW : Ctx.LiftN 1 0 ([] : List VExpr) [(VExpr.sort (.param 0) : VExpr)] := Ctx.LiftN.one
  have hR : (junkSplitOf env henv hU hT).IsPropAt [] ([] : List VExpr)
      (.forallE (.sort .zero) (.bvar 0)) :=
    ⟨VEnv.IsPropUp.of_hasType (u := .zero) (Γ := []) trivial allProp_hasType rfl, by simp⟩
  exact ((h.prop_liftN hW [] (.forallE (.sort .zero) (.bvar 0))).mpr hR).2 rfl

/-- …hence not `Stable`.  So neither property is everywhere-true on `PropSplit`, and §3 is not
the trivial statement. -/
theorem junkSplitOf_not_stable (henv : env.Ordered) (hU : env.PropUniq 0)
    (hT : env.PropTypeAgree 0) : ¬ (junkSplitOf env henv hU hT).Stable :=
  fun h => junkSplitOf_not_stableLift henv hU hT h.stableLift

/-- **The two sides, in one statement.**  At §3's hypotheses the class `PropSplit env 0` contains
both a `StableLift` member and a non-`StableLift` member, so §3 is a genuine selection. -/
theorem stableLift_is_a_real_restriction (henv : env.Ordered) (hU : env.PropUniq 0)
    (hT : env.PropTypeAgree 0) :
    (∃ L : PropSplit env 0, L.StableLift) ∧ (∃ L : PropSplit env 0, ¬ L.StableLift) :=
  ⟨⟨_, propSplitUp_stableLift henv hU hT⟩, ⟨_, junkSplitOf_not_stableLift henv hU hT⟩⟩

/-- **Positive control on the doctored object**, so the refutation is not the artefact of an empty
predicate: `junkSplitOf` does hold at `∀ p : Prop, p` over the empty context… -/
theorem junkSplitOf_isPropAt_falseProp (henv : env.Ordered) (hU : env.PropUniq 0)
    (hT : env.PropTypeAgree 0) (ls : List ℕ) :
    (junkSplitOf env henv hU hT).IsPropAt ls ([] : List VExpr)
      (.forallE (.sort .zero) (.bvar 0)) :=
  ⟨VEnv.IsPropUp.of_hasType (u := .zero) (Γ := []) trivial allProp_hasType rfl, by simp⟩

/-- …and it discriminates: `Prop` itself is not a proposition, at the same context. -/
theorem junkSplitOf_not_isPropAt_sort (henv : env.Ordered) (hU : env.PropUniq 0)
    (hT : env.PropTypeAgree 0) (ls : List ℕ) :
    ¬ (junkSplitOf env henv hU hT).IsPropAt ls ([] : List VExpr) (.sort .zero) :=
  fun h => not_isPropUp_sort henv hU ls h.1

end StablePrelude

end SetModel

end Lean4Lean

/-! ## 8. Axiom census

Every headline result, by **namespace** (this file declares in `Lean4Lean.SetModel` and
`Lean4Lean.SetModel.StablePrelude`; the directory name is not the namespace). -/

#print axioms Lean4Lean.SetModel.PropSplit.Stable.stableLift
#print axioms Lean4Lean.SetModel.PropSplit.Stable.stableInst
#print axioms Lean4Lean.SetModel.PropSplit.stable_iff_lift_and_inst
#print axioms Lean4Lean.SetModel.propSplitUp_stableLift
#print axioms Lean4Lean.SetModel.exists_stableLift_propSplit
#print axioms Lean4Lean.SetModel.exists_stableLift_propSplit_of_agree
#print axioms Lean4Lean.SetModel.propSplitUp_stableInst_iff
#print axioms Lean4Lean.SetModel.propSplitUp_stable_iff
#print axioms Lean4Lean.SetModel.interp_liftN_lift
#print axioms Lean4Lean.SetModel.interp_closed_ctx_lift
#print axioms Lean4Lean.SetModel.StablePrelude.onCtx_levelWF
#print axioms Lean4Lean.SetModel.StablePrelude.not_isType_sortParam_of_onCtx
#print axioms Lean4Lean.SetModel.StablePrelude.not_onCtx_of_lift'_sortParam
#print axioms Lean4Lean.SetModel.StablePrelude.not_isPropUpOn_sortParam_target
#print axioms Lean4Lean.SetModel.StablePrelude.not_stableLift_propSplitUpOn
#print axioms Lean4Lean.SetModel.StablePrelude.not_stable_propSplitUpOn
#print axioms Lean4Lean.SetModel.StablePrelude.not_stableLift_propSplitUpOnPreludeEnv
#print axioms Lean4Lean.SetModel.StablePrelude.junkSplitOf
#print axioms Lean4Lean.SetModel.StablePrelude.junkSplitOf_not_stableLift
#print axioms Lean4Lean.SetModel.StablePrelude.junkSplitOf_not_stable
#print axioms Lean4Lean.SetModel.StablePrelude.stableLift_is_a_real_restriction
#print axioms Lean4Lean.SetModel.StablePrelude.junkSplitOf_isPropAt_falseProp
#print axioms Lean4Lean.SetModel.StablePrelude.junkSplitOf_not_isPropAt_sort
