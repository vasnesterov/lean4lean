import Lean4Lean.Verify.TypeChecker.Basic

/-!
# R6: which `ConstantInfo` shapes a checker at `safety` can actually meet

`TrEnv'.no_inductInfo` (`Verify/Environment/Extension.lean`) is proved only at
`safety = .unsafe`, and `Verify/Environment.lean` dodges the gap by instantiating its
`VEnvs` bundle there.  `VContext` carries a single `trenv : TrEnv safety env venv` at the
`safety` the checker was invoked at and cannot dodge, so the vacuity arguments for
`reduceProjCore.WF`, `inferProj.WF` and `reduceRecursor.WF`'s `inductiveReduceRec` branch
need a version that is uniform in `safety`.

**`no_inductInfo` does not generalise** — see `no_inductInfo_false_at_safe` below, which is a
machine-checked refutation, not a remark.  An *unsafe* inductive has
`ConstantInfo.safety = .unsafe`, `¬ .safe ≤ .unsafe`, so `TrEnv'.ignore` admits it into the
constant map while the `VEnv` stays empty.  The map at `safety = .safe` really can contain an
`.inductInfo`.

What *is* uniform is the same statement **guarded by `safety ≤ ci.safety`** — the guard
`TrEnv.find?_iff` already carries, and the one that makes `ignore` contradictory in every
case rather than only at `.unsafe`.  It is not an added hypothesis: a caller holding a
`TrExprS` for the term names the constant in the `VEnv`, and `find?_iff` turns that into the
guard.  `TrEnv.find?_shape` and `VContext.not_inductInfo` below are that route, end to end.

(The mechanism the scope predicted — "the absence of an `.inductInfo` shape in
`TrConstant`" — is not the one that works: `TrConstant` never cases on the `ConstantInfo`
constructor, so it accepts `.inductInfo` happily.  The shapes are constrained by `TrEnv'`'s
*constructors*, so the proof is an induction over `TrEnv'` after all, with `ignore`
discharged by the guard.)

This belongs next to `no_inductInfo` in `Verify/Environment/Extension.lean`; it lives here
because that file is another stream's.  `Reduce.lean` is imported by `WHNF.lean`,
`InferType.lean` and `IsDefEq.lean`, so every consumer sees it from here.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-- An unsafe inductive: legal, and invisible to the safe fragment. -/
private def unsafeInductVal : InductiveVal :=
  { name := `R6.Witness, levelParams := [], type := .sort (.succ .zero),
    numParams := 0, numIndices := 0, all := [`R6.Witness], ctors := [],
    numNested := 0, isRec := false, isUnsafe := true, isReflexive := false }

/-- **`TrEnv'.no_inductInfo` is false off `safety = .unsafe`.**  Recorded live so it cannot
rot: this is why `find?_shape` below is guarded rather than unconditional. -/
theorem no_inductInfo_false_at_safe {C : ConstMap} (hwf : C.WF) (he : ∀ n, C.find? n = none) :
    TrEnv' .safe (C.insert `R6.Witness (.inductInfo unsafeInductVal)) false .empty ∧
    (C.insert `R6.Witness (.inductInfo unsafeInductVal)).find? `R6.Witness
      = some (.inductInfo unsafeInductVal) := by
  refine ⟨.ignore (ci := .inductInfo unsafeInductVal) (he _) (by decide) (.empty hwf he), ?_⟩
  rw [hwf.find?_insert]; simp

/-- **R6.**  A constant the checker running at `safety` may actually *use* is one of the five
shapes `TrEnv'` inserts.  Uniform in `safety`: the guard makes `ignore` contradictory. -/
theorem TrEnv'.find?_shape (H : TrEnv' safety C Q venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    (∃ v, ci = .axiomInfo v) ∨ (∃ v, ci = .defnInfo v) ∨ (∃ v, ci = .thmInfo v) ∨
    (∃ v, ci = .opaqueInfo v) ∨ (∃ v, ci = .quotInfo v) := by
  induction H with
  | empty _ hfind => rw [hfind] at h; cases h
  | ignore hn hhidden H ih =>
    rw [H.map_wf.find?_insert] at h; split at h
    · cases h; exact absurd hs hhidden
    · exact ih h
  | «axiom» _ _ _ _ H ih =>
    rw [H.map_wf.find?_insert] at h
    split at h <;> [(cases h; exact .inl ⟨_, rfl⟩); exact ih h]
  | defn _ _ _ _ H ih =>
    rw [H.map_wf.find?_insert] at h
    split at h <;> [(cases h; exact .inr (.inl ⟨_, rfl⟩)); exact ih h]
  | thm _ _ _ _ _ H ih =>
    rw [H.map_wf.find?_insert] at h
    split at h <;> [(cases h; exact .inr (.inr (.inl ⟨_, rfl⟩))); exact ih h]
  | «opaque» _ _ _ _ H ih =>
    rw [H.map_wf.find?_insert] at h
    split at h <;> [(cases h; exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))); exact ih h]
  | unsafeDef _ _ hnd hfr _ _ _ H ih =>
    obtain h | ⟨_, _, _, h2⟩ := insertDefs_find? H.map_wf hfr hnd h
    · exact ih h
    · exact .inr (.inl ⟨_, h2.symm⟩)
  | quot hready hadd H ih =>
    obtain ⟨lp₁, ty₁, env₁, _, hn₁, _,
      lp₂, ty₂, env₂, _, hn₂, _,
      lp₃, ty₃, env₃, _, hn₃, _,
      lp₄, ty₄, env₄, _, hn₄, _, rfl, _⟩ := hadd
    have wf₀ := H.map_wf
    have wf₁ := wf₀.insert ``Quot
      (.quotInfo { name := ``Quot, kind := .type, levelParams := lp₁, type := ty₁ }) hn₁
    have wf₂ := wf₁.insert ``Quot.mk
      (.quotInfo { name := ``Quot.mk, kind := .ctor, levelParams := lp₂, type := ty₂ }) hn₂
    have wf₃ := wf₂.insert ``Quot.lift
      (.quotInfo { name := ``Quot.lift, kind := .lift, levelParams := lp₃, type := ty₃ }) hn₃
    rw [wf₃.find?_insert] at h
    split at h <;> [(cases h; exact .inr (.inr (.inr (.inr ⟨_, rfl⟩)))); skip]
    rw [wf₂.find?_insert] at h
    split at h <;> [(cases h; exact .inr (.inr (.inr (.inr ⟨_, rfl⟩)))); skip]
    rw [wf₁.find?_insert] at h
    split at h <;> [(cases h; exact .inr (.inr (.inr (.inr ⟨_, rfl⟩)))); skip]
    rw [wf₀.find?_insert] at h
    split at h <;> [(cases h; exact .inr (.inr (.inr (.inr ⟨_, rfl⟩)))); exact ih h]
  | induct _ hadd => cases hadd

/-- The same, on a `Kernel.Environment`, with the guard obtained from the `VEnv` side —
which is where a caller holding a `TrExprS` gets it. -/
theorem TrEnv.find?_shape (H : TrEnv safety env venv) {name ci}
    (hv : ∃ ci', venv.constants name = some ci') (h : env.find? name = some ci) :
    (∃ v, ci = .axiomInfo v) ∨ (∃ v, ci = .defnInfo v) ∨ (∃ v, ci = .thmInfo v) ∨
    (∃ v, ci = .opaqueInfo v) ∨ (∃ v, ci = .quotInfo v) := by
  obtain ⟨ci₀, h₀, hs⟩ := H.find?_iff.2 hv
  cases h₀.symm.trans h
  refine TrEnv'.find?_shape (name := name) H ?_ hs
  rw [← H.map_wf.find?'_eq_find?]; exact h

theorem TrEnv.not_inductInfo (H : TrEnv safety env venv) {name v}
    (hv : ∃ ci', venv.constants name = some ci')
    (h : env.find? name = some (.inductInfo v)) : False := by
  rcases H.find?_shape hv h with ⟨_,h⟩|⟨_,h⟩|⟨_,h⟩|⟨_,h⟩|⟨_,h⟩ <;> cases h

theorem TrEnv.not_ctorInfo (H : TrEnv safety env venv) {name v}
    (hv : ∃ ci', venv.constants name = some ci')
    (h : env.find? name = some (.ctorInfo v)) : False := by
  rcases H.find?_shape hv h with ⟨_,h⟩|⟨_,h⟩|⟨_,h⟩|⟨_,h⟩|⟨_,h⟩ <;> cases h

theorem TrEnv.not_recInfo (H : TrEnv safety env venv) {name v}
    (hv : ∃ ci', venv.constants name = some ci')
    (h : env.find? name = some (.recInfo v)) : False := by
  rcases H.find?_shape hv h with ⟨_,h⟩|⟨_,h⟩|⟨_,h⟩|⟨_,h⟩|⟨_,h⟩ <;> cases h

/-! ### The dual: which *rules* a `TrEnv'`-built environment can have

R6 says which `ConstantInfo` shapes reach the constant map.  This says which `VDefEq`s reach
the `VEnv`: only δ-rules and the quotient rule.  **Currently unconsumed** — it was proved for
a route to `reduceProjCore.WF` that turned out not to be needed (the shorter route goes
through `not_ctorInfo` above).  Kept because it is inventory, not a premise: it characterises
`TrEnv'`, and anything asking "which rules can this environment have" — a `VEnv.Params`
instance, `RuleShape`'s `TrEnv'`-side counterpart, an ι-rule-absence argument once
`AddInduct` lands — wants exactly this. -/

theorem VEnv.addConst_defeqs {env env' : VEnv} (h : env.addConst n ci = some env') :
    env'.defeqs = env.defeqs := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

theorem VEnv.addConsts_defeqs : ∀ {cis : List VDefVal} {env env' : VEnv},
    env.addConsts cis = some env' → env'.defeqs = env.defeqs
  | [], _, _, h => by rw [VEnv.addConsts, List.foldlM_nil] at h; cases h; rfl
  | ci :: cis, env, env', h => by
    rw [VEnv.addConsts, List.foldlM_cons] at h
    cases h1 : env.addConst ci.name ci.toVConstant with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some env₁ =>
      rw [h1] at h
      have h2 : env₁.addConsts cis = some env' := h
      rw [VEnv.addConsts_defeqs (cis := cis) h2, VEnv.addConst_defeqs h1]

theorem VEnv.addDefEqs_defeqs : ∀ {cis : List VDefVal} {env : VEnv} {df},
    (env.addDefEqs cis).defeqs df → (∃ ci ∈ cis, df = ci.toDefEq) ∨ env.defeqs df
  | [], _, _, h => .inr h
  | ci :: cis, env, df, h => by
    rw [VEnv.addDefEqs, List.foldl_cons] at h
    rcases VEnv.addDefEqs_defeqs (cis := cis) (env := env.addDefEq ci.toDefEq) h with
      ⟨ci', hci', rfl⟩ | h
    · exact .inl ⟨_, .tail _ hci', rfl⟩
    · rcases h with rfl | h
      · exact .inl ⟨_, .head _, rfl⟩
      · exact .inr h

/-- **The dual of R6.**  A `TrEnv'`-built `VEnv` carries only δ-rules and the quotient rule —
in particular no ι-rule, since `TrEnv'.induct` is vacuous.  Uniform in `safety`; unlike R6 no
guard is needed, because `ignore` changes no rules. -/
theorem TrEnv'.defeqs_shape (H : TrEnv' safety C Q venv) (h : venv.defeqs df) :
    (∃ ci' : VDefVal, df = ci'.toDefEq) ∨ df = quotDefEq := by
  induction H with
  | empty => cases h
  | ignore _ _ _ ih => exact ih h
  | «axiom» _ _ _ hadd _ ih => exact ih (VEnv.addConst_defeqs hadd ▸ h)
  | defn _ _ _ hadd _ ih =>
    rcases h with rfl | h
    · exact .inl ⟨_, rfl⟩
    · exact ih (VEnv.addConst_defeqs hadd ▸ h)
  | thm _ _ _ _ hadd _ ih => exact ih (VEnv.addConst_defeqs hadd ▸ h)
  | «opaque» _ _ _ hadd _ ih => exact ih (VEnv.addConst_defeqs hadd ▸ h)
  | unsafeDef _ _ _ _ _ hadd _ _ ih =>
    rcases VEnv.addDefEqs_defeqs h with ⟨ci', _, rfl⟩ | h
    · exact .inl ⟨_, rfl⟩
    · exact ih (VEnv.addConsts_defeqs hadd ▸ h)
  | quot _ hadd _ ih =>
    obtain ⟨lp₁, ty₁, env₁, _, hn₁, ha₁,
      lp₂, ty₂, env₂, _, hn₂, ha₂,
      lp₃, ty₃, env₃, _, hn₃, ha₃,
      lp₄, ty₄, env₄, _, hn₄, ha₄, _, rfl⟩ := hadd
    rcases h with rfl | h
    · exact .inr rfl
    · exact ih (VEnv.addConst_defeqs ha₁ ▸ VEnv.addConst_defeqs ha₂ ▸
        VEnv.addConst_defeqs ha₃ ▸ VEnv.addConst_defeqs ha₄ ▸ h)
  | induct _ hadd => cases hadd

/-! ### R10: the induct-case lemmas the `TrEnv'` inductions will need

`AddInductStages` (`Verify/Environment/Basic.lean`) is `AddInduct`'s intended definition,
complete and witnessed but not yet substituted for the empty `AddInduct`, because the flip is
not confined to files this stream owns.  The three lemmas below are the induct arms that the
`TrEnv'` inductions downstream of the flip will need, proved here — the same relocation
`no_inductInfo_false_at_safe` above already makes.  On the flip:

* `Aligned.addInductStages` replaces `Aligned.addInduct`'s `nomatch H`
  (`Verify/Environment/Lemmas.lean:67`), whose *statement* is also wrong today: its `env₁` and
  `env₂` are auto-bound implicits unrelated to `venv₁`/`venv₂`, so the theorem says nothing.
* `ConstantInfo.deltaValue?_ind`/`_ctor`/`_rec` discharge `TrEnv'.of_value`'s induct case
  (`Verify/Environment/Lemmas.lean:279`).
* `AddInductStages.find?_shape` and `.defeqs` (in `Basic.lean`) discharge `find?_shape`'s and
  `defeqs_shape`'s induct cases here.

**The two restatements the flip forces, in full.**  `TrEnv'.find?_shape` gains three disjuncts
and becomes

    (∃ v, ci = .axiomInfo v) ∨ (∃ v, ci = .defnInfo v) ∨ (∃ v, ci = .thmInfo v) ∨
    (∃ v, ci = .opaqueInfo v) ∨ (∃ v, ci = .quotInfo v) ∨
    (∃ v, ci = .inductInfo v) ∨ (∃ v, ci = .ctorInfo v) ∨ (∃ v, ci = .recInfo v)

and `TrEnv'.defeqs_shape` gains one:

    (∃ ci' : VDefVal, df = ci'.toDefEq) ∨ df = quotDefEq ∨ ∃ D, df ∈ D.iotaRules

Neither restatement rescues `TrEnv.not_inductInfo`, `.not_ctorInfo` or `.not_recInfo`: the
new disjuncts are exactly the shapes those three refute, and no hypothesis available to their
callers excludes them.  `ctorInfo_recInfo_reachable` below is how far the refutation gets
without the flip.  So "repair the consumers" is not available for those three — they, and
everything proved through them, need the real arguments (ι-reduction, K-like reduction,
structure eta) rather than a bigger `rcases` pattern.
-/

theorem Aligned.addDefEqList : ∀ (dfs : List VDefEq) {C : ConstMap} {venv},
    Aligned safety C venv → Aligned safety C (dfs.foldl VEnv.addDefEq venv)
  | [], _, _, h => h
  | _ :: dfs, _, _, h => Aligned.addDefEqList dfs h.defeq

theorem Aligned.addIndRules {C : ConstMap} {venv : VEnv} {D : VInductDecl'}
    (h : Aligned safety C venv) : Aligned safety C (venv.addIndRules D) :=
  Aligned.addDefEqList _ h

theorem Aligned.addIndConsts {S cs m env m₂ env₂} (H : AddIndConsts S cs m env m₂ env₂) :
    Aligned safety m env → Aligned safety m₂ env₂ := by
  induction H with
  | nil => exact id
  | cons hname _ htr hfr hadd _ ih =>
    exact fun h => ih (h.const hfr (htr.sf_mono DefinitionSafety.le_safe) hadd hname)

/-- **The repair for `Aligned.addInduct`.**  Belongs in `Verify/Environment/Lemmas.lean`;
it lives here because that file is another stream's. -/
theorem Aligned.addInductStages {m₁ m₂ : ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    (H : AddInductStages m₁ env₁ D m₂ env₂) (h : Aligned safety m₁ env₁) :
    Aligned safety m₂ env₂ := by
  obtain ⟨mt, et, mc, ec, e₃, h1, h2, h3, rfl⟩ := H
  exact Aligned.addIndRules
    (Aligned.addIndConsts h3 (Aligned.addIndConsts h2 (Aligned.addIndConsts h1 h)))

theorem ConstantInfo.deltaValue?_ind {v} : (ConstantInfo.inductInfo v).deltaValue? = none := rfl
theorem ConstantInfo.deltaValue?_ctor {v} : (ConstantInfo.ctorInfo v).deltaValue? = none := rfl
theorem ConstantInfo.deltaValue?_rec {v} : (ConstantInfo.recInfo v).deltaValue? = none := rfl

/-- **`TrEnv.not_ctorInfo` and `TrEnv.not_recInfo` die on the flip, and this is how far the
refutation gets without it.**

`not_ctorInfo` needs: a constant map holding a `.ctorInfo` under a name the `VEnv` also holds,
at a `safety` the guard admits.  Every one of those three facts is established below from
`R10.Wit.addInductStages_wit` alone.  The single missing step is `TrEnv'.induct` accepting
`AddInductStages`, i.e. the definitional change itself — after which
`TrEnv'.empty ▸ TrEnv'.induct` turns this into a refutation in the shape of
`no_inductInfo_false_at_safe`.

So "`not_ctorInfo`/`not_recInfo`/`not_inductInfo` become false" is not a prediction here; it is
this lemma plus one definition.  The same holds for `reduceProjCore_none` and
`inductiveReduceRec_eq_none` (`Verify/TypeChecker/WHNF.lean`), which are proved *through* them,
and hence for `whnf.WF`. -/
theorem ctorInfo_recInfo_reachable {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env', AddInductStages m VEnv.empty R10.Wit.decl m' env' ∧
      -- the three hypotheses of `TrEnv.not_ctorInfo`, bar the `TrEnv'` derivation
      m'.find? `R10.Wit.U.unit = some (.ctorInfo R10.Wit.uCtor) ∧
      (∃ ci, env'.constants `R10.Wit.U.unit = some ci) ∧
      DefinitionSafety.safe ≤ (ConstantInfo.ctorInfo R10.Wit.uCtor).safety ∧
      -- …and of `TrEnv.not_recInfo`
      m'.find? `R10.Wit.U.rec = some (.recInfo R10.Wit.uRec) ∧
      (∃ ci, env'.constants `R10.Wit.U.rec = some ci) ∧
      DefinitionSafety.safe ≤ (ConstantInfo.recInfo R10.Wit.uRec).safety := by
  obtain ⟨m', env', H, -, hc, hr, hce, hre⟩ := R10.Wit.addInductStages_wit hwf hfr
  exact ⟨m', env', H, hc, hce, by decide, hr, hre, by decide⟩

/-- **`TrEnv'.ignore` is unavailable at `safety = .unsafe`.**  Its premise is
`¬ safety ≤ ci.safety`, and `.unsafe` is the bottom of `DefinitionSafety`, so
`.unsafe ≤ ci.safety` holds for every `ci` whatever its tag.

Recorded because two places state the opposite as the justification for gating the induct rule
to safe blocks: `Theory/Inductive/Decl.lean`'s R10 handover and `Verify/Environment/Induct.lean`'s
`TrIndDecl.safe` both say an unsafe block "is taken by `TrEnv'.ignore` instead".  That holds at
`.safe` and `.partial`; at `.unsafe` nothing is hidden, so every declared constant needs a `VEnv`
counterpart and `ignore` cannot supply one.  The gate therefore leaves `TrEnv' .unsafe` with no
rule for an unsafe inductive.  It does not *create* that gap — today `TrEnv' .unsafe` has no rule
for a safe inductive either (`TrEnv'.no_inductInfo`) — but the flip does not close it, and an
unsafe block cannot be modelled soundly anyway: `checkConstructors` skips `checkPositivity`, so
`VIndField.WF.pos` has no witness to give. -/
theorem ignore_unavailable_at_unsafe (ci : ConstantInfo) :
    DefinitionSafety.unsafe ≤ ci.safety := by cases ci.safety <;> decide

/-- **The form a `.WF` proof meets.**  The name comes from a translated `.const`, so the
`safety` guard is free: `inferProj`'s `let .inductInfo I_val ← env.get I_name | fail` fails,
uniformly in `safety`, with no `.unsafe` instantiation and no appeal to `AddInduct`. -/
theorem TypeChecker.VContext.not_inductInfo (c : TypeChecker.VContext) {name us us' v}
    (hc : c.TrExprS (.const name us) (.const name us'))
    (h : c.env.find? name = some (.inductInfo v)) : False :=
  let .const h1 _ _ := hc; c.trenv.not_inductInfo ⟨_, h1⟩ h

end Lean4Lean

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem reduceNative.WF :
    (reduceNative env e).WF fun oe => ∀ e₁, oe = some e₁ → False := by
  unfold reduceNative; split <;> [skip; exact .pure nofun]
  split <;> [exact .throw; skip]; split <;> [exact .throw; exact .pure nofun]

theorem rawNatLitExt?.WF {c : VContext} (H : rawNatLitExt? e = some n) (he : c.TrExprS e e') :
    c.venv.contains ``Nat ∧ e' = .natLit n := by
  have : c.TrExprS (.lit (.natVal n)) e' := by
    unfold rawNatLitExt? at H; split at H <;> rename_i h
    · cases H; have := he.eqv h; exact .lit (this.nat_of_natZero c.Ewf c.hasPrimitives) this
    · unfold Expr.rawNatLit? at H; split at H <;> cases H; exact he
  have hn := this.lit_has_type
  exact ⟨hn, this.unique (by trivial) (TrExprS.natLit c.hasPrimitives hn n).1⟩

def reduceBinNatOpG (guard : Nat → Nat → Prop) [DecidableRel guard]
    (f : Nat → Nat → Nat) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  if guard v1 v2 then return none
  return some <| .lit <| .natVal <| f v1 v2

theorem reduceBinNatOpG.WF {guard} [DecidableRel guard] {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatNat fc f) :
    RecM.WF c s (reduceBinNatOpG guard f a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatOpG
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]
  obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]
  cases (rawNatLitExt?.WF h b2).2
  split <;> [exact .pure nofun; rename_i h]
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  refine ⟨_, (TrExprS.natLit c.hasPrimitives hn _).1, ?_⟩
  have := heval ⟨_, h1⟩ v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact ⟨_, .appDF this b3⟩

theorem reduceBinNatPred.WF {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatBool fc f) :
    RecM.WF c s (reduceBinNatPred f a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatPred
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]; cases (rawNatLitExt?.WF h a2).2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]; cases (rawNatLitExt?.WF h b2).2
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => .boolLit, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  have := heval ⟨_, h1⟩ v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine ⟨_, (TrExprS.boolLit c.hasPrimitives ?_ _).1, ?_⟩
  · let ⟨_, H⟩ := this
    exact VExpr.WF.boolLit_has_type c.Ewf c.hasPrimitives (Γ := []) trivial ⟨_, H.hasType.2⟩
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact  ⟨_, .appDF this b3⟩

theorem reduceNat.WF {c : VContext} (he : c.TrExprS e e') :
    RecM.WF c s (reduceNat e) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  generalize hP : (fun oe => _) = P
  refine let prims := _; have hprims : Environment.primitives = .ofList prims := rfl; ?_
  replace hprims {a} : Environment.primitives.contains a ↔ a ∈ prims := by
    simp [hprims, NameSet.contains, NameSet.ofList]
  unfold reduceNat; extract_lets nargs F1 fn
  cases h1 : nargs == 1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases nargs == 2 <;> [exact hP ▸ .pure nofun; simp only [↓reduceIte]]
    split <;> [rename_i f ls a b; exact hP ▸ .pure nofun]
    have hfun guard {g fc G} [DecidableRel guard] (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatNat fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatOpG guard g a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatOpG.WF he (hprims.2 hprim) heval
    have hpred {g fc G} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatBool fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatPred g a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatPred.WF he (hprims.2 hprim) heval
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natAdd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natSub
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natMul
    apply hfun _ (by simp [prims]) c.hasPrimitives.natPow
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natGcd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natMod
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natDiv
    apply hpred (by simp [prims]) c.hasPrimitives.natBEq
    apply hpred (by simp [prims]) c.hasPrimitives.natBLE
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natLAnd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natLOr
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natXor
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natShiftLeft
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natShiftRight
    exact hP ▸ .pure nofun
  · split <;> [rename_i h2; exact hP ▸ .pure nofun]
    simp [nargs, Expr.getAppNumArgs_eq] at h1; subst fn
    let .app f a := e; simp [Expr.appFn!, Expr.eqv_const] at h2 ⊢; subst h2
    let .app ha1 ha2 hf ha := he
    let .const h1 h2 h3 := hf
    refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
    split <;> [rename_i n h; exact hP ▸ .pure nofun]
    obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
    refine hP ▸ .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
    have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
    have ⟨c2, c3⟩ := c.safePrimitives c1 <| hprims.2 (by simp [prims])
    have ⟨d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1; cases h2
    refine have ⟨p1, p2⟩ := TrExprS.natLit c.hasPrimitives hn _; ⟨_, p1, ?_⟩
    refine p2.toU.symm.trans c.Ewf c.Δwf ?_
    exact ⟨_, ha1.appDF <| a3.of_r c.Ewf c.Δwf ha2⟩

/-- The head of a translated application spine is itself translated. -/
theorem head_tr {c : VContext} {e₁ st₁} (h : c.TrExprS e₁ st₁) :
    ∃ f', c.TrExprS e₁.getAppFn f' :=
  let ⟨_, hstk⟩ := AppStack.build <| e₁.mkAppList_getAppArgsList ▸ h
  ⟨_, hstk.tr⟩

/-- **`reduceProjCore` never fires, today.**  Not because its guard rejects — it has none
worth the name: it reads `numParams` off whatever constructor it finds and indexes blindly
(`TypeChecker.lean:351-359`).  What stops it is that the constant map, at the `safety` the
checker runs at, holds no `.ctorInfo` that a *translated* term can name — `TrEnv.not_ctorInfo`,
the R6 corollary above.

This is the same rescue as `reduceBinNatOpG.WF`'s and `inferProj`'s: **the hypothesis, not
the check.**  The struct was already translated, so its head constant is in the `VEnv`, and
`find?_iff` turns that into the `safety ≤ ci.safety` guard R6 needs.

Superseded when `AddInduct` gains constructors: at that point `.ctorInfo` becomes reachable
and the real argument — `TrProj`'s `IsStructure` pins the block, so a constructor of another
type cannot appear under a well-translated projection — takes over.  That argument needs
`mkC = C.name`, hence `HasInduct` uniqueness (ledger G4), and is not available today. -/
theorem reduceProjCore_none {c : VContext} {s : VState} {i e₀ st₀} (h : c.TrExprS e₀ st₀) :
    RecM.WF c s (reduceProjCore i e₀) fun oe _ => oe = none := by
  have hget : ∀ {name}, (c.env.get name).WF fun ci => c.env.find? name = some ci := by
    intro name; simp [Environment.get]; split <;> [refine .pure ‹_›; exact .throw]
  have key : ∀ {e₁ st₁ s'}, c.TrExprS e₁ st₁ →
      RecM.WF c s' (e₁.withApp fun mk args => do
        let .const mkC _ := mk | return none
        let env ← getEnv
        let .ctorInfo mkInfo ← env.get mkC | return none
        return args[mkInfo.numParams + i]?) fun oe _ => oe = none := by
    intro e₁ st₁ s' h1
    rw [Expr.withApp_eq]
    obtain ⟨f', hf⟩ := head_tr h1
    split <;> [skip; exact .pure rfl]
    rename_i mkC us heq
    rw [heq] at hf
    let .const hc _ _ := hf
    refine .getEnv <| (M.WF.liftExcept hget).lift.bind fun ci _ _ hci => ?_
    cases ci <;> first
      | exact absurd hci fun hh => c.trenv.not_ctorInfo ⟨_, hc⟩ hh
      | exact .pure rfl
  unfold reduceProjCore
  dsimp only
  split
  · rename_i str
    have hlit : c.TrExprS (Expr.strLitToConstructor str) st₀ := by
      let .lit _ h' := h; exact h'
    exact (whnf.WF hlit).bind fun _ _ _ hh => key hh.2.choose_spec.1
  · exact key h

theorem reduceProjCore.WF (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProjCore i e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := by
  have .proj hst _ := he
  exact (reduceProjCore_none hst).mono fun _ _ _ hq _ eq => absurd (hq ▸ eq) nofun

theorem reduceProj.WF (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProj i e cheapProj) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := by
  unfold reduceProj
  have .proj (e' := s) a1 a2 := he
  refine .bind (Q := fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ s) ?_ fun _ _ _ ⟨h1, h2⟩ => ?_
  · split <;> [exact whnfCore.WF a1; exact whnf.WF a1]
  have ⟨_, b1, b2⟩ := h2.proj c.Ewf c.Δwf a2
  refine (reduceProjCore.WF b1).mono fun _ _ _ H _ eq => ?_
  have ⟨c1, c2⟩ := H _ eq; exact ⟨h1.trans c1, c2.defeq c.Ewf c.Δwf b2⟩
