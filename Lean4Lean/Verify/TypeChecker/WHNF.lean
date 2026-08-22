import Lean4Lean.Verify.TypeChecker.Reduce

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

/-- **`inductiveReduceRec` never fires, today** — and it returns `none` *before* any monadic
step, so this is an equation on the value rather than a `RecM.WF`.

Its second line is `let some (.recInfo info) := env.find? recFn | return none`, and the
constant map at the checker's `safety` holds no `.recInfo` that a *translated* term can name
(`TrEnv.not_recInfo`).  The head `recFn` comes from `e`, which the hypothesis says is
translated, so the `safety ≤ ci.safety` guard R6 wants is free.

Superseded when `AddInduct` gains constructors; at that point this branch needs the ι rule,
K-like reduction (lemma M3 of `docs/design-inductive.md`) and structure eta
(`docs/research-structeta.md`), none of which exist. -/
theorem inductiveReduceRec_eq_none {c : VContext} {e₀ st₀} (h : c.TrExprS e₀ st₀)
    {m : Type → Type} [Monad m] (whnf inferType isDefEq) :
    _root_.Lean4Lean.inductiveReduceRec c.env e₀ whnf inferType isDefEq
      = (pure none : m (Option Expr)) := by
  unfold _root_.Lean4Lean.inductiveReduceRec
  obtain ⟨f', hf⟩ := head_tr h
  split <;> [skip; rfl]
  rename_i recFn ls heq
  rw [heq] at hf
  let .const hc _ _ := hf
  split <;> [skip; rfl]
  rename_i info heq2
  exact absurd heq2 fun hh => c.trenv.not_recInfo ⟨_, hc⟩ hh

/-- **The one blocked half of `reduceRecursor`.**  `quotReduceRec` *is* reachable — unlike
everything else downstream of `AddInduct` — because `TrEnv'.quot` fires on `AddQuot`, which
never inspects `Eq`: the `QuotReady` premise is on the `VEnv` side and an `axiomDecl` named
`Eq` satisfies it.  So a `VContext` with `quotInit = true` and `Quot.lift` in its map exists.

It is blocked on **const-application injectivity** (ledger I13), not on anything about
inductives:

* `quotDefEq` binds *one* `α` and *one* `r` and uses each in **both** the `Quot.lift` head and
  the `Quot.mk` argument (`bvar 5`/`bvar 4` in both positions), so every instance of the rule
  forces the two to agree.  No choice of spine dodges it.
* `quotReduceRec` checks only the head name and `isAppOfArity ``Quot.mk 3`.  So does the C++
  kernel (`~/lean4/src/kernel/quot.h:39-69`) — we mirror it faithfully, and it is sound
  because `Quot` really is injective.
* Hence the last component of `IsDefEq.extra_applied`'s `hargs` — `a : α` for the `a` read off
  the whnf'd `Quot.mk` and the `α` read off the head — is a *reconciliation* obligation, i.e.
  `Quot α r ≡ Quot α' r' → α ≡ α'`.

`Theory/Typing/PatternRules.lean`'s `quotCheck` meets the identical hazard from the other
side and resolves it by making the *matcher refuse* (two `defeq` clauses, discharged by
reflexivity where `extra_pat` sees the rule's own variables).  The kernel does not refuse, so
this must **derive** what the pattern framework **assumes**.

A second, independent gap: `VEnv.addQuot` adds exactly one `VDefEq`, the `Quot.lift` rule,
while `quotReduceRec` reduces `Quot.ind` too.  That half is still derivable — `Quot.ind`'s
motive is `Quot α r → Prop`, so both sides inhabit the same `Prop` and `IsDefEq.proofIrrel`
applies — but it is a different argument from `extra`, and needs the same spine inversion.

The peel itself is *not* a cost: `VEnv.IsDefEq.extra_applied`
(`Theory/Inductive/StructureClosed.lean`) states it once for any `VDefEq` whose `lhs`/`rhs`/
`type` share a `mkLams`/`mkPi` telescope. -/
theorem quotReduceRec.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (quotReduceRec e whnf) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := sorry

theorem reduceRecursor.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold reduceRecursor
  refine .getEnv ?_
  have hjp : ∀ {s' : VState} (_ : Unit), RecM.WF c s'
      (bind (_root_.Lean4Lean.inductiveReduceRec c.env e whnf (fun e => inferType e) isDefEq)
        fun x => inferType'.match_1 (fun _ => RecM (Option Expr)) x (fun r => pure (some r))
          fun _ => pure none)
      (fun oe _ => ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') := by
    intro s' _
    rw [inductiveReduceRec_eq_none he]
    exact .pureBind (.pure nofun)
  dsimp only
  split
  · refine (quotReduceRec.WF he).bind fun r _ _ hr => ?_
    cases r with
    | none => exact hjp ⟨⟩
    | some r => exact .pure fun _ eq => hr _ (by cases eq; rfl)
  · exact hjp ⟨⟩

theorem whnfFVar.WF {c : VContext} {s : VState} (he : c.TrExprS (.fvar fv) e') :
    RecM.WF c s (whnfFVar (.fvar fv) cheapProj) fun e₁ _ =>
      c.FVarsBelow (.fvar fv) e₁ ∧ c.TrExpr e₁ e' := by
  refine .getLCtx ?_
  simp [Expr.fvarId!]; split <;> [skip; exact .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩]
  rename_i decl h
  rw [c.trlctx.1.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; subst this
  let ⟨e', ty', h1, h2, _, h3, _⟩ :=
    c.trlctx.find?_of_mem c.Ewf (List.mem_of_find?_eq_some h)
  refine (whnfCore.WF h3).mono fun _ _ _ ⟨h4, h5⟩ => ?_
  refine ⟨h2.trans h4, h5.defeq c.Ewf c.Δwf ?_⟩
  refine (TrExprS.fvar h1).uniq c.Ewf ?_ he
  exact .refl c.Ewf c.Δwf

theorem whnfCore'.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore' e cheapProj) fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold whnfCore'; extract_lets F
  let full := (· matches Expr.fvar _ | .app .. | .letE .. | .proj ..)
  generalize hP : (fun e₁ (_ : VState) => _) = P
  have hid {s} : RecM.WF c s (pure e) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  suffices hF : full e → RecM.WF c s (F ⟨⟩) P by
    split
    any_goals exact hid
    any_goals exact hF rfl
    · let .mdata he := he
      exact hP ▸ whnfCore'.WF he
    · refine .getLCtx ?_; split <;> [exact hid; exact hF rfl]
  simp [F]; refine fun hfull => .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    have ⟨_, h1, h2, h3⟩ := (wf.whnfCore_wf eq).2.2.2.2 he.fvarsIn
    refine ⟨h1, h3.defeq c.Ewf c.Δwf ?_⟩
    exact h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  have hsave {e₁ s} (h1 : c.FVarsBelow e e₁) (h2 : c.TrExpr e₁ e') :
      (save e cheapProj e₁).WF c s P := by
    simp [save]
    split <;> [skip; exact hP ▸ .pure ⟨h1, h2⟩]
    rintro _ mwf wf a s' ⟨⟩
    refine let s' := _; ⟨s', rfl, ?_⟩
    have hic {ic} (hic : WHNFCache.WF c s ic) : WHNFCache.WF c s (ic.insert e e₁) := by
      intro _ _ h
      rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
      rename_i eq
      refine .mk c.mlctx.noBV (.eqv h1 eq BEq.rfl) (he.eqv eq) h2 (.eqv eq ?_) ?_ --_ (.eqv h2 eq BEq.rfl) (.eqv eq ?_) ?_
      · exact he.fvarsIn.mono wf.ngen_wf
      · exact h2.fvarsIn.mono wf.ngen_wf
    exact hP ▸ ⟨.rfl, { wf with whnfCore_wf := hic wf.whnfCore_wf }, h1, h2⟩
  split <;> cases hfull
  · exact hP ▸ whnfFVar.WF he
  · rename_i fn arg _; generalize eq : fn.app arg = e at *
    have ⟨_, stk⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
    refine (whnfCore.WF stk.tr).bind fun _ s _ ⟨h1, h2⟩ => ?_
    split <;> [rename_i name dom body bi _; split]
    · let rec loop.WF {e e' i rargs f} (H : LambdaBodyN i e' f) (hi : i ≤ rargs.size) :
        ∃ n f', LambdaBodyN n e' f' ∧ n ≤ rargs.size ∧
          loop e cheapProj rargs i f = loop.cont e cheapProj rargs n f' := by
        unfold loop; split
        · split
          · refine loop.WF (by simpa [Nat.add_comm] using H.add (.succ .zero)) ‹_›
          · exact ⟨_, _, H, hi, rfl⟩
        · exact ⟨_, _, H, hi, rfl⟩
      refine
        let ⟨i, f, h3, h4, eq⟩ := loop.WF (e' := .lam name dom body bi) (.succ .zero) <| by
          simp [← eq, Expr.getAppRevArgs_eq, Expr.getAppArgsRevList]
        eq ▸ ?_; clear eq
      simp [Expr.getAppRevArgs_eq] at h4 ⊢
      obtain ⟨l₁, l₂, h5, rfl⟩ : ∃ l₁ l₂, e.getAppArgsRevList = l₁ ++ l₂ ∧ l₂.length = i :=
        ⟨_, _, (List.take_append_drop (e.getAppArgsRevList.length - i) ..).symm, by simp; omega⟩
      simp [loop.cont, h5, List.take_of_length_le]
      rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₂ := l₁) (l₃ := l₂) (by simp) (by rfl) (by rfl)]
      have br := BetaReduce.inst_reduce (l₁ := l₂.reverse)
        [] (by simpa using h3) (Expr.instantiateList_append ..) (h := by
          have := h5 ▸ (c.mlctx.noBV ▸ he.closed).getAppArgsRevList
          simp [or_imp, forall_and] at this ⊢
          exact this.2) |>.mkAppRevList (es := l₁)
      simp [← Expr.mkAppRevList_reverse, ← Expr.mkAppRevList_append, ← h5] at br
      have hl₂ : ∀ x ∈ l₂, x.looseBVarRange' = 0 := fun x hx =>
        ((c.mlctx.noBV ▸ he.closed).getAppArgsRevList
          (h5 ▸ List.mem_append_right _ hx)).looseBVarRange_zero
      rw [Expr.instantiate_eq _ _ (by simpa using hl₂)]
      have := h2.rebuild_mkAppRevList c.Ewf c.Δwf stk.tr <|
        e.mkAppRevList_getAppArgsRevList ▸ he
      have ⟨_, a1, a2⟩ := this.beta c.Ewf c.Δwf br
      refine (whnfCore.WF a1).bind fun _ _ _ ⟨b1, b2⟩ => ?_
      have hb := e.mkAppRevList_getAppArgsRevList ▸ h1.mkAppRevList
      exact hsave (hb.trans (.betaReduce br) |>.trans b1) <|
        b2.defeq c.Ewf c.Δwf a2
    · refine (reduceRecursor.WF he).bind fun _ _ _ h => ?_
      split <;> [skip; exact hid]
      let ⟨h1, _, h2, eq⟩ := h _ rfl
      refine hP ▸ (whnfCore.WF h2).mono fun _ _ _ ⟨h3, h4⟩ => ?_
      exact ⟨h1.trans h3, h4.defeq c.Ewf c.Δwf eq⟩
    · rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₃ := [])
        (by simp [Expr.getAppRevArgs_toList]; rfl) (by rfl) (by simp [Expr.getAppRevArgs_eq])]
      have {e e₁ : Expr} (hb : c.FVarsBelow e e₁) {es e₀' e'}
          (hes : c.TrExprS (e.mkAppRevList es) e₀') (he : c.TrExprS e e') (he₁ : c.TrExpr e₁ e') :
          c.FVarsBelow (e.mkAppRevList es) (e₁.mkAppRevList es) ∧
          c.TrExpr (e₁.mkAppRevList es) e₀' := by
        induction es generalizing e₁ e₀' e' with
        | nil =>
          refine ⟨hb, he₁.defeq c.Ewf c.Δwf ?_⟩
          exact he.uniq c.Ewf (.refl c.Ewf c.Δwf) hes
        | cons _ _ ih =>
          have .app h1 h2 h3 h4 := hes
          have ⟨h5, h6⟩ := ih hb h3 he he₁
          exact ⟨fun _ hP he => ⟨h5 _ hP he.1, he.2⟩,
            .app c.Ewf c.Δwf h1 h2 h6 (h4.trExpr c.Ewf c.Δwf)⟩
      have eq := e.mkAppRevList_getAppArgsRevList
      let ⟨h3, _, h4, eq⟩ := eq ▸ this h1 (eq ▸ he) stk.tr h2
      refine (whnfCore.WF h4).bind fun _ _ _ ⟨h5, h6⟩ => ?_
      refine hsave (h3.trans h5) (h6.defeq c.Ewf c.Δwf eq)
  · let .letE h1 h2 h3 h4 := he
    refine (whnfCore.WF (h4.inst_let c.Ewf.ordered h3)).bind fun _ _ _ ⟨h1, h2⟩ => ?_
    exact hsave (.trans (fun _ _ he => he.2.2.instantiate1 he.2.1) h1) h2
  · refine (reduceProj.WF he).bind fun _ _ _ H => ?_
    split
    · let ⟨h1, _, h2, eq⟩ := H _ rfl
      refine (whnfCore.WF h2).bind fun _ _ _ ⟨h3, h4⟩ => ?_
      exact hsave (h1.trans h3) (h4.defeq c.Ewf c.Δwf eq)
    · exact hsave .rfl (he.trExpr c.Ewf c.Δwf)

theorem whnf'.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnf' e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold whnf'; extract_lets F
  generalize hP : (fun e₁ (_ : VState) => _) = P
  have hid {s} : RecM.WF c s (pure e) P := hP ▸ .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf⟩
  suffices hF : RecM.WF c s (F ()) P by
    split
    any_goals exact hid
    any_goals exact hF
    · let .mdata he := he
      exact hP ▸ whnf'.WF he
    · refine .getLCtx ?_; split <;> [exact hid; exact hF]
  simp [F]; refine .get ?_; split
  · rename_i r eq; refine .stateWF fun wf => hP ▸ .pure ?_
    have ⟨_, h1, h2, h3⟩ := (wf.whnf_wf eq).2.2.2.2 he.fvarsIn
    refine ⟨h1, h3.defeq c.Ewf c.Δwf ?_⟩
    exact h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  have {e e' s n} (he : c.TrExprS e e') : (loop e n).WF c s fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
    induction n generalizing s e e' with | zero => exact .throw | succ n ih => ?_
    refine .getEnv <| (whnfCore'.WF he).bind fun e₁ s _ ⟨h1, _, he₁, eq⟩ => ?_
    refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h3 => ?_
    split <;> [cases h3 _ rfl; skip]
    refine (reduceNat.WF he₁).bind fun _ _ _ h3 => ?_; split
    · exact .pure ⟨.trans h1 (h3 _ rfl).1, (h3 _ rfl).2.defeq c.Ewf c.Δwf eq⟩
    refine (unfoldDefinition.WF he₁).bind fun _ _ _ H => ?_
    split <;> [skip; exact .pure ⟨h1, _, he₁, eq⟩]
    have ⟨a1, _, a2, eq'⟩ := H
    refine (ih a2).mono fun _ _ _ ⟨b1, b2⟩ => ?_
    exact ⟨h1.trans <| a1.trans b1, b2.defeq c.Ewf c.Δwf <| eq'.trans c.Ewf c.Δwf eq⟩
  refine .readThe <| (this he).bind fun e₁ s _ ⟨h1, h2⟩ => ?_
  rintro _ mwf wf a s' ⟨⟩
  refine let s' := _; ⟨s', rfl, ?_⟩
  have hic {ic} (hic : WHNFCache.WF c s ic) : WHNFCache.WF c s (ic.insert e e₁) := by
    intro _ _ h
    rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
    rename_i eq
    refine .mk c.mlctx.noBV (.eqv h1 eq BEq.rfl) (he.eqv eq) h2 (.eqv eq ?_) ?_
    · exact he.fvarsIn.mono wf.ngen_wf
    · exact h2.fvarsIn.mono wf.ngen_wf
  exact hP ▸ ⟨.rfl, { wf with whnf_wf := hic wf.whnf_wf }, h1, h2⟩
