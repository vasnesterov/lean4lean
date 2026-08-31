import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.QuotReduce

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

/-- **`quotReduceRec` is sound** — CLOSED 2026-08-31.  This was the last open half of
`reduceRecursor`; the other half (`inductiveReduceRec`) is vacuous today
(`inductiveReduceRec_eq_none` above).

`quotReduceRec` is reachable — unlike everything else downstream of `AddInduct` — because
`TrEnv'.quot` fires on `AddQuot`, which never inspects `Eq`: the `QuotReady` premise is on the
`VEnv` side and an `axiomDecl` named `Eq` satisfies it.  So a `VContext` with
`quotInit = true` and `Quot.lift` in its map exists, and this branch has to be proved, not
argued away.

## How it is proved

Everything abstract lives in `Verify/QuotReduce.lean`:

* `TrEnv.quotFacts` reads the five facts the branch needs off `quotInit = true`: the four
  constants `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` are in the map with their intended
  `VConstant`s, and `quotDefEq` is in `defeqs`.
* `VEnv.quotLift_reduce` fires `IsDefEq.extra_applied` on `quotDefEq` and reconciles the two
  readings of `α`/`r` (see the hazard below) via `VEnv.quotLift_reconcile`, which is where
  const-application injectivity is spent.
* `VEnv.quotInd_reduce` does the `Quot.ind` half by `IsDefEq.proofIrrel` — `addQuot` adds
  exactly one `VDefEq`, the `Quot.lift` rule, so `Quot.ind` gets no δ-style rule; its motive
  is `Quot α r → Prop`, so both sides inhabit the same `Prop`.
* `VContext.quotLiftFull` / `quotIndFull` package the spine bookkeeping: each takes a
  `TrExprS` of the full application, returns **one** translation `v` of the major premise, and
  a continuation that consumes exactly `whnf.WF`'s postcondition at `v`.  That shape is
  deliberate: no two translations of the same subterm ever have to be reconciled, which is
  what made earlier attempts collapse.

The `WHNF`-side proof below is then only implementation-shape glue: `exists_cons6`/
`exists_cons5` turn the `mkPos < args.size` guard into a cons pattern, `isAppOfArity3_inv`
inverts the `Quot.mk` test, `Expr.mkAppRange_eq` turns the re-applied trailing arguments back
into `mkAppList`, and `FVarsIn.mkAppList` plus `whnf`'s own `FVarsBelow` discharge the
`FVarsBelow` half (the reduct's new subterm `b3` is a subterm of the whnf'd major premise).

## What it costs, honestly

`quotLift_reconcile` runs on `IsDefEqU.const_app_inv` (`Theory/Typing/Injectivity.lean`, fact
**(B)**) at the constant `Quot`, and both ι-steps take `VEnv.PiInv` from `VEnv.piInv_axiom`.
Neither is a carried hypothesis any more: (B) is proved from `VEnv.WF` alone (its residual is
the `trans` case, i.e. `VEnv.WF.rigidShapeUniqNS`), and `patWF_quot` takes `PiInv` plus
`VEnv.WF`.  So this theorem is `sorry`-free but not hole-free.

**[measured 2026-08-31]**, forward cone over type *and* value, `allowOpaque := true`:

    quotReduceRec.WF   cone  9770   holes  TrProj.uniq, weakN_iff,
                                           forallE_inv_stratified, rigidShapeUniqNS
    inferType.WF       cone  9043   holes  TrProj.uniq, weakN_iff, forallE_inv_stratified
    whnf.WF            cone   195   holes  (none)

so three of the four holes were already required by the checker's own `inferType` stack, and
the one this branch newly brings into the whnf/`reduceRecursor` cone is `rigidShapeUniqNS` —
a hole with 202 transitive users, hence already load-bearing tree-wide rather than new
pressure.  `VEnv.IsDefEq.church_rosser` and `VEnv.NormalEq.descend` are **not** in the cone
(checked by name), so the conditional-refutation caveat recorded in
`Verify/Typing/ConstSpineWF.lean` does *not* apply here: this branch takes the direct
`IsDefEqStrong` route to (B), not the Church--Rosser one.

**Two corrections to this docstring's previous text.**  (1) It said the residual was "forward
(discharge `PatWF`)" and that the theorem "cannot acquire" a `PatWF` hypothesis.  The second
half is right, the first is stale: `PatWF` never had to be discharged upward, because
`patWF_quot` is stated with `PiInv` as its only extra premise and (B) has since been proved
outright.  (2) It said (B) was `sorry` and that this branch was "blocked on const-application
injectivity".  (B) is proved; what remains under it is the injectivity *corner*
(`rigidShapeUniqNS` and friends), which is a different and shared obstruction.

## Why `hq` is a hypothesis

It is `reduceRecursor`'s own guard: the implementation calls `quotReduceRec` only under
`if env.quotInit`, and `reduceRecursor.WF` supplies `hq` from the `split`, so nothing is lost.
It is not bookkeeping.  `quotReduceRec` itself checks only that the head constant is
`Quot.lift`/`Quot.ind` and that the major premise whnf's to a three-argument `Quot.mk`; it
never consults `quotInit`.  With `quotInit = false` a `TrEnv'` chain may still hold
`Quot.lift` and `Quot.mk` as ordinary *axioms* of arbitrary type — `TrEnv'.axiom` inspects no
names — while the model contains **no `quotDefEq` at all** (`TrEnv'.defeqs_shape`).  The
branch then fires and the postcondition has no rule to appeal to.  So the theorem is, to the
best reading of the source, **false without `hq`**; that reading is *not* machine-checked,
because turning it into a witness needs `.app`-at-a-non-function ill-typedness, i.e. sort/Π
disjointness — fact (A), itself `sorry`.

## The reconciliation hazard, kept for the record

* `quotDefEq` binds *one* `α` and *one* `r` and uses each in **both** the `Quot.lift` head and
  the `Quot.mk` argument (`bvar 5`/`bvar 4` in both positions), so every instance of the rule
  forces the two to agree.  No choice of spine dodges it.
* `quotReduceRec` checks only the head name and `isAppOfArity ``Quot.mk 3`.  So does the C++
  kernel (`~/lean4/src/kernel/quot.h:39-69`) — we mirror it faithfully, and it is sound
  because `Quot` really is injective.
* Hence the last component of `IsDefEq.extra_applied`'s `hargs` — `a : α` for the `a` read off
  the whnf'd `Quot.mk` and the `α` read off the head — is a *reconciliation* obligation,
  `Quot α r ≡ Quot α' r' → α ≡ α'`.  `Theory/Typing/PatternRules.lean`'s `quotCheck` meets the
  identical hazard from the other side and resolves it by making the *matcher refuse*; the
  kernel does not refuse, so this branch had to **derive** what the pattern framework
  **assumes**.  `quotLift_reconcile` is that derivation.
* `RuleFreeHead env ``Quot``, (B)'s other side condition, is proved as
  `TrEnv.ruleFreeHead_quot` (`Verify/TypeChecker/Reduce.lean`) with no `VEnv.Sig` and no
  `VEnv.WF` induction: `VEnv.addConst` refuses a name already present, `TrEnv'` only grows
  `constants`, and `Q = true` forces the `quot` step — so a δ-rule named `Quot` and the
  quotient step cannot both occur.  Non-vacuity is checked at a concrete witness in
  `Verify/QuotConsts.lean` (`QuotWit.ruleFreeHead_quot_wit`). -/
theorem quotReduceRec.WF {c : VContext} {s : VState} (hq : c.env.quotInit = true)
    (he : c.TrExprS e e') :
    RecM.WF c s (quotReduceRec e whnf) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold quotReduceRec
  split
  · rename_i fn ls heq
    split
    · rename_i hlift
      dsimp only
      have hfn : e.getAppFn = .const ``Quot.lift ls := by rw [heq, eq_of_beq hlift]
      split
      · rename_i h
        obtain ⟨a1, a2, a3, a4, a5, q, post, hLeq⟩ := exists_cons6 (l := e.getAppArgsList)
          (by rw [Expr.getAppArgs_eq] at h; simpa using h)
        have hargs : e.getAppArgs = (a1::a2::a3::a4::a5::q::post).toArray := by
          rw [Expr.getAppArgs_eq, hLeq]
        have he2 : c.TrExprS
            ((Expr.const ``Quot.lift ls).mkAppList (a1::a2::a3::a4::a5::q::post)) e' := by
          rw [← hLeq, ← hfn, Expr.mkAppList_getAppArgsList]; exact he
        obtain ⟨v, hqv, hstep⟩ := c.quotLiftFull hq he2
        have heqe : e = (Expr.const ``Quot.lift ls).mkAppList (a1::a2::a3::a4::a5::q::post) := by
          rw [← hLeq, ← hfn, Expr.mkAppList_getAppArgsList]
        simp only [hargs]
        refine (whnf.WF hqv).bind fun mk _ _ ⟨hfb, hmkr⟩ => ?_
        split
        · exact .pure nofun
        · rename_i hari
          obtain ⟨us', b1, b2, b3, rfl⟩ := isAppOfArity3_inv (n := ``Quot.mk) (by simpa using hari)
          have happ : (Lean.mkApp3 (Expr.const ``Quot.mk us') b1 b2 b3).appArg! = b3 := rfl
          have hres := hstep (us' := us') (b1 := b1) (b2 := b2) (b3 := b3) hmkr
          have hbelow : c.FVarsBelow e ((a4.app b3).mkAppList post) := by
            intro P hP hfv
            rw [heqe, FVarsIn.mkAppList] at hfv
            rw [FVarsIn.mkAppList]
            refine ⟨⟨hfv.2 _ (by simp), ?_⟩, fun a ha => hfv.2 _ (by simp [ha])⟩
            exact (hfb P hP (hfv.2 _ (by simp))).2
          have hidx : (a1::a2::a3::a4::a5::q::post).toArray[3]! = a4 := rfl
          split
          · rename_i hpost
            have hrange : mkAppRange ((a1::a2::a3::a4::a5::q::post).toArray[3]!.app b3) (5+1)
                (a1::a2::a3::a4::a5::q::post).toArray.size
                (a1::a2::a3::a4::a5::q::post).toArray = (a4.app b3).mkAppList post := by
              rw [hidx]
              exact Expr.mkAppRange_eq (l₁ := [a1,a2,a3,a4,a5,q]) (l₂ := post) (l₃ := [])
                (by simp) (by simp) (by simp)
            rw [happ, hrange]
            refine .pure fun e₁ eqn => ?_
            obtain rfl := Option.some.inj eqn
            exact ⟨hbelow, hres⟩
          · rename_i hpost
            have hnil : post = [] := by
              rw [List.size_toArray] at hpost
              simp_all
            subst hnil
            rw [happ, hidx]
            refine .pure fun e₁ eqn => ?_
            obtain rfl := Option.some.inj eqn
            exact ⟨hbelow, by simpa using hres⟩
      · exact .pure nofun
    · split
      · rename_i hind
        dsimp only
        have hfn : e.getAppFn = .const ``Quot.ind ls := by rw [heq, eq_of_beq hind]
        split
        · rename_i h
          obtain ⟨a1, a2, a3, a4, q, post, hLeq⟩ := exists_cons5 (l := e.getAppArgsList)
            (by rw [Expr.getAppArgs_eq] at h; simpa using h)
          have hargs : e.getAppArgs = (a1::a2::a3::a4::q::post).toArray := by
            rw [Expr.getAppArgs_eq, hLeq]
          have heqe : e = (Expr.const ``Quot.ind ls).mkAppList (a1::a2::a3::a4::q::post) := by
            rw [← hLeq, ← hfn, Expr.mkAppList_getAppArgsList]
          have he2 : c.TrExprS
              ((Expr.const ``Quot.ind ls).mkAppList (a1::a2::a3::a4::q::post)) e' := heqe ▸ he
          obtain ⟨v, hqv, hstep⟩ := c.quotIndFull hq he2
          simp only [hargs]
          refine (whnf.WF hqv).bind fun mk _ _ ⟨hfb, hmkr⟩ => ?_
          split
          · exact .pure nofun
          · rename_i hari
            obtain ⟨us', b1, b2, b3, rfl⟩ :=
              isAppOfArity3_inv (n := ``Quot.mk) (by simpa using hari)
            have happ : (Lean.mkApp3 (Expr.const ``Quot.mk us') b1 b2 b3).appArg! = b3 := rfl
            have hres := hstep (us' := us') (b1 := b1) (b2 := b2) (b3 := b3) hmkr
            have hbelow : c.FVarsBelow e ((a4.app b3).mkAppList post) := by
              intro P hP hfv
              rw [heqe, FVarsIn.mkAppList] at hfv
              rw [FVarsIn.mkAppList]
              refine ⟨⟨hfv.2 _ (by simp), ?_⟩, fun a ha => hfv.2 _ (by simp [ha])⟩
              exact (hfb P hP (hfv.2 _ (by simp))).2
            have hidx : (a1::a2::a3::a4::q::post).toArray[3]! = a4 := rfl
            split
            · rename_i hpost
              have hrange : mkAppRange ((a1::a2::a3::a4::q::post).toArray[3]!.app b3) (4+1)
                  (a1::a2::a3::a4::q::post).toArray.size
                  (a1::a2::a3::a4::q::post).toArray = (a4.app b3).mkAppList post := by
                rw [hidx]
                exact Expr.mkAppRange_eq (l₁ := [a1,a2,a3,a4,q]) (l₂ := post) (l₃ := [])
                  (by simp) (by simp) (by simp)
              rw [happ, hrange]
              refine .pure fun e₁ eqn => ?_
              obtain rfl := Option.some.inj eqn
              exact ⟨hbelow, hres⟩
            · rename_i hpost
              have hnil : post = [] := by
                rw [List.size_toArray] at hpost
                simp_all
              subst hnil
              rw [happ, hidx]
              refine .pure fun e₁ eqn => ?_
              obtain rfl := Option.some.inj eqn
              exact ⟨hbelow, by simpa using hres⟩
        · exact .pure nofun
      · exact .pure nofun
  · exact .pure nofun

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
  · rename_i hq
    refine (quotReduceRec.WF hq he).bind fun r _ _ hr => ?_
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
