import Lean4Lean.Verify.Inductive.BinderScan

/-!
# The two residuals of `BinderScan.lean`, closed

`Verify/Inductive/BinderScan.lean` §9(d)/(e) leaves exactly two obligations behind
`recArgOf_binders_noBlock_noLen`:

* **(d)** a de Bruijn σ-composition at **non-adjacent** indices,
  `(b[u]_{d+1})[w[u]_d]_0 = (b[w]_0)[u]_d` — the tree has only the adjacent form
  (`instantiate1'_instantiate1'`, `Verify/Expr.lean`:1116).  It is what `ScanCert.unsubst_fvar`'s
  `.letE` case needs, and with it the `scanShapeNoLet` side condition disappears.
* **(e)** `hβ : S.piArity = 0 → r.binders = []`, the `Expr`-side β step at `.app (.lam ..) a`.

§1-§2 are the substitution calculus, §3 rebuilds the un-substitution, §4-§5 rerun `BinderScan`
§5-§6 with no side condition, §6-§7 do β.
-/

set_option autoImplicit false

namespace Lean.Expr

/-! ## §0 The three `bvar` clauses of `instantiate1'` and the two of `liftLooseBVars'`

Named so that §1/§2's index arithmetic is a `rw` chain against stated equations rather than nested
`split`s. -/

theorem instantiate1'_bvar_lt {i d : Nat} (a : Expr) (h : i < d) :
    instantiate1' (.bvar i) a d = .bvar i := by
  simp only [instantiate1']; rw [if_pos h]

theorem instantiate1'_bvar_self {d : Nat} (a : Expr) :
    instantiate1' (.bvar d) a d = a.liftLooseBVars' 0 d := by
  simp [instantiate1']

theorem instantiate1'_bvar_gt {i d : Nat} (a : Expr) (h : d < i) :
    instantiate1' (.bvar i) a d = .bvar (i - 1) := by
  simp only [instantiate1']; rw [if_neg (by omega), if_neg (by omega)]

theorem liftLooseBVars_bvar_lt {i s : Nat} (k : Nat) (h : i < s) :
    liftLooseBVars' (.bvar i) s k = .bvar i := by
  simp only [liftLooseBVars']; rw [if_pos h]

theorem liftLooseBVars_bvar_ge {i s : Nat} (k : Nat) (h : s ≤ i) :
    liftLooseBVars' (.bvar i) s k = .bvar (i + k) := by
  simp only [liftLooseBVars']; rw [if_neg (by omega)]

/-! ## §1 Lifting commutes with instantiation

`(w[u]_j)↑(s,k) = (w↑(s,k))[u]_{j+k}` whenever `s ≤ j`.  Not in the tree; the `.bvar i = j` case is
where `liftLooseBVars_liftLooseBVars` is spent.  The result index is a *variable* `m` constrained by
`j + k = m` rather than the literal `j + k`, so descending a binder is `j+1, m+1` and needs no
`Nat.add_right_comm` rewriting — which is what keeps the eleven structural cases one-liners. -/

theorem liftLooseBVars_instantiate1' (u : Expr) (k : Nat) :
    ∀ (w : Expr) (s j m : Nat), s ≤ j → j + k = m →
      (w.instantiate1' u j).liftLooseBVars' s k = (w.liftLooseBVars' s k).instantiate1' u m := by
  intro w
  induction w with intro s j m hsj hm
  | bvar i =>
    subst hm
    rcases Nat.lt_trichotomy i j with h | rfl | h
    · rw [instantiate1'_bvar_lt _ h]
      rcases Nat.lt_or_ge i s with h2 | h2
      · rw [liftLooseBVars_bvar_lt _ h2, instantiate1'_bvar_lt _ (by omega)]
      · rw [liftLooseBVars_bvar_ge _ h2, instantiate1'_bvar_lt _ (by omega)]
    · rw [instantiate1'_bvar_self, liftLooseBVars_bvar_ge _ hsj, instantiate1'_bvar_self]
      exact liftLooseBVars_liftLooseBVars (Nat.zero_le _) (by omega)
    · have e1 : (Expr.bvar i).instantiate1' u j = .bvar (i - 1) := instantiate1'_bvar_gt _ h
      rw [e1, liftLooseBVars_bvar_ge _ (show s ≤ i - 1 by omega),
        liftLooseBVars_bvar_ge _ (show s ≤ i by omega),
        instantiate1'_bvar_gt _ (show j + k < i + k by omega)]
      congr 1; omega
  | fvar _ => rfl
  | mvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app _ _ ihf iha =>
    simp only [instantiate1', liftLooseBVars', ihf _ _ _ hsj hm, iha _ _ _ hsj hm]
  | lam _ _ _ _ iht ihb =>
    simp only [instantiate1', liftLooseBVars', iht _ _ _ hsj hm,
      ihb (s + 1) (j + 1) (m + 1) (Nat.succ_le_succ hsj) (by omega)]
  | forallE _ _ _ _ iht ihb =>
    simp only [instantiate1', liftLooseBVars', iht _ _ _ hsj hm,
      ihb (s + 1) (j + 1) (m + 1) (Nat.succ_le_succ hsj) (by omega)]
  | letE _ _ _ _ _ iht ihv ihb =>
    simp only [instantiate1', liftLooseBVars', iht _ _ _ hsj hm, ihv _ _ _ hsj hm,
      ihb (s + 1) (j + 1) (m + 1) (Nat.succ_le_succ hsj) (by omega)]
  | mdata _ _ ih => simp only [instantiate1', liftLooseBVars', ih _ _ _ hsj hm]
  | proj _ _ _ ih => simp only [instantiate1', liftLooseBVars', ih _ _ _ hsj hm]

/-! ## §2 σ-composition at non-adjacent indices

`BinderScan` §9(d)'s obligation.  The outer index `k` and the gap `j` are separate, so descending a
binder increments `k` and the total `d` and leaves `j` alone; the consumer wants `k = 0`, which is
exactly what the tree's adjacent `instantiate1'_instantiate1'` (indices `j+1`/`j`) does not cover.

`u` must be **closed** — it is `.fvar v` at every call site, and closedness is what discharges the
`i = d+1` case with no lift on the right. -/

theorem instantiate1'_instantiate1'_closed {u : Expr} (hu : u.looseBVarRange' = 0) (w : Expr)
    (j : Nat) :
    ∀ (e : Expr) (k d : Nat), k + j = d →
      (e.instantiate1' u (d + 1)).instantiate1' (w.instantiate1' u j) k
        = (e.instantiate1' w k).instantiate1' u d := by
  have hlift : ∀ n, u.liftLooseBVars' 0 n = u := fun _ => liftLooseBVars_eq_self (by omega)
  have hinst : ∀ (a : Expr) n, u.instantiate1' a n = u := fun _ _ => instantiate1'_eq_self (by omega)
  intro e
  induction e with intro k d hd
  | bvar i =>
    rcases Nat.lt_trichotomy i k with h | rfl | h
    · -- `i < k`: both orders leave the index alone
      rw [instantiate1'_bvar_lt u (show i < d + 1 by omega),
        instantiate1'_bvar_lt (w.instantiate1' u j) h, instantiate1'_bvar_lt w h,
        instantiate1'_bvar_lt u (show i < d by omega)]
    · -- `i = k`: the two orders differ by §1
      rw [instantiate1'_bvar_lt u (show i < d + 1 by omega)]
      simp only [instantiate1'_bvar_self]
      exact liftLooseBVars_instantiate1' u i w 0 j d (Nat.zero_le _) (by omega)
    · rcases Nat.lt_trichotomy i (d + 1) with h2 | rfl | h2
      · -- `k < i ≤ d`: one decrement on each side
        rw [instantiate1'_bvar_lt u h2, instantiate1'_bvar_gt (w.instantiate1' u j) h,
          instantiate1'_bvar_gt w h, instantiate1'_bvar_lt u (show i - 1 < d by omega)]
      · -- `i = d+1`: the variable being replaced by `u`; closedness is spent here
        rw [instantiate1'_bvar_self u, hlift, hinst,
          instantiate1'_bvar_gt w (show k < d + 1 by omega)]
        show _ = instantiate1' (.bvar d) u d
        rw [instantiate1'_bvar_self u, hlift]
      · -- `i > d+1`: two decrements on each side
        rw [instantiate1'_bvar_gt u h2, instantiate1'_bvar_gt w (show k < i by omega),
          instantiate1'_bvar_gt (w.instantiate1' u j) (show k < i - 1 by omega),
          instantiate1'_bvar_gt u (show d < i - 1 by omega)]
  | fvar _ => rfl
  | mvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app _ _ ihf iha => simp only [instantiate1', ihf _ _ hd, iha _ _ hd]
  | lam _ _ _ _ iht ihb =>
    simp only [instantiate1', iht _ _ hd, ihb (k + 1) (d + 1) (by omega)]
  | forallE _ _ _ _ iht ihb =>
    simp only [instantiate1', iht _ _ hd, ihb (k + 1) (d + 1) (by omega)]
  | letE _ _ _ _ _ iht ihv ihb =>
    simp only [instantiate1', iht _ _ hd, ihv _ _ hd, ihb (k + 1) (d + 1) (by omega)]
  | mdata _ _ ih => simp only [instantiate1', ih _ _ hd]
  | proj _ _ _ ih => simp only [instantiate1', ih _ _ hd]

/-- `BinderScan` §9(d)'s obligation verbatim, at the `fvar` the loop substitutes. -/
theorem instantiate1'_instantiate1'_fvar (v : FVarId) (w b : Expr) (d : Nat) :
    (b.instantiate1' (.fvar v) (d + 1)).instantiate1' (w.instantiate1' (.fvar v) d)
      = (b.instantiate1' w).instantiate1' (.fvar v) d :=
  instantiate1'_instantiate1'_closed (u := .fvar v) rfl w d b 0 d (Nat.zero_add _)

end Lean.Expr

namespace Lean4Lean
open Lean

/-! ## §3 `ScanCert.unsubst_fvar` with **no side condition**

`BinderScan` §4 carries `scanShapeNoLet e = true` because a structural recursion on `e` cannot do the
`.letE` case: the sub-certificate is about `body.instantiate1' val`, which is not a subterm of
`.letE _ _ val body _` and admits no size measure (`let x := big; x x` ζ-reduces to `big big`).  The
repair is to induct on the **certificate** instead — its `.letE` node's sub-derivation is already at
the reduct — and then §2 is exactly the equation that lines the two reducts up.

Two auxiliaries keep the thirteen derivation cases to four: `scanHead` marks the only heads
`ScanCert` is not free at, and it is invariant under the substitution. -/

/-- The three heads at which `ScanCert` says something.  At every other head it is a constructor. -/
def scanHead : Expr → Bool
  | .mdata .. | .forallE .. | .letE .. => true
  | _ => false

theorem scanHead_instantiate1'_fvar (v : FVarId) :
    ∀ (e : Expr) (d : Nat), scanHead (e.instantiate1' (.fvar v) d) = scanHead e
  | .letE .., _ | .mvar _, _ | .sort _, _ | .const .., _ | .fvar _, _
  | .lit _, _ | .app .., _ | .lam .., _ | .proj .., _ | .mdata .., _ | .forallE .., _ => rfl
  | .bvar i, d => by
      show scanHead (if i < d then _ else if i = d then _ else _) = _
      split; · rfl
      split <;> rfl

variable {p : Lean.Expr → Bool}

/-- Off the three descent heads the certificate is free. -/
theorem ScanCert.of_scanHead_false : ∀ {e : Expr}, scanHead e = false → ScanCert p e
  | .bvar _, _ => .bvar
  | .fvar _, _ => .fvar
  | .mvar _, _ => .mvar
  | .sort _, _ => .sort
  | .const .., _ => .const
  | .app .., _ => .app
  | .lam .., _ => .lam
  | .lit _, _ => .lit
  | .proj .., _ => .proj
  | .mdata .., h => absurd h nofun
  | .forallE .., h => absurd h nofun
  | .letE .., h => absurd h nofun

/-- Which of the three descent heads `e` has, if any — the case split that keeps §3's induction to
four real cases instead of `13 × 13`. -/
theorem scanHead_cases (e : Expr) :
    (∃ m b, e = .mdata m b) ∨ (∃ n a b bi, e = .forallE n a b bi) ∨
      (∃ n a w b nd, e = .letE n a w b nd) ∨ scanHead e = false :=
  match e with
  | .mdata m b => .inl ⟨m, b, rfl⟩
  | .forallE n a b bi => .inr (.inl ⟨n, a, b, bi, rfl⟩)
  | .letE n a w b nd => .inr (.inr (.inl ⟨n, a, w, b, nd, rfl⟩))
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .app ..
  | .lam .. | .lit _ | .proj .. => .inr (.inr (.inr rfl))

open Lean in
/-- **Reading the certificate back through the loop's substitution, unconditionally.**
`BinderScan.ScanCert.unsubst_fvar` with `scanShapeNoLet` **deleted**: the `.letE` case is closed by
§2's σ-composition at the non-adjacent indices `d+1` / `0`. -/
theorem ScanCert.unsubst_fvar_all
    (hne : ∀ e : Lean.Expr, (∀ c us, e ≠ .const c us) → p e = false) (v : FVarId) :
    ∀ {t : Expr}, ScanCert p t → ∀ {e : Expr} {d : Nat},
      e.instantiate1' (.fvar v) d = t → ScanCert p e := by
  intro t hc
  induction hc with
  | miss h =>
    intro e d he
    exact .miss ((anySub_instantiate1'_fvar hne v e d).symm.trans (he ▸ h))
  | @forallE _ dom body _ hdom _ ih =>
    intro e d he
    rcases scanHead_cases e with ⟨_, _, rfl⟩ | ⟨_, a, b, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | h
    · exact absurd he nofun
    · injection he with h1 h2 h3 h4
      subst h1; subst h2; subst h3; subst h4
      exact .forallE ((anySub_instantiate1'_fvar hne v a d).symm.trans hdom) (ih rfl)
    · exact absurd he nofun
    · exact .of_scanHead_false h
  | @mdata _ _ _ ih =>
    intro e d he
    rcases scanHead_cases e with ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | h
    · injection he with h1 h2
      subst h1; subst h2
      exact .mdata (ih rfl)
    · exact absurd he nofun
    · exact absurd he nofun
    · exact .of_scanHead_false h
  | @letE _ _ _ _ _ _ ih =>
    intro e d he
    rcases scanHead_cases e with ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, w, b, _, rfl⟩ | h
    · exact absurd he nofun
    · exact absurd he nofun
    · injection he with h1 h2 h3 h4 h5
      subst h1; subst h2; subst h3; subst h4; subst h5
      exact .letE (ih (Expr.instantiate1'_instantiate1'_fvar v w b d).symm)
    · exact .of_scanHead_false h
  | bvar | fvar | sort | const | app | lam | lit | proj | mvar =>
    exact fun {e d} he =>
      .of_scanHead_false (by rw [← scanHead_instantiate1'_fvar v e d, he]; rfl)

end Lean4Lean

namespace Lean4Lean
open Lean

/-! ## §4 `hβ` was **not derivable** either, and its shape is reachable

`BinderScan` §6 replaced `PosIndex` §4.2's `hlen` by `hβ : S.piArity = 0 → r.binders = []`, and §9(e)
called `hβ` "a second, independent residual" without settling whether it is a *hypothesis* or a
*theorem*.  It is a hypothesis, and a false one: §4.1 exhibits a configuration satisfying every other
hypothesis of `recArgOf_binders_noBlock_noLen` at which `hβ` fails while the conclusion holds, and
§4.2 measures that the `Expr` shape it excludes reaches `Lean4Lean.addDecl`.

The witness is `BinderScan` §7's, with the `vlet`'s value replaced by a **head β-redex** whose
contraction is a pi: `V = (fun (_ : Sort 0) => (Sort 0) → I) (Sort 0)`.  Stage 1 of the reader fails
on `V` (its spine head is a `.lam`, not `.const I []`); `VExpr.betaHead V` is the pi, so stage 2
fires with one binder — while `V.piArity = 0`.  `.bvar` is again the `Expr` side, for `BinderScan`
§7's reason: `whnf'`'s first arm returns it with no cache and no `LocalContext`. -/

namespace AddInductive
open Lean hiding Environment Exception
open Kernel

/-- The `vlet` value: a head β-redex whose contraction is `(Sort 0) → I`. -/
def betaWitVal (I : Name) : VExpr :=
  .app (.lam (.sort .zero) (.forallE (.sort .zero) (.const I []))) (.sort .zero)

theorem betaWitVal_piArity (I : Name) : (betaWitVal I).piArity = 0 := rfl

/-- The head β step really does expose a binder the stored type does not have. -/
theorem betaWitVal_betaHead (I : Name) :
    VExpr.betaHead (betaWitVal I) = .forallE (.sort .zero) (.const I []) := rfl

end AddInductive

open Lean AddInductive in
/-- **`hβ` was not derivable — the witness.**  Every hypothesis of
`BinderScan.recArgOf_binders_noBlock_noLen` other than `hβ` holds here, including `scanShapeNoLet`
and `checkPositivity`'s success as a real monadic value, and `hβ`'s conclusion `r.binders = []` is
**false** while the theorem's conclusion `∀ B ∈ r.binders, NoConsts Sn B` is **true**.

So `hβ` cannot be discharged as a lemma from the other hypotheses, exactly as `hlen` could not
(`BinderScan` §7); the β branch has to be *proved*, and §5 states what that costs. -/
theorem hβ_not_derivable {env : VEnv} {Sn : List Name} {I : Name} (hI : I ∉ Sn)
    {stats : InductiveStats} {ctor : Name} {idx : Nat} {cx : Context} {k f i : Nat}
    {D : VInductDecl'} (hD : D.idRestore = prRestore I) (hnm : D.nm = 1)
    (hr : cx.fuel.recDepth = k+1) (hf : cx.fuel.inductiveFuel = f+1) :
    ∃ (Δ : VLCtx) (t : Lean.Expr) (S : VExpr) (r : VIndRecArg),
      TrExprS env [] Δ t S ∧
      (∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts Sn x) ∧
      checkPositivity stats t ctor idx cx = .ok () ∧
      scanShapeNoLet t = true ∧
      D.recArgOf i S = some r ∧
      S.piArity = 0 ∧ r.binders = [.sort .zero] ∧ r.binders ≠ [] ∧
      (∀ B ∈ r.binders, VExpr.NoConsts Sn B) := by
  refine ⟨[(none, .vlet (.sort .zero) (betaWitVal I))], .bvar 0, betaWitVal I,
    { binders := [.sort .zero], idx := 0, args := [] }, .bvar rfl, ?_,
    checkPositivity_bvar_ok hr hf, rfl, ?_, rfl, rfl, nofun, ?_⟩
  · refine VLCtx.noConsts_cons ⟨⟨trivial, trivial, hI⟩, trivial⟩ ?_
    intro _ _ _ h; exact absurd h nofun
  · rw [VInductDecl'.recArgOf, hD, hnm, betaWitVal_betaHead]
    rw [VIndRestore.recog, VIndRestore.recog]
    simp only [List.range_one, List.findSome?_cons, List.findSome?_nil]
    rw [VIndRestore.recogAt, VIndRestore.recogAt]
    simp [prRestore, betaWitVal, VExpr.piArity, VExpr.splitPis, VExpr.spineFn]
  · intro B hB
    rcases List.mem_cons.1 hB with rfl | h
    · trivial
    · exact absurd h nofun

end Lean4Lean

namespace Lean4Lean
open Lean

/-! ## §5 The β branch, as far as the `VExpr` side alone can take it

§4 says `hβ` must be proved, not assumed.  The part that needs **no** `Expr`-side β step and no
typing hypothesis is this: block-freeness survives the head β contraction.  `noConsts_inst` already exists
(`Theory/Inductive/NestedBuild.lean`:74), so `betaHead` is four short lemmas away.

The payoff is §5.2: `hβ` weakens to a disjunction whose second arm is `checkPositivity.loop`'s own
**early-return test**, `hasIndOcc stats.indConsts t = false`.  That is a strict weakening (the old
`hβ` implies it), and it is discharged outright rather than assumed. -/

namespace VExpr

/-- Block-freeness of an application spine.  A copy of
`Lean4Lean.MRedex.TQWit.noConsts_mkApp` (`Theory/Inductive/IndexedNested.lean`:457), which is general
but lives in a witness namespace that `Verify/Inductive/BinderScan.lean`'s import closure does not
reach.  Four lines, so restated rather than importing `Theory/Inductive/IndexedNested.lean`. -/
theorem noConsts_mkApp' {S : List Name} {f : VExpr} (hf : NoConsts S f) :
    ∀ (args : List VExpr), (∀ a ∈ args, NoConsts S a) → NoConsts S (f.mkApp args)
  | [], _ => hf
  | a :: as, ha =>
    noConsts_mkApp' (f := .app f a) ⟨hf, ha a List.mem_cons_self⟩ as
      fun b hb => ha b (List.mem_cons_of_mem _ hb)

/-- Block-freeness passes to the spine head and to every spine argument. -/
theorem noConsts_spine {S : List Name} : ∀ {e : VExpr}, NoConsts S e →
    NoConsts S e.spineFn ∧ ∀ a ∈ e.spineArgs, NoConsts S a
  | .app f a, h =>
    ⟨(noConsts_spine h.1).1, by
      intro c hb
      rw [VExpr.spineArgs, List.mem_append] at hb
      refine hb.elim (fun hb => (noConsts_spine (e := f) h.1).2 c hb) fun hb => ?_
      rcases List.mem_singleton.1 hb with rfl
      exact h.2⟩
  | .bvar _, h | .sort _, h | .const _ _, h | .lam _ _, h | .forallE _ _, h => ⟨h, nofun⟩

/-- Block-freeness survives an arbitrary head β spine contraction. -/
theorem noConsts_betaSpine {S : List Name} :
    ∀ (as : List VExpr), (∀ a ∈ as, NoConsts S a) →
      ∀ {f : VExpr}, NoConsts S f → NoConsts S (betaSpine as f)
  | [], _, _, hf => hf
  | a :: as, ha, .lam _ _b, hf =>
    noConsts_betaSpine as (fun c hc => ha c (List.mem_cons_of_mem _ hc))
      (noConsts_inst (ha a List.mem_cons_self) 0 hf.2)
  | _ :: _, ha, .bvar _, hf | _ :: _, ha, .sort _, hf
  | _ :: _, ha, .const _ _, hf | _ :: _, ha, .app _ _, hf
  | _ :: _, ha, .forallE _ _, hf => noConsts_mkApp' hf _ ha

/-- **`VExpr.betaHead` preserves block-freeness.**  The `VExpr` half of the β obligation, with no
typing hypothesis and no `Expr`-side step. -/
theorem noConsts_betaHead {S : List Name} {e : VExpr} (h : NoConsts S e) :
    NoConsts S (betaHead e) :=
  noConsts_betaSpine _ (noConsts_spine h).2 (noConsts_spine h).1

end VExpr

/-! ### §5.1 The reader's binders, with the β stage **visible**

`PosIndex` §4.1's `recArgOf_binders_piBinderDoms` collapses stage 2 into "`S.piArity = 0`", which
loses the information that the binders are then `(betaHead S).piBinderDoms`.  Keeping it is what makes
§5.2 possible. -/

theorem recArgOf_binders_piBinderDoms_beta {D : VInductDecl'} {i : Nat} {S : VExpr}
    {r : VIndRecArg} (h : D.recArgOf i S = some r) :
    r.binders = S.piBinderDoms ∨ r.binders = (VExpr.betaHead S).piBinderDoms := by
  rw [VInductDecl'.recArgOf] at h
  cases h1 : D.idRestore.recog D.nm i S with
  | some r' =>
    rw [h1] at h; cases h
    exact .inl (by rw [VIndRestore.recog_binders h1, VExpr.splitPis_piArity_fst])
  | none =>
    rw [h1, Option.orElse] at h
    exact .inr (by rw [VIndRestore.recog_binders h, VExpr.splitPis_piArity_fst])

/-- **A block-free stored type has block-free reader binders, in both stages.**  No arity hypothesis,
no certificate, no `hβ`. -/
theorem recArgOf_binders_noBlock_of_noConsts {D : VInductDecl'} {i : Nat} {S : VExpr}
    {r : VIndRecArg} (hr : D.recArgOf i S = some r)
    (hS : VExpr.NoConsts D.blockNames S) : ∀ B ∈ r.binders, D.NoBlock B := by
  rcases recArgOf_binders_piBinderDoms_beta hr with hb | hb
  · rw [hb]; exact VExpr.noConsts_piBinderDoms hS
  · rw [hb]; exact VExpr.noConsts_piBinderDoms (VExpr.noConsts_betaHead hS)

/-! ### §5.2 `BinderScan` §6 with `hβ` weakened to the checker's own early-return test -/

open Lean AddInductive in
/-- **Part (B) of `VIndField.WF.pos`, with `hβ` weakened.**  `BinderScan` §6's
`hβ : S.piArity = 0 → r.binders = []` becomes
`S.piArity = 0 → (r.binders = [] ∨ hasIndOcc stats.indConsts t = false)`, whose second arm is
`checkPositivity.loop`'s early return — a *syntactic, checkable* condition on the field type rather
than a claim about the reader.  The old hypothesis implies the new one by `.inl`, so this is strictly
stronger than `BinderScan` §6, which is strictly stronger than `PosIndex` §4.2 (§6.1 there). -/
theorem recArgOf_binders_noBlock_noLen_beta {env : VEnv} {Us : List Name}
    {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {cx : Context} {u : Unit} {D : VInductDecl'} {i : Nat} {r : VIndRecArg}
    {Δ : VLCtx} {t : Expr} {S : VExpr}
    (henv : VEnv.Ordered env)
    (hS : ∀ c ∈ D.blockNames, ∃ I ∈ stats.indConsts, I.constName! = c)
    (hlit : ∀ l : Lean.Literal,
      anySub (fun e => match e with
        | .const e _ => stats.indConsts.any fun I => I.constName! == e
        | _ => false) l.toConstructor = false)
    (hproj : ∀ Γ s i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConsts D.blockNames x → VExpr.NoConsts D.blockNames y)
    (H : TrExprS env Us Δ t S)
    (hctx : ∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts D.blockNames x)
    (hchk : checkPositivity stats t ctor idx cx = .ok u)
    (hs : scanShapeNoLet t = true)
    (hr : D.recArgOf i S = some r)
    (hβ : S.piArity = 0 → (r.binders = [] ∨ hasIndOcc stats.indConsts t = false)) :
    ∀ B ∈ r.binders, D.NoBlock B := by
  rcases recArgOf_binders_piBinderDoms hr with hb | h0
  · intro B hB
    exact H.piBinderDoms_noConsts henv (hasIndOcc_hpS hS) hlit hproj
      (checkPositivity_scanCert hs hchk) hctx B (hb ▸ hB)
  · rcases hβ h0 with h | hocc
    · rw [h]; exact nofun
    · refine recArgOf_binders_noBlock_of_noConsts hr
        (H.noConsts (hasIndOcc_hpS hS) hlit hproj hctx ?_)
      rwa [hasIndOcc_eq] at hocc

open Lean AddInductive in
/-- The old head-β hypothesis implies the new one. -/
theorem hβ_beta_of_hβ {stats : InductiveStats} {t : Expr} {S : VExpr} {r : VIndRecArg}
    (h : S.piArity = 0 → r.binders = []) :
    S.piArity = 0 → (r.binders = [] ∨ hasIndOcc stats.indConsts t = false) :=
  fun h0 => .inl (h h0)

end Lean4Lean

namespace Lean4Lean

/-! ## §6 The β residual is real, not vacuous — an executable tripwire

§4 shows `hβ` is false at a `VLCtx`/`checkPositivity` configuration.  This section measures the other
half: that the **`Expr` shape** it excludes occurs in a declaration `Lean4Lean.addDecl` **accepts**,
so `recArgOf_binders_noBlock_noLen_beta`'s remaining hypothesis is not free.

The previous round recorded that it "did **not** measure whether a head-β-redex field type is
reachable through `addDecl`".  It is.  Both arms below are load-bearing, for `BinderScan` §8's
reasons: if the *positive* redex were rejected, the residual would be a fiction; if the
*non-positive* one were accepted, `checkPositivity` would not be β-reducing before it scans and
`recArgOf_binders_noBlock_noLen`'s β branch would be **false** rather than unproved. -/

namespace ScanResidualWit
open Lean

/-- `(fun (x : Type) => (_ : x) → W α) α` — a head β-redex whose contraction is a *positive* pi. -/
def fldGoodB : Expr :=
  .app (.lam `x (.sort (.succ .zero))
    (.forallE `a (.bvar 0) (.app (.const `WGoodB []) (.bvar 2)) .default) .default) (.bvar 0)

/-- Its non-positive twin, `(fun (x : Type) => (_ : W x) → W α) α`. -/
def fldBadB : Expr :=
  .app (.lam `x (.sort (.succ .zero))
    (.forallE `a (.app (.const `WBadB []) (.bvar 1)) (.app (.const `WBadB []) (.bvar 2)) .default)
    .default) (.bvar 0)

/-- **The β witness satisfies `scanShapeNoLet`.**  So the two residuals are independent: closing the
`.letE` one cannot touch this one, and `BinderScan` §8's tripwire and this one guard different
debts. -/
theorem fldB_scanShape : scanShapeNoLet fldGoodB = true ∧ scanShapeNoLet fldBadB = true := ⟨rfl, rfl⟩

/-- …and the `Expr` side has no stored pi at all, so `PosIndex` §4.2's `hlen` is *also* false here —
`BinderScan` §6 did not create this gap, it exposed it. -/
theorem fldGoodB_gap :
    posBinderDoms fldGoodB = [] ∧ fldGoodB.consumeMData.piArity = 0 ∧ fldGoodB.piArity = 0 :=
  ⟨rfl, rfl, rfl⟩

#eval show Lean.CoreM Unit from do
  let goodB := PosReachWit.tryInd `WGoodB fldGoodB
  let badB := PosReachWit.tryInd `WBadB fldBadB
  unless goodB.toOption.isSome do
    throwError "ScanResidual/§6: `Lean4Lean.addDecl` REJECTS the POSITIVE head-β-redex field \
      `(fun x => (_ : x) → W α) α`.  So the β branch of `recArgOf_binders_noBlock_noLen` excludes \
      nothing reachable, §4's `hβ_not_derivable` is about an unreachable shape only, and this \
      file's §6 prose is overstated -- re-measure before trusting it"
  unless badB.toOption.isNone do
    throwError "ScanResidual/§6: `Lean4Lean.addDecl` ACCEPTS the NON-POSITIVE head-β-redex field \
      `(fun x => (_ : W x) → W α) α`.  `checkPositivity` is therefore NOT β-reducing before it \
      scans, so the β branch of `PosIndex.recArgOf_binders_noBlock` is FALSE, not merely unproved. \
      This is a soundness alarm: stop and re-run `docs/handoff-scanresidual.md` §2"
  Lean.logInfo "ScanResidual/§6: POSITIVE head-β-redex field ACCEPTED (so the β residual excludes a \
    REACHABLE accepted declaration -- it is real), NON-POSITIVE head-β-redex field REJECTED (so the \
    β branch is a proof gap, not a bug) ✓"

end ScanResidualWit

/-! ## §7 The limits, each measured or proved

**(a) Item 1 is proved, and it is *not* the whole `.letE` residual.**  §2's
`instantiate1'_instantiate1'_closed` is `BinderScan` §9(d)'s obligation, general in the gap and
hole-free, and §3's `ScanCert.unsubst_fvar_all` is `BinderScan` §4 with `scanShapeNoLet` **deleted**.
But `BinderScan` §9(d)'s further claim that `scanShapeNoLet` then "disappears from §5 and §6" is
**false**, and this is measured, not guessed:

* §5 of `BinderScan` spends `hs` in *two* places — `unsubst_fvar`'s side condition (§3 kills it) and
  its own `.letE` **head** case (§3 cannot).
* The head case needs `whnf`'s ζ, and unlike `whnf_mdata` it is **not** an `M Expr` equality:
  `whnf'`'s `.mdata` arm returns before the cache (`TypeChecker.lean`:531), whereas `.letE` falls
  through to `whnfCore'`, whose `.letE` arm is `save <|← whnfCore (body.instantiate1 val)`
  (`TypeChecker.lean`:416-417) — it writes the cache under the **pre-ζ** key, so the two
  computations' states differ after the step.
* And even granting the equality, **§5's induction would have no measure**: the equality is at the
  *same* `inductiveFuel` (as `checkPositivity_loop_mdata` is), while `body.instantiate1' val` is not
  a structural subterm of `.letE _ _ val body _` and admits no size measure — `let x := big; x x`
  ζ-reduces to `big big`.  The `.mdata` case escapes this only because `e` *is* a subterm of
  `.mdata m e`.  So closing it needs a termination argument for the head-ζ chain (morally
  `whnfCore`'s own) or the `whnf'.WF` bridge, not a substitution lemma.

**(b) Item 2 is real, not vacuous** — the measurement the previous round declined to make.
`Lean4Lean.addDecl` **accepts** a constructor field whose type is a head β-redex contracting to a
positive pi and **rejects** its non-positive twin (§6, executable).  `scanShapeNoLet` is `true` on
both (§6's `fldB_scanShape`), so the β residual is independent of the `.letE` one.

**(c) `hβ` was not derivable** (§4), at a configuration satisfying every other hypothesis of
`BinderScan` §6 — the translation, the context invariant, `scanShapeNoLet`, and `checkPositivity`'s
success as a real monadic value — where `hβ`'s conclusion is false and the theorem's conclusion is
true.  So the plan "discharge `hβ` from the other hypotheses" is impossible, exactly as it was for
`hlen` (`BinderScan` §7).  The β branch has to be *proved*.

**(d) What proving it costs, stated exactly.**  Two pieces, and §5 supplies the first:

1. *`VExpr` side, done.*  `VExpr.noConsts_betaHead` (§5) — block-freeness survives head β, no typing
   hypothesis.  With it, §5.2 weakens `hβ` to
   `S.piArity = 0 → (r.binders = [] ∨ hasIndOcc stats.indConsts t = false)`, whose second arm is the
   checker's own early return.  This is a strict weakening (`hβ_beta_of_hβ`), and it does **not**
   cover §6's reachable witness, where `hasIndOcc` is `true`.
2. *`Expr` side, open.*  A `whnf`-β behaviour lemma at `.app (.lam ..) a`, plus `TrExprS.inst`
   (`Verify/Typing/Lemmas.lean`:2189) — which, unlike the ζ twin `TrExprS.inst_let`, requires
   `t₀ : env.HasType Us.length Δ.toCtx e₀' A₀`.  So a β clause imports a **typing** hypothesis into
   `TrExprS.piBinderDoms_noConsts`, which is currently typing-free; that asymmetry, not the β step,
   is item 2's real price.  `VExpr.betaHead_eq_self_of_noLam` (`B6`:168) is *not* a route: §6's
   reachable witness translates to a term containing a `.lam`.

**(e) `BinderScan` §8's tripwire is NOT retired.**  Q4 of `docs/handoff-scanresidual.md` predicted it
would become vacuous; it does not, because (a) shows `scanShapeNoLet` survives in §5/§6.  §6 above
arms a *second*, independent tripwire on the β debt rather than replacing it.

**(f) No `decide`.**  §4's witness is discharged by `rw`/`simp` on `VIndRestore.recog`,
`recogAt`, `prRestore`, `VExpr.piArity` and `VExpr.splitPis` — the same route `BinderScan` §7 uses,
and for the same reason: the block name is a bound `Name`, so the goal has free variables and `decide`
is unavailable (`PosReach` §5(c)).  §1/§2's index arithmetic is `omega` inside `rw [if_pos]`/
`rw [if_neg]`, never `decide`.

**(g) `VIndRecArg.exists_indep` is untouched and off this path**, for `PosIndex` §7(g)'s reason:
every statement here is a substitution equality, a `NoConsts` fact about a telescope entry, or
`checkPositivity`'s control flow. -/

#print axioms Lean.Expr.instantiate1'_bvar_lt
#print axioms Lean.Expr.instantiate1'_bvar_self
#print axioms Lean.Expr.instantiate1'_bvar_gt
#print axioms Lean.Expr.liftLooseBVars_bvar_lt
#print axioms Lean.Expr.liftLooseBVars_bvar_ge
#print axioms Lean.Expr.liftLooseBVars_instantiate1'
#print axioms Lean.Expr.instantiate1'_instantiate1'_closed
#print axioms Lean.Expr.instantiate1'_instantiate1'_fvar
#print axioms Lean4Lean.scanHead_instantiate1'_fvar
#print axioms Lean4Lean.ScanCert.of_scanHead_false
#print axioms Lean4Lean.scanHead_cases
#print axioms Lean4Lean.ScanCert.unsubst_fvar_all
#print axioms Lean4Lean.AddInductive.betaWitVal_piArity
#print axioms Lean4Lean.AddInductive.betaWitVal_betaHead
#print axioms Lean4Lean.hβ_not_derivable
#print axioms Lean4Lean.VExpr.noConsts_mkApp'
#print axioms Lean4Lean.VExpr.noConsts_spine
#print axioms Lean4Lean.VExpr.noConsts_betaSpine
#print axioms Lean4Lean.VExpr.noConsts_betaHead
#print axioms Lean4Lean.recArgOf_binders_piBinderDoms_beta
#print axioms Lean4Lean.recArgOf_binders_noBlock_of_noConsts
#print axioms Lean4Lean.recArgOf_binders_noBlock_noLen_beta
#print axioms Lean4Lean.hβ_beta_of_hβ
#print axioms Lean4Lean.ScanResidualWit.fldB_scanShape
#print axioms Lean4Lean.ScanResidualWit.fldGoodB_gap

end Lean4Lean
