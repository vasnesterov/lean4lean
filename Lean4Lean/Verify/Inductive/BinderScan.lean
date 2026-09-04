import Lean4Lean.Verify.Inductive.PosIndex

/-!
# The binder scan, VExpr-indexed: deleting `PosIndex`'s arity hypothesis

`Verify/Inductive/PosIndex.lean` §4.2 (`recArgOf_binders_noBlock`) carries
`hlen : r.binders.length ≤ t.consumeMData.piArity`.  Two rounds named the same next step — the
general theorem *"the loop scans every `VExpr` binder"*, which would **delete** the hypothesis rather
than weaken it.  This file is that theorem, and the precise account of what is left.
-/

set_option autoImplicit false

namespace Lean4Lean

/-! ## §1 Two vacuity lemmas on the `VExpr` side -/

theorem VExpr.piBinderDoms_eq_nil : ∀ {e : VExpr}, (∀ A B, e ≠ .forallE A B) → e.piBinderDoms = []
  | .bvar _, _ | .sort _, _ | .const .., _ | .app .., _ | .lam .., _ => rfl
  | .forallE A B, h => absurd rfl (h A B)

/-- A block-free `VExpr` has block-free binder domains.  The `VExpr` twin of
`posBinderDoms_noOcc`. -/
theorem VExpr.noConsts_piBinderDoms {Sn : List Name} :
    ∀ {e : VExpr}, VExpr.NoConsts Sn e → ∀ A ∈ e.piBinderDoms, VExpr.NoConsts Sn A
  | .forallE A B, h, C, hC => by
      rw [VExpr.piBinderDoms_forallE, List.mem_cons] at hC
      obtain ⟨hA, hB⟩ := h
      exact hC.elim (fun h => h ▸ hA) (VExpr.noConsts_piBinderDoms hB C)
  | .bvar _, _, _, hC | .sort _, _, _, hC | .const .., _, _, hC
  | .app .., _, _, hC | .lam .., _, _, hC => absurd hC nofun

/-- A projection translates to a recursor **application**, never to a pi — so `TrProj`'s output has
no leading binder for the scan to miss.  The one fact that makes the `.proj` clause of §3 vacuous. -/
theorem VInductDecl'.projTerm_ne_forallE (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps ιs : List VExpr) (i : Nat) (e : VExpr) :
    ∀ A B, D.projTerm T C us ps ιs i e ≠ .forallE A B :=
  VExpr.mkApp_ne_forallE (by rintro _ _ ⟨⟩)

/-! ## §2 The scan certificate

The `Expr`-side datum the bridge consumes.  It is **not** `posBinderDoms`: at a `.letE` it recurses
into the ζ-*reduct*, which is exactly the step `whnf` takes and `posBinderDoms` cannot see, and it is
trivially satisfied at every head whose `TrExprS` image has no leading pi. -/

open Lean in
/-- **What a successful positivity scan certifies about a field type.**  Read the clauses as the
`whnf`-following descent: strip `.mdata`, ζ-reduce a `.letE`, check each `.forallE` domain, and stop
at any other head — where the bridge's conclusion is vacuous or supplied by the context. -/
inductive ScanCert (p : Expr → Bool) : Expr → Prop
  | miss {e} : anySub p e = false → ScanCert p e
  | forallE {nm dom body bi} : anySub p dom = false → ScanCert p body →
      ScanCert p (.forallE nm dom body bi)
  | mdata {m e} : ScanCert p e → ScanCert p (.mdata m e)
  | letE {nm ty val body nd} : ScanCert p (body.instantiate1' val) →
      ScanCert p (.letE nm ty val body nd)
  | bvar {i} : ScanCert p (.bvar i)
  | fvar {fv} : ScanCert p (.fvar fv)
  | sort {u} : ScanCert p (.sort u)
  | const {c us} : ScanCert p (.const c us)
  | app {f a} : ScanCert p (.app f a)
  | lam {nm ty b bi} : ScanCert p (.lam nm ty b bi)
  | lit {l} : ScanCert p (.lit l)
  | proj {s i e} : ScanCert p (.proj s i e)
  | mvar {mv} : ScanCert p (.mvar mv)

variable {env : VEnv} {Us : List Name} {Sn : List Name} {p : Lean.Expr → Bool}

/-! ## §3 The bridge — every `VExpr` binder domain is scanned

The theorem the two prior rounds priced and declined.  Induction on the **certificate**, inverting
`TrExprS` at each node; the `.letE` clause is discharged by `TrExprS.inst_let`
(`Verify/Typing/Lemmas.lean`:2280), whose `VExpr` side is *unchanged* — which is why no `VLCtx.WF`,
no `VContext` and no `vlet`↔`ldecl` dictionary is needed here. -/

open Lean in
/-- **Every leading pi domain of the translation is block-free.**  No arity hypothesis: the
`.mdata`, `.letE` and let-bound-variable cases — the three that make
`S.piArity ≤ t.consumeMData.piArity` false — are each closed on their own terms. -/
theorem TrExprS.piBinderDoms_noConsts (henv : VEnv.Ordered env)
    (hpS : ∀ c us, c ∈ Sn → p (.const c us) = true)
    (hlit : ∀ l : Lean.Literal, anySub p l.toConstructor = false)
    (hproj : ∀ Γ s i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConsts Sn x → VExpr.NoConsts Sn y) :
    ∀ {t : Expr}, ScanCert p t → ∀ {Δ : VLCtx} {S : VExpr}, TrExprS env Us Δ t S →
      (∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts Sn x) →
      ∀ A ∈ S.piBinderDoms, VExpr.NoConsts Sn A := by
  intro t hcert
  induction hcert with
  | miss h =>
    intro _ _ H hctx
    exact VExpr.noConsts_piBinderDoms (H.noConsts hpS hlit hproj hctx h)
  | forallE hdom _ ih =>
    intro _ _ H hctx
    let .forallE _ _ hty hbody := H
    intro A hA
    rw [VExpr.piBinderDoms_forallE, List.mem_cons] at hA
    rcases hA with rfl | hA
    · exact hty.noConsts hpS hlit hproj hctx hdom
    · exact ih hbody (VLCtx.noConsts_cons trivial hctx) A hA
  | mdata _ ih =>
    intro _ _ H hctx
    let .mdata h := H
    exact ih h hctx
  | letE _ ih =>
    intro _ _ H hctx
    let .letE _ _ hval hbody := H
    exact ih (hbody.inst_let henv hval) hctx
  | bvar =>
    intro _ _ H hctx
    let .bvar h := H
    exact VExpr.noConsts_piBinderDoms (hctx _ _ _ h)
  | fvar =>
    intro _ _ H hctx
    let .fvar h := H
    exact VExpr.noConsts_piBinderDoms (hctx _ _ _ h)
  | sort => intro _ _ H _; let .sort _ := H; exact nofun
  | const => intro _ _ H _; let .const _ _ _ := H; exact nofun
  | app => intro _ _ H _; let .app _ _ _ _ := H; exact nofun
  | lam => intro _ _ H _; let .lam _ _ _ := H; exact nofun
  | lit =>
    intro _ _ H hctx
    let .lit _ h := H
    exact VExpr.noConsts_piBinderDoms (h.noConsts hpS hlit hproj hctx (hlit _))
  | mvar => intro _ _ H _; nomatch H
  | proj =>
    intro _ _ H _
    let .proj _ hpr := H
    cases hpr
    rw [VExpr.piBinderDoms_eq_nil (VInductDecl'.projTerm_ne_forallE _ _ _ _ _ _ _ _)]
    exact nofun



/-! ## §4 The certificate is stable under the loop's fvar substitution

`checkPositivity.loop` descends a pi by `withLocalDecl` + `instantiate1`, so its recursive evidence is
about `body.instantiate1 (.fvar fv)` while §2's `.forallE` clause wants it about `body`.  Reading it
back is structural on the `.mdata`/`.forallE` skeleton — **except at a `.letE`**, where §2's clause
recurses into `body.instantiate1' val` and un-substituting would need the σ-composition
`(b[fvar v]_{d+1})[v'[fvar v]_d]_0 = (b[v']_0)[fvar v]_d`, whose adjacent-index form
(`instantiate1'_instantiate1'`, `Verify/Expr.lean`:1116) is the only one in the tree.

So this section carries a syntactic side condition naming exactly that gap. -/

open Lean in
/-- No `.letE` on the descent path the scan follows (through head `.mdata` and pi codomains).
Nothing is said about domains, values, or anything under an `.app`. -/
def scanShapeNoLet : Expr → Bool
  | .letE .. => false
  | .mdata _ e => scanShapeNoLet e
  | .forallE _ _ b _ => scanShapeNoLet b
  | _ => true

open Lean in
theorem scanShapeNoLet_instantiate1'_fvar (v : FVarId) :
    ∀ (e : Expr) (d : Nat), scanShapeNoLet (e.instantiate1' (.fvar v) d) = scanShapeNoLet e
  | .letE .., _ | .mvar _, _ | .sort _, _ | .const .., _ | .fvar _, _
  | .lit _, _ | .app .., _ | .lam .., _ | .proj .., _ => rfl
  | .bvar i, d => by
      show scanShapeNoLet (if i < d then _ else if i = d then _ else _) = _
      split; · rfl
      split <;> rfl
  | .mdata _ e, d => scanShapeNoLet_instantiate1'_fvar v e d
  | .forallE _ _ b _, d => scanShapeNoLet_instantiate1'_fvar v b (d+1)

open Lean in
/-- The `miss` clause reads back for free: `anySub` is invariant under an fvar substitution
(`anySub_instantiate1'_fvar`, `PosScan` §3.1). -/
theorem ScanCert.miss_unsubst
    (hne : ∀ e : Lean.Expr, (∀ c us, e ≠ .const c us) → p e = false) (v : FVarId)
    {e : Expr} {d : Nat}
    (h : anySub p (e.instantiate1' (.fvar v) d) = false) : ScanCert p e :=
  .miss ((anySub_instantiate1'_fvar hne v e d).symm.trans h)

open Lean in
/-- **Reading the certificate back through the loop's substitution.**  Structural on `e`; the
`.letE` case is where the side condition is spent. -/
theorem ScanCert.unsubst_fvar
    (hne : ∀ e : Lean.Expr, (∀ c us, e ≠ .const c us) → p e = false) (v : FVarId) :
    ∀ (e : Expr) (d : Nat), scanShapeNoLet e = true →
      ScanCert p (e.instantiate1' (.fvar v) d) → ScanCert p e
  | .mdata m e, d, hs, hc => by
      have : (Expr.mdata m e).instantiate1' (.fvar v) d
          = .mdata m (e.instantiate1' (.fvar v) d) := rfl
      rw [this] at hc
      cases hc with
      | miss h => exact ScanCert.miss_unsubst hne v (e := .mdata m e) (d := d) h
      | mdata h => exact .mdata (ScanCert.unsubst_fvar hne v e d hs h)
  | .forallE nm dom body bi, d, hs, hc => by
      have : (Expr.forallE nm dom body bi).instantiate1' (.fvar v) d
          = .forallE nm (dom.instantiate1' (.fvar v) d)
              (body.instantiate1' (.fvar v) (d+1)) bi := rfl
      rw [this] at hc
      cases hc with
      | miss h =>
        exact ScanCert.miss_unsubst hne v (e := .forallE nm dom body bi) (d := d) h
      | forallE hd hb =>
        exact .forallE ((anySub_instantiate1'_fvar hne v dom d).symm.trans hd)
          (ScanCert.unsubst_fvar hne v body (d+1) hs hb)
  | .letE .., _, hs, _ => absurd hs nofun
  | .bvar _, _, _, _ => .bvar
  | .fvar _, _, _, _ => .fvar
  | .mvar _, _, _, _ => .mvar
  | .sort _, _, _, _ => .sort
  | .const .., _, _, _ => .const
  | .app .., _, _, _ => .app
  | .lam .., _, _, _ => .lam
  | .lit _, _, _, _ => .lit
  | .proj .., _, _, _ => .proj

/-! ## §5 The checker produces the certificate

`checkPositivity.loop`'s success **is** a `ScanCert`, on the `.letE`-free descent path.  Three facts
are consumed and all three are cited, not rebuilt: `whnf_forallE` and `checkPositivity_loop_forallE`
(`PosScan` §3.2/§3.3) for the pi step, and `checkPositivity_loop_mdata` (`PosReach` §2) for the
annotation step — the latter being an equality at the **same** fuel, which is why the `.mdata` case is
a *structural* recursion on `t` nested inside the fuel induction rather than a fuel step.

Note what is **not** here: no δ, no β, no ι, no `Nat`-literal or native reduction.  §3's conclusion is
vacuous at every head where `whnf` would perform one of those, so the loop's `whnf` needs to be
understood at exactly two heads. -/

namespace AddInductive
open Lean hiding Environment Exception
open Kernel

/-- `hasIndOcc`'s predicate is `false` off the `.const` nodes — the side condition
`ScanCert.unsubst_fvar` needs, and the same one `hasIndOcc_instantiate1'_fvar` discharges. -/
theorem indOcc_hne (indConsts : Array Expr) : ∀ e : Expr, (∀ c us, e ≠ .const c us) →
    (fun e => match e with
      | .const e _ => indConsts.any fun I => I.constName! == e
      | _ => false) e = false := by
  intro e' he'
  cases e' <;> first | rfl | exact absurd rfl (he' _ _)

/-- **A successful positivity scan is a scan certificate.**  No arity hypothesis, no fuel
hypothesis on the caller's side, and — on the `.letE`-free path — no residual. -/
theorem checkPositivity_loop_scanCert {stats : InductiveStats} {ctor : Name} {idx : Nat} :
    ∀ (fuel : Nat) (t : Expr), scanShapeNoLet t = true → ∀ (c : Context) (u : Unit),
      checkPositivity.loop stats ctor idx t fuel c = .ok u →
      ScanCert (fun e => match e with
        | .const e _ => stats.indConsts.any fun I => I.constName! == e
        | _ => false) t := by
  intro fuel
  induction fuel with
  | zero => intro t _ c u h; rw [checkPositivity.loop] at h; exact absurd h nofun
  | succ fuel ih =>
    intro t
    induction t with
    | mdata m e ihe =>
      intro hs c u h
      rw [checkPositivity_loop_mdata] at h
      exact .mdata (ihe hs c u h)
    | forallE nm dom body bi _ _ =>
      intro hs c u h
      rcases checkPositivity_loop_forallE h with hnone | ⟨hd, dom', -, hrec⟩
      · exact .miss (by rwa [hasIndOcc_eq] at hnone)
      · refine .forallE (by rwa [hasIndOcc_eq] at hd) ?_
        have hrec' : checkPositivity.loop stats ctor idx
            (body.instantiate1' (.fvar ⟨c.ngen.curr⟩)) fuel (posPush c nm dom' bi) = .ok u := by
          rwa [Lean.Expr.instantiate1_eq] at hrec
        exact ScanCert.unsubst_fvar (indOcc_hne _) ⟨c.ngen.curr⟩ body 0 hs
          (ih _ (by rw [scanShapeNoLet_instantiate1'_fvar]; exact hs) _ _ hrec')
    | letE _ _ _ _ _ _ _ _ => intro hs _ _ _; exact absurd hs nofun
    | bvar _ => exact fun _ _ _ _ => .bvar
    | fvar _ => exact fun _ _ _ _ => .fvar
    | mvar _ => exact fun _ _ _ _ => .mvar
    | sort _ => exact fun _ _ _ _ => .sort
    | const _ _ => exact fun _ _ _ _ => .const
    | app _ _ _ _ => exact fun _ _ _ _ => .app
    | lam _ _ _ _ _ _ => exact fun _ _ _ _ => .lam
    | lit _ => exact fun _ _ _ _ => .lit
    | proj _ _ _ _ => exact fun _ _ _ _ => .proj

/-- The same at the entry point `checkConstructors` calls. -/
theorem checkPositivity_scanCert {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {t : Expr} {c : Context} {u : Unit} (hs : scanShapeNoLet t = true)
    (h : checkPositivity stats t ctor idx c = .ok u) :
    ScanCert (fun e => match e with
      | .const e _ => stats.indConsts.any fun I => I.constName! == e
      | _ => false) t := by
  rw [checkPositivity] at h
  obtain ⟨-, -, h⟩ := M_bind_ok h
  exact checkPositivity_loop_scanCert (ctor := ctor) (idx := idx) _ t hs c u h

end AddInductive

/-! ## §6 `PosIndex` §4.2 with the arity hypothesis gone from the reachable branch

The composition.  `hlen : r.binders.length ≤ t.consumeMData.piArity` is **deleted**; what replaces it
is not another arity bound:

* `henv : VEnv.Ordered env` — free at every call site, and used only by §3's `.letE` clause;
* `hs : scanShapeNoLet t = true` — syntactic, and §5's residual;
* `hβ : S.piArity = 0 → r.binders = []` — the head-β-redex branch **only**, and *implied by* the old
  `hlen` (§6.1), so this theorem is strictly stronger than `PosIndex` §4.2 on that branch.

The branch that mattered — `r.binders = S.piBinderDoms`, the one `PosIndex` §3.2's witness and
`PosReach` §4's tripwire live in — now carries **no** hypothesis relating the two arities. -/

open Lean AddInductive in
/-- **Part (B) of `VIndField.WF.pos`, with no `Expr`/`VExpr` arity hypothesis.**  `PosIndex` §3.2's
counterexample is no longer excluded by an arity bound: it is excluded because §5 turns the
*rejection* into a certificate, and §3 consumes the certificate at the `VExpr` telescope. -/
theorem recArgOf_binders_noBlock_noLen {stats : InductiveStats} {ctor : Name} {idx : Nat}
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
    (hβ : S.piArity = 0 → r.binders = []) :
    ∀ B ∈ r.binders, D.NoBlock B := by
  rcases recArgOf_binders_piBinderDoms hr with hb | h0
  · intro B hB
    exact H.piBinderDoms_noConsts henv (hasIndOcc_hpS hS) hlit hproj
      (checkPositivity_scanCert hs hchk) hctx B (hb ▸ hB)
  · rw [hβ h0]; exact nofun

/-! ### §6.1 The replacement really is a weakening

`hβ` is what `PosIndex` §4.2 *uses* `hlen` for in its second branch, and nothing more — so any caller
that could discharge the old hypothesis can discharge the new one. -/

open Lean in
/-- The old arity hypothesis implies the new head-β one, via `TrExprS.piArity_le`. -/
theorem hβ_of_hlen {Δ : VLCtx} {t : Lean.Expr} {S : VExpr} {r : VIndRecArg}
    (H : TrExprS env Us Δ t S) (hlen : r.binders.length ≤ t.consumeMData.piArity) :
    S.piArity = 0 → r.binders = [] := by
  intro h0
  have : t.consumeMData.piArity = 0 := Nat.le_zero.1 (h0 ▸ H.consumeMData.piArity_le)
  rw [this, Nat.le_zero, List.length_eq_zero_iff] at hlen
  exact hlen

/-! ## §7 The deleted hypothesis was **not derivable**, and the witness is airtight

`hlen` could not have been discharged as a lemma: this section exhibits a configuration satisfying
*every* hypothesis of `PosIndex` §4.2 — the translation, the context invariant, and `checkPositivity`'s
success at a **real monadic value**, not a hand-waved one — at which `hlen` is **false** while the
conclusion holds.  So the two prior rounds' plan "discharge `hlen` from `hchk`" was impossible; only
the route §3-§6 takes (change what the `Expr` side certifies) can work.

The witness is a **let-bound de Bruijn variable**: `t = .bvar 0` in a `VLCtx` whose head entry is a
`vlet` whose value is a pi.  `posBinderDoms t = []` and `t.consumeMData.piArity = 0`, while
`S.piArity = 1`.  `.bvar` is chosen over `.fvar` deliberately: `whnf'`'s **first** match arm returns a
`.bvar` unchanged with no cache lookup and no `LocalContext` consulted, so `checkPositivity`'s success
is provable without any R1/R2 dictionary. -/

namespace AddInductive
open Lean hiding Environment Exception
open Kernel

/-- **`whnf` is the identity on a `.bvar`, positively.**  `whnf_forallE`'s missing direction, at the
one head where the refutation needs it. -/
theorem whnf_bvar {i : Nat} {c : Context} {k : Nat} (hr : c.fuel.recDepth = k+1) :
    (liftM (TypeChecker.whnf (.bvar i)) : M Expr) c = .ok (.bvar i) := by
  simp only [liftM, monadLift, MonadLift.monadLift, TypeChecker.whnf, TypeChecker.Inner.whnf,
    TypeChecker.RecM.run, TypeChecker.M.run, readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, bind, StateT.bind, StateT.pure, pure, StateT.run', Except.bind,
    Functor.map, Except.map, Except.pure, hr, TypeChecker.Methods.withFuel,
    TypeChecker.Inner.whnf', ReaderT.pure]

/-- A de Bruijn variable carries no block occurrence: `anySub` at a `.bvar` is the predicate itself,
and the predicate is `false` off the `.const` nodes.  No `decide` — `Array.any` would not reduce
(`PosScan` §3.5). -/
theorem hasIndOcc_bvar (indConsts : Array Expr) (i : Nat) :
    hasIndOcc indConsts (.bvar i) = false := by
  rw [hasIndOcc_eq, anySub_eq]; rfl

end AddInductive

namespace AddInductive
open Lean hiding Environment Exception
open Kernel

/-- **`checkPositivity` accepts a bare de Bruijn variable**, at any fuel that is not exhausted. -/
theorem checkPositivity_bvar_ok {stats : InductiveStats} {ctor : Name} {idx : Nat} {i : Nat}
    {c : Context} {k f : Nat} (hr : c.fuel.recDepth = k+1) (hf : c.fuel.inductiveFuel = f+1) :
    checkPositivity stats (.bvar i) ctor idx c = .ok () := by
  rw [checkPositivity]
  simp only [readThe, MonadReaderOf.read, ReaderT.read, ReaderT.bind, bind, pure,
    Except.bind, Except.pure]
  rw [hf, checkPositivity.loop]
  simp only [bind, ReaderT.bind, whnf_bvar hr, Except.bind, hasIndOcc_bvar, Bool.not_false,
    if_true, pure, ReaderT.pure, Except.pure]

end AddInductive

open Lean AddInductive in
/-- **`hlen` was not derivable — the witness, with `checkPositivity`'s success as a real monadic
value.**  A let-bound de Bruijn variable whose `vlet` value is a pi: the `Expr` side has arity `0`,
the `VExpr` side arity `1`, the recogniser fires with one binder, `checkPositivity` **accepts**, and
every other hypothesis of `PosIndex` §4.2 holds.  So `r.binders.length ≤ t.consumeMData.piArity` is
false here while the conclusion `∀ B ∈ r.binders, NoConsts Sn B` is true — which is why §6 had to
replace the hypothesis rather than discharge it.

`whnf` never touches a `LocalContext` on this path (`whnf'`'s first arm), so no R1/R2 dictionary and no
`M.WF` is involved. -/
theorem hlen_not_derivable {env : VEnv} {Sn : List Name} {I : Name} (hI : I ∉ Sn)
    {stats : InductiveStats} {ctor : Name} {idx : Nat} {cx : Context} {k f i κ : Nat}
    (hr : cx.fuel.recDepth = k+1) (hf : cx.fuel.inductiveFuel = f+1) :
    ∃ (Δ : VLCtx) (t : Lean.Expr) (S : VExpr) (r : VIndRecArg),
      TrExprS env [] Δ t S ∧
      (∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts Sn x) ∧
      checkPositivity stats t ctor idx cx = .ok () ∧
      scanShapeNoLet t = true ∧
      (prRestore I).recogAt i κ S = some r ∧
      posBinderDoms t = [] ∧ t.consumeMData.piArity = 0 ∧ S.piArity = 1 ∧
      r.binders.length = 1 ∧
      ¬ (r.binders.length ≤ t.consumeMData.piArity) ∧
      (∀ B ∈ r.binders, VExpr.NoConsts Sn B) := by
  refine ⟨[(none, .vlet (.sort .zero) (.forallE (.sort .zero) (.const I [])))], .bvar 0,
    .forallE (.sort .zero) (.const I []),
    { binders := [.sort .zero], idx := κ, args := [] }, .bvar rfl, ?_,
    checkPositivity_bvar_ok hr hf, rfl, ?_, rfl, rfl, rfl, rfl, Nat.not_succ_le_zero 0, ?_⟩
  · refine VLCtx.noConsts_cons ⟨trivial, hI⟩ ?_
    intro _ _ _ h; exact absurd h nofun
  · rw [VIndRestore.recogAt]
    simp [prRestore, VExpr.piArity, VExpr.splitPis]
  · intro B hB
    rcases List.mem_cons.1 hB with rfl | h
    · trivial
    · exact absurd h nofun

/-! ## §8 The new residual is real, not vacuous — an executable tripwire

`PosReach` §4's tripwire is **untouched** and still meaningful: it guards `PosIndex` §4.2, which stays
in the tree, and its arms are still the live check that `addDecl` routes through `checkPositivity` and
that the checker rejects an annotated non-positive field.

What §6 changes is *which* facts are load-bearing, so this section arms a tripwire on the new one.
`recArgOf_binders_noBlock_noLen` no longer rests on an unproved behavioural claim in the `.mdata`
direction — `whnf_mdata` and `whnf_forallE` are theorems read off `whnf'`'s source, so a change there
breaks the **build**, not the statement.  Its one remaining behavioural debt is `scanShapeNoLet`: the
`.letE` descent path, where §5's induction stops.  The two things worth guarding are

1. that the excluded shape **occurs in accepted declarations** (else §6's hypothesis is free and the
   residual is a fiction), and
2. that the checker **does** reject the non-positive instance of it (else the theorem §5 cannot yet
   prove is not merely unproved but false).

Both are measured below at `Lean4Lean.addDecl`. -/

namespace BinderScanWit
open Lean

/-- A positive field behind a `let`: `let β := α; (_ : β) → W α`.  `scanShapeNoLet` is `false` on it. -/
def fldGoodL : Expr :=
  .letE `β (.sort (.succ .zero)) (.bvar 0)
    (.forallE `a (.bvar 0) (.app (.const `WGoodL []) (.bvar 2)) .default) false

/-- Its non-positive twin: `let β := α; (_ : W α) → W α`. -/
def fldBadL : Expr :=
  .letE `β (.sort (.succ .zero)) (.bvar 0)
    (.forallE `a (.app (.const `WBadL []) (.bvar 1))
      (.app (.const `WBadL []) (.bvar 2)) .default) false

/-- §6's new hypothesis is **false** on both, by `rfl` — no environment, no `decide`. -/
theorem fldL_outside_scanShape :
    scanShapeNoLet fldGoodL = false ∧ scanShapeNoLet fldBadL = false := ⟨rfl, rfl⟩

/-- …and the `Expr`/`VExpr` arity gap is there too: no stored pi at all. -/
theorem fldGoodL_gap : posBinderDoms fldGoodL = [] ∧ fldGoodL.consumeMData.piArity = 0 := ⟨rfl, rfl⟩

/-! ### §8.1 The measurement, self-checking

If the positive `let`-field is ever **rejected**, §6's `scanShapeNoLet` hypothesis costs nothing and
this file has overstated its own residual — say so and delete the claim.  If the non-positive
`let`-field is ever **accepted**, then `checkPositivity` does *not* ζ-reduce before scanning, the
theorem §5 leaves open is **false** rather than unproved, and `recArgOf_binders_noBlock_noLen` cannot
be extended to `.letE` at all — which is a soundness-relevant finding about the `let` path, not a
proof-engineering note. -/
#eval show Lean.CoreM Unit from do
  let goodL := PosReachWit.tryInd `WGoodL fldGoodL
  let badL := PosReachWit.tryInd `WBadL fldBadL
  unless goodL.toOption.isSome do
    throwError "BinderScan/§8: `Lean4Lean.addDecl` REJECTS the POSITIVE `let`-headed field \
      `let β := α; (_ : β) → W α`.  So `scanShapeNoLet` excludes nothing reachable and §6's \
      residual is overstated -- re-measure before trusting §8's prose"
  unless badL.toOption.isNone do
    throwError "BinderScan/§8: `Lean4Lean.addDecl` ACCEPTS the NON-POSITIVE `let`-headed field \
      `let β := α; (_ : W α) → W α`.  `checkPositivity` is therefore NOT ζ-reducing before it \
      scans, so the `.letE` clause of §5 is FALSE, not merely unproved, and \
      `recArgOf_binders_noBlock_noLen` can never be extended to cover it.  Stop and re-run \
      `docs/handoff-binderscan.md` §2"
  Lean.logInfo "BinderScan/§8: POSITIVE `let`-headed field ACCEPTED (so §6's `scanShapeNoLet` \
    hypothesis excludes a REACHABLE accepted declaration -- the residual is real), NON-POSITIVE \
    `let`-headed field REJECTED (so §5's missing `.letE` clause is plausibly true and is a \
    proof gap, not a bug) ✓"

end BinderScanWit

/-! ## §9 The limits, each measured or proved

**(a) What is proved, and what it replaces.**  §3 is the general theorem two rounds priced and
declined — *every* `VExpr` binder domain of the translation is block-free, with **no** arity
hypothesis — and it is hole-free.  §5 supplies its `Expr`-side input from `checkPositivity`'s success,
hole-free on the `.letE`-free descent path.  §6 composes them: `PosIndex` §4.2's
`hlen : r.binders.length ≤ t.consumeMData.piArity` is **gone from the branch that matters**
(`r.binders = S.piBinderDoms`) and survives only as `hβ`, which bites on a head β-redex alone and is
implied by the old hypothesis (§6.1).

**(b) `hlen` was never derivable** (§7), at a witness where `checkPositivity` succeeds as a real
monadic value.  So no amount of work on `PosScan`'s `Expr`-side scan could have discharged it; the
statement had to change.  This settles the question the two prior rounds left open in the *negative*
direction they did not consider.

**(c) The three obligations the prior rounds named, re-measured.**
* *The `.letE` clause of the bridge*: **cheap**, one line — `TrExprS.inst_let` already existed
  (`Verify/Typing/Lemmas.lean`:2280) and its `VExpr` side is unchanged, so no `vlet`↔`ldecl`
  dictionary, no `VLCtx.WF`, no `VContext`.
* *The let-bound variable*: **free** — `hctx` already covers it, because `VLCtx.find?` on a `vlet`
  returns the value.
* *`whnf`'s δ*: **owes nothing.**  §3's conclusion is vacuous at every head where `whnf` would
  δ-, β-, ι-, `Nat`- or native-reduce, because `TrExprS` sends `.const`/`.app`/`.lam`/`.proj`/`.lit`
  to targets with no leading pi.  Only two heads need `whnf` understood, and both lemmas were cited.

**(d) What is left, stated exactly.**  One de Bruijn σ-composition at **non-adjacent** indices,
`(b[fvar v]_{d+1})[v'[fvar v]_d]_0 = (b[v']_0)[fvar v]_d`.  The tree has only the adjacent form
(`instantiate1'_instantiate1'`, `Verify/Expr.lean`:1116).  With it, `ScanCert.unsubst_fvar` (§4) loses
its side condition, `scanShapeNoLet` disappears from §5 and §6, and `hlen`'s only survivor is `hβ`.
Nothing about `whnf`'s ζ step as an `M`-value is needed — the certificate absorbs it.

**(e) `hβ` is a second, independent residual**, and its shape is β not ζ: `VExpr.betaHead` can expose
binders that `S` itself does not have (`recArgOf`'s stage 2), and the dictionary for it —
`TrExprS.inst`, whose `VExpr` side *is* `e'.inst e₀'` — exists.  What is missing is the same kind of
`Expr`-side step, at `.app (.lam ..) a`.  `PosIndex` §4.1's docstring says this branch "collapses"
under `hlen`; §6 makes visible that `hlen` was doing that work, which is why deleting it leaves `hβ`.

**(f) No `decide` regression.**  `Lean.Expr.eqv` never appears: §7's `hasIndOcc_bvar` goes through
`hasIndOcc_eq` + `anySub_eq` + `rfl` at a `.bvar` (where the predicate's `_ => false` arm fires without
touching `Array.any`), and §7's one `Nat` fact is `Nat.not_succ_le_zero`.  `decide` was tried at §7's
arity inequality and **rejected** ("Expected type must not contain free variables" — the record
carries the free index `κ`), which is a third distinct way `decide` fails on this path, alongside the
free `Name` and the `Array.anyM.loop` cases `PosReach` §5(c) records.

**(g) `VIndRecArg.exists_indep` is untouched and off this path**, for `PosIndex` §7(g)'s reason: every
statement here is about `NoConsts` of a telescope entry, `checkPositivity`'s control flow, or a
substitution lemma. -/

#print axioms Lean4Lean.VExpr.piBinderDoms_eq_nil
#print axioms Lean4Lean.VExpr.noConsts_piBinderDoms
#print axioms Lean4Lean.VInductDecl'.projTerm_ne_forallE
#print axioms Lean4Lean.TrExprS.piBinderDoms_noConsts
#print axioms Lean4Lean.scanShapeNoLet_instantiate1'_fvar
#print axioms Lean4Lean.ScanCert.miss_unsubst
#print axioms Lean4Lean.ScanCert.unsubst_fvar
#print axioms Lean4Lean.AddInductive.indOcc_hne
#print axioms Lean4Lean.AddInductive.checkPositivity_loop_scanCert
#print axioms Lean4Lean.AddInductive.checkPositivity_scanCert
#print axioms Lean4Lean.recArgOf_binders_noBlock_noLen
#print axioms Lean4Lean.hβ_of_hlen
#print axioms Lean4Lean.AddInductive.whnf_bvar
#print axioms Lean4Lean.AddInductive.hasIndOcc_bvar
#print axioms Lean4Lean.AddInductive.checkPositivity_bvar_ok
#print axioms Lean4Lean.hlen_not_derivable
#print axioms Lean4Lean.BinderScanWit.fldL_outside_scanShape
#print axioms Lean4Lean.BinderScanWit.fldGoodL_gap

end Lean4Lean
