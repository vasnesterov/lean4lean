import Lean4Lean.Verify.Inductive.PosReach

/-!
# The `Expr`→`VExpr` indexing bridge for the positivity binder scan

`Verify/Inductive/PosScan.lean` §5(b) item 3 names exactly one residue: the **indexing**
correspondence, *"that the `k`-th entry of `posBinderDoms F.type` translates to the `k`-th entry of
`r.binders`"*.  The predicate half already exists (`TrExprS.noConsts`, `Verify/Inductive/Add.lean`).
This file supplies the indexing, and then says — with a witness rather than a hedge — exactly which
direction of it is false.

## Contents

* **§1 two telescope readers, and `splitPis` in terms of one of them.**  `posBinderDoms`
  (`PosScan`, `Expr`-side) and `VExpr.piBinderDoms` (here) both collect the leading pi domains.
  `(VExpr.splitPis n e).1 = e.piBinderDoms.take n` **unconditionally**, so `recogAt`'s
  `r.binders = (splitPis S.piArity S).1` is literally `S.piBinderDoms`.
* **§2 the bridge, and it is unconditional in one direction.**  `TrExprS.binderDoms`: the `k`-th
  stored `Expr` domain translates to the `k`-th `VExpr` domain, in the `VLCtx` extended by the first
  `k` `VExpr` domains as `vlam`s.  Its corollary `TrExprS.piArity_le` is `t.piArity ≤ S.piArity` —
  every `Expr` pi forces a `VExpr` pi, never the converse.
* **§3 the converse is FALSE, at every `VEnv` — but the witness is UNREACHABLE.**
  `.mdata`-wrapping a pi hides it from `posBinderDoms` while `TrExprS` translates straight through
  (`trExprS_piArity_lt`), and the sharpened form (`binders_noBlock_not_transferable`) breaks part
  (B) itself: an annotated non-positive field type whose `Expr` scan is *vacuously* clean and whose
  `VExpr` binder carries the block constant.  This is the separation witness `PosScan` §5.5 says it
  did not build — and it separates the **binders**, where `cgmRedex` separated only the head.
  **§3.3** then shows `checkPositivity` **throws** on it (`Verify/Inductive/PosReach.lean`), so it is
  no soundness bug: §4's hypothesis is *weakened* to `(consumeMData t).piArity` rather than dropped,
  and `binders_noBlock_not_transferable_unreachable` carries both halves at one witness.
* **§4 part (B), end to end, under one `Nat` hypothesis.**  `posBinders_noBlock_of_le`: reader +
  `checkPositivity` + `TrExprS` + `r.binders.length ≤ t.consumeMData.piArity` ⟹
  `∀ B ∈ r.binders, D.NoBlock B`.  The hypothesis is the field-level twin of `ElimLoopInv.spine`, and
  §3 shows it cannot be dropped — only weakened to the arity `TrExprS` sees, which is what it now is.
* **§5 the same for the residual arguments and `r.args`.**
* **§6 the limits, each measured or proved.**
-/

set_option autoImplicit false

namespace Lean4Lean

/-! ## §1 The two telescope readers

`PosScan.posBinderDoms` reads the `Expr` side.  The `VExpr` side needs the same function, and it is
*not* in the tree: `VExpr.splitPis` (`Theory/Inductive/Decl.lean`:1144) takes a count, and
`VExpr.piArity` (`Theory/Inductive/Telescope.lean`:95) produces one, but no lemma connects the pair
to a recursive collector.  `VExpr.NoCSubst.splitPis` and `SpineClause.splitPis_length_self` are the
only `splitPis` lemmas, and neither is this. -/

namespace VExpr

/-- The leading pi-domain telescope of a `VExpr` — the `VExpr` twin of `posBinderDoms`. -/
def piBinderDoms : VExpr → List VExpr
  | .forallE A B => A :: piBinderDoms B
  | _ => []

@[simp] theorem piBinderDoms_forallE {A B : VExpr} :
    (VExpr.forallE A B).piBinderDoms = A :: B.piBinderDoms := rfl

/-- **`splitPis` is a prefix of the telescope reader, with no side condition.**  This holds in the
truncating case too: when `e` runs out of pis both sides stop. -/
theorem splitPis_fst : ∀ (n : Nat) (e : VExpr), (splitPis n e).1 = e.piBinderDoms.take n
  | 0, e => by rw [splitPis, List.take_zero]
  | n+1, .forallE A B => by
      rw [splitPis, piBinderDoms_forallE, List.take_succ_cons, ← splitPis_fst n B]
  | _+1, .bvar _ | _+1, .sort _ | _+1, .const .. | _+1, .app .. | _+1, .lam .. => rfl

theorem length_piBinderDoms : ∀ (e : VExpr), e.piBinderDoms.length = e.piArity
  | .forallE _ B => by rw [piBinderDoms_forallE, List.length_cons, piArity, length_piBinderDoms B]
  | .bvar _ | .sort _ | .const .. | .app .. | .lam .. => rfl

/-- At the term's own pi-arity the split is the whole telescope — which is the form
`VIndRestore.recogAt_binders` hands over. -/
theorem splitPis_piArity_fst (e : VExpr) : (splitPis e.piArity e).1 = e.piBinderDoms := by
  rw [splitPis_fst, ← length_piBinderDoms, List.take_length]

end VExpr

open Lean in
theorem length_posBinderDoms : ∀ (e : Expr), (posBinderDoms e).length = e.piArity
  | .forallE _ _ b _ => by
      rw [posBinderDoms, List.length_cons, Lean.Expr.piArity, length_posBinderDoms b]
  | .bvar _ | .sort _ | .const .. | .fvar _ | .mvar _ | .lit _ | .app .. | .lam ..
  | .letE .. | .mdata .. | .proj .. => rfl

/-! ## §2 The bridge

`TrExprS.forallE` (`Verify/Typing/Expr.lean`:170) is structural on both sides — source
`.forallE name ty body bi` to target `.forallE ty' body'`, with the body translated in
`(none, .vlam ty') :: Δ`.  So the `k`-th stored domain and the `k`-th target domain are related in
the `VLCtx` grown by the first `k` target domains, and **that is the whole content of the bridge**:
no `VLCtx.mkFVars`, no R1/R2 dictionary, no `VContext`, and no well-formedness hypothesis.

`Verify/Inductive/Add.lean`'s R1/R2 section supplies `TrExprS.forallE_target` (the target's *shape*)
and `ElimLoopInv.spine` (the `Nat` inequality, for the **constructor** telescope).  Neither is the
pointwise correspondence, and neither is stated for a *field*'s own telescope. -/

/-- Grow a `VLCtx` by a list of `vlam` binders, outermost first — the shape `TrExprS.forallE`
produces when it descends a pi telescope. -/
def VLCtx.pushVLams : List VExpr → VLCtx → VLCtx
  | [], Δ => Δ
  | A :: As, Δ => pushVLams As ((none, .vlam A) :: Δ)

@[simp] theorem VLCtx.pushVLams_nil {Δ : VLCtx} : VLCtx.pushVLams [] Δ = Δ := rfl
@[simp] theorem VLCtx.pushVLams_cons {A : VExpr} {As : List VExpr} {Δ : VLCtx} :
    VLCtx.pushVLams (A :: As) Δ = VLCtx.pushVLams As ((none, .vlam A) :: Δ) := rfl

variable {env : VEnv} {Us : List Name}

open Lean in
/-- **The indexing bridge.**  If the source's `k`-th stored pi domain is `d`, then the target's
`k`-th pi domain exists and `d` translates to it, in the `VLCtx` extended by the target's first `k`
domains.

Proved by structural recursion on the source, with `k` along for the ride; the only two cases are
"the source is a `.forallE`" and "the index is out of range". -/
theorem TrExprS.binderDoms :
    ∀ {Δ : VLCtx} {t : Expr} {S : VExpr}, TrExprS env Us Δ t S →
      ∀ (k : Nat) (d : Expr), (posBinderDoms t)[k]? = some d →
        ∃ A, S.piBinderDoms[k]? = some A ∧
          TrExprS env Us (Δ.pushVLams (S.piBinderDoms.take k)) d A
  | _, .forallE _ _ _ _, _, H, 0, d, hd => by
      let .forallE _ _ hty hbody := H
      rw [posBinderDoms] at hd
      cases Option.some.inj hd
      exact ⟨_, rfl, hty⟩
  | _, .forallE _ _ b _, _, H, k+1, d, hd => by
      let .forallE _ _ _ hbody := H
      rw [posBinderDoms, List.getElem?_cons_succ] at hd
      obtain ⟨A, hA, hAd⟩ := hbody.binderDoms k d hd
      exact ⟨A, by rw [VExpr.piBinderDoms_forallE, List.getElem?_cons_succ]; exact hA,
        by rw [VExpr.piBinderDoms_forallE, List.take_succ_cons, VLCtx.pushVLams_cons]; exact hAd⟩
  | _, .bvar _, _, _, _, _, hd | _, .sort _, _, _, _, _, hd | _, .const .., _, _, _, _, hd
  | _, .fvar _, _, _, _, _, hd | _, .mvar _, _, _, _, _, hd | _, .lit _, _, _, _, _, hd
  | _, .app .., _, _, _, _, hd | _, .lam .., _, _, _, _, hd | _, .letE .., _, _, _, _, hd
  | _, .mdata .., _, _, _, _, hd | _, .proj .., _, _, _, _, hd => absurd hd nofun

open Lean in
/-- **Every source pi forces a target pi.**  The unconditional half of the correspondence, and the
reason §3's failing direction is *equivalent* to an equality rather than independent of it. -/
theorem TrExprS.piArity_le :
    ∀ {Δ : VLCtx} {t : Expr} {S : VExpr}, TrExprS env Us Δ t S → t.piArity ≤ S.piArity
  | _, .forallE .., _, H => by
      let .forallE _ _ _ hbody := H
      exact Nat.succ_le_succ hbody.piArity_le
  | _, .bvar _, _, _ | _, .sort _, _, _ | _, .const .., _, _ | _, .fvar _, _, _
  | _, .mvar _, _, _ | _, .lit _, _, _ | _, .app .., _, _ | _, .lam .., _, _
  | _, .letE .., _, _ | _, .mdata .., _, _ | _, .proj .., _, _ => Nat.zero_le _


/-! ## §3 The converse is false, and it breaks part (B) itself

§2's inequality goes one way only.  The direction part (B) actually needs is the **converse** —
`S.piArity ≤ t.piArity`, equivalently (given §2) equality — because part (B) quantifies over
`r.binders`, a `List VExpr`, while `checkPositivity_binderDoms` quantifies over `posBinderDoms t`, a
`List Expr`.  A scan of a proper *sub*-telescope cannot discharge a quantifier over the whole one.

`Verify/Inductive/Add.lean` already knows this in the abstract: `Lean.Expr.piArity`'s docstring says
*"`TrExprS` does not determine it (`.mdata`/`.letE` translate through)"*, and `ElimLoopInv.spine`
carries the inequality as a **hypothesis** for the constructor telescope.  What follows is the witness
neither states, at a *field*'s telescope, in the two strengths that matter.

`PosScan` §5(b) items 1-2 call the gap *"a weakening, and again in the safe direction"*.  That is true
of the `Expr`-side lemma read on its own and **false for the transfer**: §3.2 exhibits an
`Expr` field type whose stored scan is *vacuously* clean and whose translated binder telescope
carries the block constant.  `PosScan` §5.5 records that it had not built a witness separating
`posBinderDoms` from what the checker scans, the near-miss being that `cgmRedex` differs in the
**head**.  These differ in the **binders**. -/

/-- **§3.1 The telescopes differ, at every `VEnv`.**  `.mdata` at the head of a field type hides a
binder from `posBinderDoms` while `TrExprS.mdata` translates straight through, so
`t.piArity < S.piArity` — and no environment hypothesis is needed, because sorts type themselves. -/
theorem trExprS_piArity_lt (env : VEnv) (m : Lean.MData) (nm : Lean.Name) :
    ∃ (t : Lean.Expr) (S : VExpr), TrExprS env [] [] t S ∧
      t.piArity = 0 ∧ S.piArity = 1 ∧ posBinderDoms t = [] ∧ S.piBinderDoms = [.sort .zero] :=
  ⟨.mdata m (.forallE nm (.sort .zero) (.sort .zero) .default),
    .forallE (.sort .zero) (.sort .zero),
    .mdata (.forallE ⟨_, .sortDF (by decide) (by decide) rfl⟩
      ⟨_, .sortDF (by decide) (by decide) rfl⟩ (.sort rfl) (.sort rfl)),
    rfl, rfl, rfl, rfl⟩

/-! ### §3.2 …and the difference carries a block constant

The sharp form.  Three hypotheses, and each is satisfied by a real block member: the member `I` is a
declared constant, at no universe parameters, whose stored type is `Sort 0` — i.e. a `Prop`-valued
member of the block being declared, in the staged environment `checkConstructors` runs at.

The field type is `.mdata m ((_ : I) → I)`: a **non-positive** field, annotated at the top.  Its
stored pi telescope is empty, so `checkPositivity_binderDoms`' conclusion is *vacuous* on it; its
translation is `∀ (_ : I), I`, on which `VIndRestore.recogAt` fires with `binders = [I]`; and `I` is a
block name, so part (B) fails on the very entry the `Expr` scan could not see. -/

/-- The restoration that recognises `I` at every member: `I` at no levels and no stored arguments. -/
def prRestore (I : Lean.Name) : VIndRestore where
  tyName _ := I
  tyLvls _ := []
  tyArgs _ := []
  ctorName := id
  recName := id

open Lean in
theorem prRestore_recogAt (I : Name) (i k : Nat) :
    (prRestore I).recogAt i k (.forallE (.const I []) (.const I [])) =
      some { binders := [.const I []], idx := k, args := [] } := by
  rw [VIndRestore.recogAt]
  simp [prRestore, VExpr.piArity, VExpr.splitPis]

open Lean AddInductive in
/-- **Part (B) does not transfer from `posBinderDoms`, and the counterexample is a real field
type.**  At any environment declaring `I : Sort 0`, the field type `.mdata m ((_ : I) → I)`
translates to a `VExpr` on which `recogAt` fires with a **blocked** binder, while every domain the
`Expr` scan can see is block-free *because there are none*.

So `checkPositivity_binderDoms` (`PosScan` §3.3) is **not** strong enough to discharge
`VIndField.WF.pos`'s `binders_noBlock`, and no strengthening of the `VExpr` side can fix it: the
missing information is on the `Expr` side. -/
theorem binders_noBlock_not_transferable {env : VEnv} {I : Name} {ci : VConstant}
    (hI : env.constants I = some ci) (hu : ci.uvars = 0) (hty : ci.type = .sort .zero)
    (Sn : List Name) (hIS : I ∈ Sn) (m : MData) (nm : Name) (i k : Nat) :
    ∃ (t : Expr) (S : VExpr) (r : VIndRecArg),
      TrExprS env [] [] t S ∧
      (prRestore I).recogAt i k S = some r ∧
      (∀ B ∈ posBinderDoms t, hasIndOcc #[.const I []] B = false) ∧
      ¬ (∀ B ∈ r.binders, VExpr.NoConsts Sn B) ∧
      t = .mdata m (.forallE nm (.const I []) (.const I []) .default) ∧
      r.binders.length = 1 := by
  have hc : env.HasType 0 [] (.const I []) (.sort .zero) := by
    have := VEnv.IsDefEq.constDF (env := env) (uvars := 0) (Γ := []) (ls := []) (ls' := [])
      hI (by simp) (by simp) (by simp [hu]) .nil
    rwa [hty] at this
  have hc' : env.HasType 0 [.const I []] (.const I []) (.sort .zero) := by
    have := VEnv.IsDefEq.constDF (env := env) (uvars := 0) (Γ := [.const I []]) (ls := [])
      (ls' := []) hI (by simp) (by simp) (by simp [hu]) .nil
    rwa [hty] at this
  have htr : ∀ Δ : VLCtx, TrExprS env [] Δ (.const I []) (.const I []) :=
    fun _ => .const hI rfl (by simp [hu])
  refine ⟨.mdata m (.forallE nm (.const I []) (.const I []) .default),
    .forallE (.const I []) (.const I []), _,
    .mdata (.forallE ⟨_, hc⟩ ⟨_, hc'⟩ (htr _) (htr _)), prRestore_recogAt I i k, ?_, ?_, rfl, rfl⟩
  · simp [posBinderDoms]
  · exact fun h => h _ (List.mem_cons_self ..) hIS



/-! ### §3.3 …but the checker throws it out, so the arity hypothesis is weakened, not dropped

**Answered 2026-09-04** (`docs/handoff-posreach.md`): §3.2's witness is *unreachable*.
`checkPositivity.loop`'s first act is `whnf`, and `whnf'`'s `.mdata` arm
(`Lean4Lean/TypeChecker.lean`:531) descends *past* the annotation — so the loop reaches the
`.forallE` arm, tests `hasIndOcc stats.indConsts dom` on the block-carrying domain, and **throws**.
`Verify/Inductive/PosReach.lean` §1-§3 is that mechanism as theorems; the missing information is in
`checkPositivity_binderDoms`' **statement**, not in `checkPositivity`'s **behaviour**, so there is no
kernel bug here and `bugs-found.md` is untouched.

§3.2 nonetheless stays true, so §4.2's hypothesis cannot simply be deleted.  What it *can* be is
weakened to the arity `TrExprS` actually sees — `(consumeMData t).piArity`, since `TrExprS.mdata`
translates straight through (`TrExprS.consumeMData`, `PosReach` §3.1) and `checkPositivity`'s answer is
invariant under the same stripping (`checkPositivity_consumeMData`, `PosReach` §2).  §4.2 now carries
that form.

**And the weakened form is tight.**  At §3.2's own witness the weakened hypothesis is *satisfied*
(`consumeMData` arity 1, `r.binders.length` 1), so §4.2 is saved from §3.2 by its `hchk` hypothesis
**alone** — i.e. by the rejection below and by nothing else.  Were `whnf` ever to stop descending past
`.mdata`, §4.2 would be **false** rather than merely unproved.  `PosReach` §4's `#eval` tripwire is
armed on exactly that. -/

open Lean AddInductive in
/-- **§3.2's witness never reaches `VIndField.WF.pos`'s consumers.**  `PosReach`'s
`checkPositivity_reject` at the witness shape, with the block occurrence in the domain supplied by
`hasIndOcc_const` rather than by `decide` (`Lean.Expr.eqv` is opaque and `Array.any` does not reduce in
the kernel — `PosScan` §3.5). -/
theorem binders_noBlock_witness_rejected {stats : InductiveStats} {I : Name}
    (hst : stats.indConsts = #[.const I []]) {t : Expr} {m : MData} {nm : Name}
    (ht : t = .mdata m (.forallE nm (.const I []) (.const I []) .default))
    {ctor : Name} {idx : Nat} {cx : Context} {u : Unit} :
    checkPositivity stats t ctor idx cx ≠ .ok u := by
  subst ht; exact checkPositivity_reject_mdata_witness hst

open Lean AddInductive in
/-- **The round's headline, both halves at one witness.**  The same field type that breaks the
`posBinderDoms` transfer (§3.2) is **rejected by `checkPositivity` at every fuel and every context**,
*and* satisfies §4.2's weakened `hlen`.  The three facts together are the precise statement of the
answer: the counterexample is unreachable, the arity gap it exploits is not, and §4.2's truth now rests
on the rejection. -/
theorem binders_noBlock_not_transferable_unreachable {env : VEnv} {I : Name} {ci : VConstant}
    (hI : env.constants I = some ci) (hu : ci.uvars = 0) (hty : ci.type = .sort .zero)
    (Sn : List Name) (hIS : I ∈ Sn) (m : MData) (nm : Name) (i k : Nat)
    {stats : InductiveStats} (hst : stats.indConsts = #[.const I []]) :
    ∃ (t : Expr) (S : VExpr) (r : VIndRecArg),
      TrExprS env [] [] t S ∧
      (prRestore I).recogAt i k S = some r ∧
      (∀ B ∈ posBinderDoms t, hasIndOcc #[.const I []] B = false) ∧
      ¬ (∀ B ∈ r.binders, VExpr.NoConsts Sn B) ∧
      (∀ (ctor : Name) (idx : Nat) (cx : Context) (u : Unit),
        checkPositivity stats t ctor idx cx ≠ .ok u) ∧
      t.piArity = 0 ∧ r.binders.length ≤ t.consumeMData.piArity := by
  obtain ⟨t, S, r, hTr, hrec, hscan, hbad, ht, hlen⟩ :=
    binders_noBlock_not_transferable hI hu hty Sn hIS m nm i k
  exact ⟨t, S, r, hTr, hrec, hscan, hbad,
    fun _ _ _ _ => binders_noBlock_witness_rejected hst ht,
    by rw [ht]; rfl, by rw [hlen, ht]; exact Nat.le_refl _⟩


/-! ## §4 Part (B), end to end, under one `Nat` hypothesis

§3 says the transfer needs `S.piArity ≤ t.piArity`, which by §2 is equality.  This section shows that
is *all* it needs: with that one arithmetic hypothesis, `checkPositivity`'s success plus `recArgOf`'s
answer plus a `TrExprS` give `VIndField.WF.pos`'s `binders_noBlock` outright.

The hypothesis is the field-level twin of `ElimLoopInv.spine` (`Verify/Inductive/Add.lean`:1803),
which carries `Bs.length ≤ type.piArity` for the **constructor** telescope and argues the caller has
it free.  Nobody has carried it for a field's own telescope, and §3 is the proof that it cannot be
dropped rather than merely not-yet-discharged. -/

theorem VLCtx.noConsts_pushVLams {Sn : List Name} :
    ∀ (L : List VExpr) {Δ : VLCtx},
      (∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts Sn x) →
      ∀ v x A, (Δ.pushVLams L).find? v = some (x, A) → VExpr.NoConsts Sn x
  | [], _, h => h
  | _ :: L, _, h => VLCtx.noConsts_pushVLams L (VLCtx.noConsts_cons trivial h)

namespace VExpr

/-- Membership in `splitPis`' telescope, with the index — the shape §2's bridge consumes. -/
theorem mem_splitPis {A : VExpr} : ∀ (n : Nat) (e : VExpr), A ∈ (splitPis n e).1 →
    ∃ k, k < n ∧ e.piBinderDoms[k]? = some A
  | 0, _, h => absurd h nofun
  | n+1, .forallE B C, h => by
      rw [splitPis] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨0, Nat.succ_pos _, rfl⟩
      · obtain ⟨k, hk, hkA⟩ := mem_splitPis n C h
        exact ⟨k+1, Nat.succ_lt_succ hk, by
          rw [piBinderDoms_forallE, List.getElem?_cons_succ]; exact hkA⟩
  | _+1, .bvar _, h | _+1, .sort _, h | _+1, .const .., h | _+1, .app .., h
  | _+1, .lam .., h => absurd h nofun

end VExpr

variable {Sn : List Name} {p : Lean.Expr → Bool}

open Lean in
/-- **The transfer, on the prefix the `Expr` side can see.**  Every domain of `splitPis n S` is
block-free, for any `n ≤ t.piArity`, given the `Expr`-side scan and `TrExprS.noConsts`' three side
conditions.  This is §2's bridge composed with the predicate half, and nothing else. -/
theorem TrExprS.splitPis_noConsts
    (hpS : ∀ c us, c ∈ Sn → p (.const c us) = true)
    (hlit : ∀ l : Lean.Literal, anySub p l.toConstructor = false)
    (hproj : ∀ Γ s i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConsts Sn x → VExpr.NoConsts Sn y)
    {Δ : VLCtx} {t : Expr} {S : VExpr} (H : TrExprS env Us Δ t S)
    (hctx : ∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts Sn x)
    (hscan : ∀ B ∈ posBinderDoms t, anySub p B = false)
    (n : Nat) (hn : n ≤ t.piArity) :
    ∀ A ∈ (VExpr.splitPis n S).1, VExpr.NoConsts Sn A := by
  intro A hA
  obtain ⟨k, hkn, hkA⟩ := VExpr.mem_splitPis n S hA
  have hklt : k < (posBinderDoms t).length := by
    rw [length_posBinderDoms]; omega
  obtain ⟨d, hd⟩ : ∃ d, (posBinderDoms t)[k]? = some d :=
    ⟨_, List.getElem?_eq_getElem hklt⟩
  obtain ⟨A', hA', hTr⟩ := H.binderDoms k d hd
  cases Option.some.inj (hkA.symm.trans hA')
  exact hTr.noConsts hpS hlit hproj (VLCtx.noConsts_pushVLams _ hctx)
    (hscan d (List.mem_iff_getElem?.2 ⟨k, hd⟩))

/-! ### §4.1 `recArgOf`'s binders **are** the target's telescope

`VIndRestore.recogAt_binders` gives `r.binders = (splitPis S.piArity S).1`, which §1 turns into
`S.piBinderDoms`.  `VInductDecl'.recArgOf` has a second stage at `VExpr.betaHead S`, and the
head β-contraction is invisible in the disjunction below for a reason worth stating: `betaHead` is the
identity on a `forallE` (`betaSpine [] f = f`), so the *only* way stage 2 can produce binders that
`S` does not have is for `S` to be a head redex — and then `S.piArity = 0`, which §4.2's hypothesis
already collapses. -/

theorem VExpr.betaHead_forallE {A B : VExpr} :
    VExpr.betaHead (.forallE A B) = .forallE A B := rfl

/-- **The reader's telescope, in `piBinderDoms` form.**  Either the binders are the stored target's
own pi telescope, or the stored target has no pis at all. -/
theorem recArgOf_binders_piBinderDoms {D : VInductDecl'} {i : Nat} {S : VExpr} {r : VIndRecArg}
    (h : D.recArgOf i S = some r) : r.binders = S.piBinderDoms ∨ S.piArity = 0 := by
  rw [VInductDecl'.recArgOf] at h
  cases h1 : D.idRestore.recog D.nm i S with
  | some r' =>
    rw [h1] at h; cases h
    exact .inl (by rw [VIndRestore.recog_binders h1, VExpr.splitPis_piArity_fst])
  | none =>
    rw [h1, Option.orElse] at h
    have hb := VIndRestore.recog_binders h
    rw [VExpr.splitPis_piArity_fst] at hb
    cases S with
    | forallE A B => exact .inl (by rw [hb, VExpr.betaHead_forallE])
    | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ => exact .inr rfl

/-! ### §4.2 `binders_noBlock`, from the checker

The composition.  `hlen` is the one hypothesis §3 shows is indispensable; everything else is either
the checker's success, the reader's answer, the translation, or one of `TrExprS.noConsts`' three side
conditions (`hproj` is the one `Verify/Inductive/Add.lean` leaves open, and it is *its* residue, not
this file's). -/

open Lean AddInductive in
/-- **Part (B) of `VIndField.WF.pos`, from `checkPositivity`.**  `hlen` is `ElimLoopInv.spine` at a
field; `binders_noBlock_not_transferable` (§3.2) is the proof that dropping it makes the statement
false. -/
theorem recArgOf_binders_noBlock {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {cx : Context} {u : Unit} {D : VInductDecl'} {i : Nat} {r : VIndRecArg}
    {Δ : VLCtx} {t : Expr} {S : VExpr}
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
    (hr : D.recArgOf i S = some r)
    (hlen : r.binders.length ≤ t.consumeMData.piArity) :
    ∀ B ∈ r.binders, D.NoBlock B := by
  have H' := H.consumeMData
  have hscan : ∀ B ∈ posBinderDoms t.consumeMData,
      anySub (fun e => match e with
        | .const e _ => stats.indConsts.any fun I => I.constName! == e
        | _ => false) B = false := by
    intro B hB
    have := checkPositivity_binderDoms_consumeMData hchk B hB
    rwa [hasIndOcc_eq] at this
  rcases recArgOf_binders_piBinderDoms hr with hb | h0
  · have hn : S.piArity ≤ t.consumeMData.piArity := by
      rw [← VExpr.length_piBinderDoms, ← hb]; exact hlen
    have := H'.splitPis_noConsts (hasIndOcc_hpS hS) hlit hproj hctx hscan S.piArity hn
    rw [VExpr.splitPis_piArity_fst] at this
    intro B hB
    exact this B (hb ▸ hB)
  · have : t.consumeMData.piArity = 0 := Nat.le_zero.1 (h0 ▸ H'.piArity_le)
    rw [this, Nat.le_zero, List.length_eq_zero_iff] at hlen
    rw [hlen]; exact nofun



/-! ## §5 The residual arguments, and an asymmetry the binder half does not have

`PosScan` §5(b) names the args half in the same breath as the binders — *"and likewise for the
residual arguments and `r.args`"*.  It is **not** likewise, in one structural respect that has to be
stated before anything else: **binder telescopes align from the left, application spines align from
the right.**

`TrExprS.forallE` puts the new domain at the *head* of both telescopes, so index `k` means the same
thing on both sides and §2's bridge is index-preserving.  `TrExprS.app` puts the new argument at the
*tail* of both spines (`VExpr.spineArgs (.app f a) = f.spineArgs ++ [a]`), so when the source spine is
*shorter* than the target's — which §3 shows it can be — left indices are shifted by the difference
and only right indices agree.  Hence the bridge below is stated over `Expr.getAppArgsRevList` and
`VExpr.spineArgs.reverse`, both of which count from the head-most application outward.

`Verify/Inductive/Add.lean`'s `TrExprS.mem_spineArgs` is the **membership** shadow of this statement
(it is what `VIndCtor.mem_args_of_mem_getAppArgs` consumes) and carries no index; it is the safe
direction, which is why membership was enough there and is not enough here. -/

open Lean in
/-- **The spine bridge, right-anchored.**  The `k`-th argument counted from the head-most
application translates to the target's `k`-th, at the *same* `VLCtx` — no binder is crossed, so
unlike §2 there is no context extension. -/
theorem TrExprS.spineArgs_index :
    ∀ {Δ : VLCtx} {t : Expr} {S : VExpr}, TrExprS env Us Δ t S →
      ∀ (k : Nat) (a : Expr), t.getAppArgsRevList[k]? = some a →
        ∃ a', S.spineArgs.reverse[k]? = some a' ∧ TrExprS env Us Δ a a'
  | _, .app _ b, _, H, 0, a, ha => by
      let .app _ _ _ hb := H
      rw [Lean.Expr.getAppArgsRevList] at ha
      cases Option.some.inj ha
      exact ⟨_, by rw [VExpr.spineArgs, List.reverse_append]; rfl, hb⟩
  | _, .app f _, _, H, k+1, a, ha => by
      let .app _ _ hf _ := H
      rw [Lean.Expr.getAppArgsRevList, List.getElem?_cons_succ] at ha
      obtain ⟨a', ha', hTr⟩ := hf.spineArgs_index k a ha
      exact ⟨a', by rw [VExpr.spineArgs, List.reverse_append]; exact ha', hTr⟩
  | _, .bvar _, _, _, _, _, ha | _, .sort _, _, _, _, _, ha | _, .const .., _, _, _, _, ha
  | _, .fvar _, _, _, _, _, ha | _, .mvar _, _, _, _, _, ha | _, .lit _, _, _, _, _, ha
  | _, .lam .., _, _, _, _, ha | _, .forallE .., _, _, _, _, ha | _, .letE .., _, _, _, _, ha
  | _, .mdata .., _, _, _, _, ha | _, .proj .., _, _, _, _, ha => absurd ha nofun

open Lean in
/-- The spine analogue of §2's `piArity_le`, and it fails in the same direction for the same reason:
`.mdata`/`.letE`/a `vlet`-bound variable can translate to an application the source does not have. -/
theorem TrExprS.spine_length_le {Δ : VLCtx} {t : Expr} {S : VExpr} (H : TrExprS env Us Δ t S) :
    t.getAppArgsRevList.length ≤ S.spineArgs.length := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  obtain ⟨a, ha⟩ : ∃ a, t.getAppArgsRevList[S.spineArgs.length]? = some a :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨a', ha', -⟩ := H.spineArgs_index _ a ha
  have := (List.getElem?_eq_some_iff.1 ha').1
  rw [List.length_reverse] at this
  exact absurd this (Nat.lt_irrefl _)

open Lean in
/-- **The residual transfer, on the head-anchored prefix the `Expr` side can see.**  `q` positions
counted from the head-most application; §4's `hctx` discipline is unchanged, and no context extension
appears because a spine crosses no binder. -/
theorem TrExprS.spineArgs_noConsts
    (hpS : ∀ c us, c ∈ Sn → p (.const c us) = true)
    (hlit : ∀ l : Lean.Literal, anySub p l.toConstructor = false)
    (hproj : ∀ Γ s i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConsts Sn x → VExpr.NoConsts Sn y)
    {Δ : VLCtx} {t : Expr} {S : VExpr} (H : TrExprS env Us Δ t S)
    (hctx : ∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts Sn x)
    (q : Nat) (hq : q ≤ t.getAppArgsRevList.length)
    (hscan : ∀ (k : Nat) (a : Expr), k < q → t.getAppArgsRevList[k]? = some a →
      anySub p a = false) :
    ∀ (k : Nat) (a' : VExpr), k < q → S.spineArgs.reverse[k]? = some a' →
      VExpr.NoConsts Sn a' := by
  intro k a' hk hka
  obtain ⟨a, ha⟩ : ∃ a, t.getAppArgsRevList[k]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨a'', ha'', hTr⟩ := H.spineArgs_index k a ha
  cases Option.some.inj (hka.symm.trans ha'')
  exact hTr.noConsts hpS hlit hproj hctx (hscan k a hk ha)


/-! ## §6 The firing

§3's two theorems are already instances — of the *failure*.  A relation with no positive instance
proves nothing either, so here is the bridge firing at a **two**-binder field type, hypothesis-free
at every `VEnv`, with both indices live.  This is what rules out the degenerate reading of §2 (a
statement true only because its `getElem?` premise is never satisfiable). -/

namespace PosIndexWit

open Lean in
/-- **The bridge fires, twice, at every `VEnv`.**  `(A : Sort 0) → (B : Sort 0) → Sort 0` has a
two-entry stored telescope, a two-entry translated telescope, and §2 relates them at both indices. -/
theorem binderDoms_fires (env : VEnv) (nm₁ nm₂ : Name) :
    ∃ (t : Expr) (S : VExpr), TrExprS env [] [] t S ∧
      posBinderDoms t = [.sort .zero, .sort .zero] ∧
      S.piBinderDoms = [.sort .zero, .sort .zero] ∧
      t.piArity = 2 ∧ S.piArity = 2 ∧
      ∀ (k : Nat) (d : Expr), (posBinderDoms t)[k]? = some d →
        ∃ A, S.piBinderDoms[k]? = some A ∧
          TrExprS env [] (VLCtx.pushVLams (S.piBinderDoms.take k) []) d A := by
  have hs0 : ∀ Γ : List VExpr, env.IsType 0 Γ (.sort .zero) :=
    fun _ => ⟨_, .sortDF (by decide) (by decide) rfl⟩
  have hpi : ∀ Γ : List VExpr, env.IsType 0 Γ (.forallE (.sort .zero) (.sort .zero)) :=
    fun _ => ⟨_, .forallEDF (.sortDF (by decide) (by decide) rfl)
      (.sortDF (by decide) (by decide) rfl)⟩
  have H : TrExprS env [] ([] : VLCtx)
      (Expr.forallE nm₁ (.sort .zero)
        (Expr.forallE nm₂ (.sort .zero) (.sort .zero) .default) .default)
      (VExpr.forallE (.sort .zero) (VExpr.forallE (.sort .zero) (.sort .zero))) :=
    .forallE (hs0 _) (hpi _) (.sort rfl)
      (.forallE (hs0 _) (hs0 _) (.sort rfl) (.sort rfl))
  exact ⟨_, _, H, rfl, rfl, rfl, rfl, H.binderDoms⟩

end PosIndexWit

/-! ## §7 The limits, each measured or proved

**(a) The indexing correspondence is proved, and it is proved in one direction only.**  §2's
`TrExprS.binderDoms` and §5's `TrExprS.spineArgs_index` are the two halves the residue named, both
hole-free and both **unconditional**: no `VLCtx.WF`, no `VContext`, no `M.WF`, no environment
well-formedness, no R1/R2.  What they say is `Expr`→`VExpr`: *given* the `k`-th source entry, the
`k`-th target entry exists and is its translation.

**(b) The converse is false, and that is a theorem here rather than a hedge.**  §3.1
(`trExprS_piArity_lt`) separates the telescopes at every `VEnv`; §3.2
(`binders_noBlock_not_transferable`) separates part (B) itself, with `VIndRestore.recogAt` firing on
the translated type and the `Expr` scan vacuous on the stored one.  The head that does it is
`.mdata`, the cheapest of the four `TrExprS` rules that can build a target pi from a non-pi source
(`.mdata`, `.letE`, and `.bvar`/`.fvar` through a `vlet` entry).  `Verify/Inductive/Add.lean` already
records the *fact* — `Lean.Expr.piArity`'s docstring and `ElimLoopInv.spine`'s — for the constructor
telescope; what is new is the witness, and that it is at a **field**'s telescope, where nobody carries
the inequality.

**(c) So `WF.pos` follows end to end from the checker *plus one `Nat` hypothesis*, and not without
it.**  `recArgOf_binders_noBlock` (§4.2) is the composition: `checkPositivity` success + `recArgOf`'s
answer + a `TrExprS` + `r.binders.length ≤ t.consumeMData.piArity` ⟹ `∀ B ∈ r.binders, D.NoBlock B`.
§3.2 is the proof that the last hypothesis is not removable.  It is the field-level twin of
`ElimLoopInv.spine`, and the question this used to leave open — *"whether `checkConstructors` supplies
it for a field the way it supplies it for a constructor"* — **is settled, 2026-09-04, and the answer is
no**: `checkConstructors`' loop applies `isValidIndAppIdx` only to the **terminal** of the constructor
chain and to no domain, so `ElimLoopInv.spine`'s docstring is true of a constructor and silent about a
field.  What supplies §4.2 instead is the weakening to `(consumeMData t).piArity` plus
`PosReach`'s rejection theorem; see `docs/handoff-posreach.md` §2 M1 and `PosReach` §5(e) for why that
makes §4.2's truth *depend* on the rejection.

**(d) What would remove the hypothesis, and why it is not a `VExpr`-side job.**  The missing
information is on the `Expr` side: the checker's loop `whnf`s before matching, and `whnf` strips
`.mdata`, does zeta, and unfolds `let`-bound fvars.  So the `Expr`-side scan that *would* close part
(B) unconditionally is a **whnf-closed** binder-domain collector, not `posBinderDoms`.  Its
`.mdata` clause is a structural recursion and looks cheap; its `.letE` clause is not — the
whnf-faithful reading is `posBinderDoms (b.instantiate1 v)`, which is not structural, and its
`TrExprS` counterpart is a `vlet` **context** entry rather than a substitution, so the correspondence
would need a substitution lemma this file does not have.  Nothing here suggests it is false; it is
unproved and priced.

**Answered 2026-09-04** (`Verify/Inductive/BinderScan.lean`, `docs/handoff-binderscan.md`).  Three of
the four clauses above cost nothing.  The substitution lemma this file "does not have" **already
existed** — `TrExprS.inst_let` (`Verify/Typing/Lemmas.lean`:2280), whose `VExpr` side is *unchanged*,
so the `.letE` clause of the correspondence is one line and needs no `vlet`↔`ldecl` dictionary; the
`.bvar`/`.fvar`-through-a-`vlet` clause is free, because `hctx` already covers it; and `whnf`'s δ (and
β, ι, `Nat`, native) owe nothing at all, because part (B)'s conclusion is **vacuous** at every head
where `whnf` would perform one.  `BinderScan` §3 proves the unconditional statement,
`BinderScan.recArgOf_binders_noBlock_noLen` composes it, and §4.2's `hlen` survives there only as
`S.piArity = 0 → r.binders = []` — the head-β-redex branch, which `hlen` had been silently doing the
work of.  What is genuinely left is **one de Bruijn σ-composition at non-adjacent indices**
(`BinderScan` §9(d)), not a collector.

And §3.2's hypothesis was never *derivable*: `BinderScan.hlen_not_derivable` exhibits a let-bound
`.bvar` at which `checkPositivity` succeeds as a real monadic value while
`r.binders.length ≤ t.consumeMData.piArity` is false — so the plan "discharge `hlen` from `hchk`" was
impossible, and only changing what the `Expr` side certifies could work.

**(e) The args half is `likewise` only up to an asymmetry, which is §5's first paragraph.**  Binder
telescopes align from the left, application spines from the right.  §5's bridge is therefore stated
over `Expr.getAppArgsRevList` and `VExpr.spineArgs.reverse`, and `Verify/Inductive/Add.lean`'s
existing `TrExprS.mem_spineArgs` is its index-free membership shadow.  **Not** done: composing §5 into
`∀ a ∈ r.args, D.NoBlock a`.  Two things block it, and both are outside this file: `r.args` is
`sp.drop nA` at the *translated* spine while `isValidIndAppIdx`'s residual scan runs on the whnf
**reduct** `t₁`, and `PosScan` §5.4 records that `checkPositivity_loop_validApp` was never composed
into a whole-telescope residual scan.  §5 is the transfer that composition will consume.

**(f) No firing of the *composed* transfer can be hypothesis-free today, and the blocker is named.**
`TrExprS.noConsts`' third side condition `hproj` is open in `Verify/Inductive/Add.lean` (its §"From
the syntactic check to `VExpr.NoConsts`" records why: `TrProj`'s `ps`/`ιs` are pinned only up to
conversion).  So §6 fires §2's bridge, which needs none of the three, and §4.2 carries `hproj` as a
hypothesis exactly as its own source does.  That is `Add.lean`'s residue, not this file's, and it is
not a new one.

**(g) `VIndRecArg.exists_indep` is off this file's path.**  Nothing here mentions it; the reason is
the one `WFPos` §5(d) and `PosScan` §5(d) give and it is unchanged by anything above — `exists_indep`
is `VIndField.WF.binders_indep`'s obligation, and every statement here is about `NoBlock` of a
telescope entry, with no `∃` over independent binders anywhere in it.  Measured in
`docs/handoff-posindex.md` §2 with the watch list set explicitly.

## §8 Axiom checks

Every declaration this file introduces.  The prediction recorded in `docs/handoff-posindex.md` §1 S4
was that **no `Lean.Expr.eqv_eq` appears anywhere here** — the file compares nothing with `BEq Expr`;
`posBinderDoms`, `piBinderDoms`, `splitPis` and `piArity` are `match`es and `TrExprS` is an inductive.
`recArgOf_binders_noBlock` is the one result that composes with `PosScan`'s
`checkPositivity_binderDoms`, so it is the one that inherits `Lean.Expr.instantiate1_eq`. -/

#print axioms Lean4Lean.VExpr.splitPis_fst
#print axioms Lean4Lean.VExpr.length_piBinderDoms
#print axioms Lean4Lean.VExpr.splitPis_piArity_fst
#print axioms Lean4Lean.length_posBinderDoms
#print axioms Lean4Lean.VLCtx.pushVLams
#print axioms Lean4Lean.TrExprS.binderDoms
#print axioms Lean4Lean.TrExprS.piArity_le
#print axioms Lean4Lean.trExprS_piArity_lt
#print axioms Lean4Lean.prRestore_recogAt
#print axioms Lean4Lean.binders_noBlock_not_transferable
#print axioms Lean4Lean.binders_noBlock_witness_rejected
#print axioms Lean4Lean.binders_noBlock_not_transferable_unreachable
#print axioms Lean4Lean.VLCtx.noConsts_pushVLams
#print axioms Lean4Lean.VExpr.mem_splitPis
#print axioms Lean4Lean.TrExprS.splitPis_noConsts
#print axioms Lean4Lean.VExpr.betaHead_forallE
#print axioms Lean4Lean.recArgOf_binders_piBinderDoms
#print axioms Lean4Lean.recArgOf_binders_noBlock
#print axioms Lean4Lean.TrExprS.spineArgs_index
#print axioms Lean4Lean.TrExprS.spine_length_le
#print axioms Lean4Lean.TrExprS.spineArgs_noConsts
#print axioms Lean4Lean.PosIndexWit.binderDoms_fires

end Lean4Lean
