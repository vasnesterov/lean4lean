import Lean4Lean.Theory.Typing.NormalEqStrengthen
import Lean4Lean.Theory.Typing.WeakNProjGate

/-!
# `PiDescend`, split into Π-shape recovery and type pinning

`VEnv.PiDescend` (`Theory/Typing/Strengthen.lean:370`) is the typing half of
`VEnv.IsDefEqU.weakN_iff` (`TypingStrengthening.iff_piDescend`), and by
`docs/handoff-weakn.md` §7 it is exactly what frees the projection corner once
`Verify/Typing/ProjSkip.lean`'s four gate call sites are rewired.  Round 8's assignment was to
attack it.  It is **not** proved here.  What is here is a decomposition that makes the
remaining obligation one statement rather than two, and a correction to what the previous
rounds said that obligation is.

## The statement, and what its two conjuncts are

```
PiDescend : Ctx.LiftN n k Γ Γ' → OnCtx Γ → OnCtx Γ' →
  Γ' ⊢ f↑ : ∀A.B → Γ' ⊢ a↑ : A → VExpr.WF Γ f → VExpr.WF Γ a →
  ∃ A₀ B₀, Γ ⊢ f : ∀A₀.B₀ ∧ Γ ⊢ a : A₀
```

Its conclusion is a conjunction and the two halves are different problems:

* **Π-shape recovery** (`PiDescendFst`, §1): find *some* Π type for `f` downstairs.  `f`'s
  downstairs type `T` exists by `VExpr.WF Γ f`, and upstairs `T↑ ≡ ∀A.B`; the obligation is to
  turn that into `T ≡ ∀A₀.B₀` **downstairs**, where the right-hand side is *not* in the image
  of the lift.  `NormalEqStrengthen.lean:161`'s correction note already identifies this as the
  gap; §1 gives it a name and shows it is the *whole* gap.
* **Type pinning** (`ArgPin`, §2): `a`'s own downstairs type `S` need not be `A₀`, and
  reconciling them is a conversion `Γ ⊢ S ≡ A₀` whose only witness lives upstairs, routed
  through the non-lift `A`.

## The result, in one line

**`PiDescend ↔ PiDescendFst ∧ SortConvStrengthening`** (§3, `piDescend_iff_fst_sortConv`), and
`ArgPin` is inter-derivable with `SortConvStrengthening` modulo `SortDescend` (§2).

## The correction this makes to `docs/handoff-weakn.md` §A.6(4)

That entry says `PiDescend`

> "is now known to need *conversion* strengthening too, not just typing strengthening: its
> second conjunct asks for `Γ ⊢ a : A₀` with `A₀` **f's** domain, and reconciling `a`'s own
> downstairs type with `A₀` is `TransStrengthening`."

The diagnosis is right and the price is wrong.  Both `S` and `A₀` are **types**, so the
conversion needed is `Γ' ⊢ S↑ ≡ A₀↑ : .sort v` -- a *sort-typed* conversion between two lifts,
i.e. an instance of `SortConvStrengthening` (`NormalEqStrengthen.lean:95`), not of
`TransStrengthening`.  And round 6 §6.2 proved `SortConvStrengthening` is a **consequence** of
the typing half (`SortConvStrengthening.of_piDescend`), so it is not an extra unknown: the
whole residual is the Π-shape recovery.  §3's `iff` says exactly that.

## Why the split does not collapse (working rule 5), and the obstruction named

The `iff` would be decoration if `PiDescendFst` alone gave `SortConvStrengthening`.  It does
not, and the reason is sharp: `SortConvStrengthening`'s proof from the typing half
(`SortConvStrengthening.of_typing`) needs `Γ ⊢ .lam A₂ (.bvar 0) : .forallE A₁ A₁.lift` -- the
Π type **pinned to `A₁`**, which is what makes `uniqU` against the term's natural type
`.forallE A₂ A₂.lift` produce `A₂ ≡ A₁`.  `PiDescendFst` returns an **unpinned** `∃ A₀ B₀`, and
`ArgPin`, which does the pinning, is (§2) the same statement as `SortConvStrengthening`.  So:

> **The obstruction is that Π-shape recovery is existential and type pinning is not, and the
> ascription redex that would convert one into the other needs its own conclusion as an input.**

§4 records that circle as a theorem-shaped observation rather than a claim: `ArgPin` at a
`.lam A₀ (.bvar 0)` subject is *equivalent* to its own instance at `a` (`argPin_ascription_circle`).

Nothing here closes the hole, nothing here removes a `sorry`, and every result below is
conditional on an open hypothesis.  §5 shows the hypotheses are inhabited; §6 has the controls.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## 1. `PiDescendFst`: the first conjunct alone

Same premises as `PiDescend`, conclusion truncated to the Π typing for `f`.  Keeping *all* the
premises -- including the argument `a` and `VExpr.WF Γ a` -- is deliberate: it makes
`PiDescend → PiDescendFst` a projection, so `PiDescendFst` is provably no stronger than
`PiDescend`.  (A version without `a` would be a *different*, possibly strictly stronger,
statement -- that is `KEta.lean:847`'s `PiTypeDescend`, and there is no route from `PiDescend`
to it: `A` need not be inhabited, so no argument can be manufactured.) -/

/-- **`PiDescend`'s first conjunct.**  Π-shape recovery for the function. -/
def PiDescendFst (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {f a A B : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ' (f.liftN n k) (.forallE A B) → env.HasType U Γ' (a.liftN n k) A →
    VExpr.WF env U Γ f → VExpr.WF env U Γ a →
    ∃ A₀ B₀, env.HasType U Γ f (.forallE A₀ B₀)

/-- Projection: the first conjunct is no stronger than the whole. -/
theorem PiDescend.fst (HP : PiDescend env U) : PiDescendFst env U := fun W hΓ hΓ' hf ha wf1 wf2 =>
  let ⟨A₀, B₀, h, _⟩ := HP W hΓ hΓ' hf ha wf1 wf2; ⟨A₀, B₀, h⟩

/-! ## 2. `ArgPin`: the second conjunct, and it is `SortConvStrengthening`

`ArgPin` is "a lifted subject already typed downstairs, whose upstairs type is a lift, may be
retyped at that lift's base".  It is `TypingStrengthening.typed`'s conclusion with the
*existence* of a downstairs typing handed over rather than produced -- which is exactly the
situation `PiDescend`'s second conjunct is in, because `VExpr.WF Γ a` is one of its premises.

The `IsType Γ A₀` premise is free at the call site (`A₀` is the domain of a Π that types `f`
downstairs, so `HasType.forallE_inv` supplies it) and is what makes §2b's converse go. -/

/-- **The second conjunct, isolated.**  Type pinning for a lifted subject at a lifted type. -/
def ArgPin (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {a S A₀ : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ a S → env.IsType U Γ A₀ →
    env.HasType U Γ' (a.liftN n k) (A₀.liftN n k) →
    env.HasType U Γ a A₀

/-- **`SortConvStrengthening` with the two endpoints already known typeable downstairs.**  This
is the form §2b can deliver and the only form §3 consumes: at both call sites the endpoints are
`a`'s own downstairs type and the domain of a Π that types `f`, so both are `IsType Γ _`.  The
premises are exactly what `SortDescend` presupposes and cannot produce -- the asymmetry
`docs/handoff-weakn.md` §7.7 records. -/
def SortConvStrengtheningWF (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr} {u : VLevel}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.IsType U Γ e1 → env.IsType U Γ e2 →
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (.sort u) → env.IsDefEqU U Γ e1 e2

/-- The unrestricted form implies the restricted one; nothing below needs more. -/
theorem SortConvStrengthening.wf (HS : SortConvStrengthening env U) :
    SortConvStrengtheningWF env U := fun W hG hG' _ _ h => HS W hG hG' h

variable! (henv : VEnv.WF env) in
/-- **§2a: sort-typed conversion strengthening pins types.**  `a`'s two upstairs types are both
lifts and both types, so `uniqU` gives a conversion between them, retypeable at a sort; that is
exactly one instance of `SortConvStrengtheningWF`. -/
theorem ArgPin.of_sortConvWF (HS : SortConvStrengtheningWF env U) : ArgPin env U := by
  intro n k Γ Γ' a S A₀ W hΓ hΓ' haS hA₀ haA₀
  have hSty : env.IsType U Γ S := haS.isType henv.ordered hΓ
  have ⟨v, hSv⟩ := hSty
  have hSv' : env.HasType U Γ' (S.liftN n k) (.sort v) := hSv.weakN henv.ordered W
  have haS' : env.HasType U Γ' (a.liftN n k) (S.liftN n k) := haS.weakN henv.ordered W
  obtain ⟨T, hT⟩ : env.IsDefEqU U Γ' (S.liftN n k) (A₀.liftN n k) := haS'.uniqU henv hΓ' haA₀
  have hTv : env.IsDefEqU U Γ' T (.sort v) := hT.hasType.1.uniqU henv hΓ' hSv'
  have hconv : env.IsDefEq U Γ' (S.liftN n k) (A₀.liftN n k) (.sort v) :=
    IsDefEqU.defeqDF henv hΓ' hTv hT
  exact haS.defeqU_r henv hΓ (HS W hΓ hΓ' hSty hA₀ hconv)

variable! (henv : VEnv.WF env) in
/-- …and off the unrestricted form, which is what the tree states. -/
theorem ArgPin.of_sortConv (HS : SortConvStrengthening env U) : ArgPin env U :=
  ArgPin.of_sortConvWF henv HS.wf

variable! (henv : VEnv.WF env) in
/-- **§2b: the converse.**  Given `Γ' ⊢ A₂↑ ≡ A₁↑ : .sort u` with both endpoints typeable
downstairs, the identity function on `A₂` may be retyped upstairs at `A₁ → A₁` -- both a lift --
so `ArgPin` hands back `Γ ⊢ .lam A₂ (.bvar 0) : .forallE A₁ A₁.lift` **downstairs, with the type
pinned**, and `uniqU` against its natural type plus Π-injectivity recovers `A₂ ≡ A₁`.

This is `SortConvStrengthening.of_typing`'s proof with `TypingStrengthening.hasType_inv`
replaced by `ArgPin` -- the only appeal that proof makes to the typing half. -/
theorem SortConvStrengtheningWF.of_argPin (HA : ArgPin env U) :
    SortConvStrengtheningWF env U := by
  intro n k Γ Γ' A₂ A₁ u W hΓ hΓ' hA₂d hA₁d h
  have hA₂' : env.HasType U Γ' (A₂.liftN n k) (.sort u) := h.hasType.1
  have hlam : env.HasType U Γ' (.lam (A₂.liftN n k) (.bvar 0))
      (.forallE (A₂.liftN n k) ((A₂.liftN n k).lift)) := .lamDF hA₂' (.bvar .zero)
  have hpi : env.IsDefEq U Γ' (.forallE (A₂.liftN n k) ((A₂.liftN n k).lift))
      (.forallE (A₁.liftN n k) ((A₁.liftN n k).lift)) (.sort (.imax u u)) :=
    .forallEDF h (h.weakN henv .one)
  have hid : env.HasType U Γ' ((VExpr.lam A₂ (.bvar 0)).liftN n k)
      ((VExpr.forallE A₁ A₁.lift).liftN n k) := by
    rw [VExpr.liftN_lam_bvar0, VExpr.liftN_forallE_self_lift]; exact .defeqDF hpi hlam
  have ⟨u₂, hA₂⟩ := hA₂d
  have ⟨u₁, hA₁⟩ := hA₁d
  have hnat : env.HasType U Γ (.lam A₂ (.bvar 0)) (.forallE A₂ A₂.lift) :=
    .lamDF hA₂ (.bvar .zero)
  have hA₁ty : env.IsType U Γ (VExpr.forallE A₁ A₁.lift) :=
    ⟨_, .forallEDF hA₁ (hA₁.weakN henv .one)⟩
  have hnatWF : env.IsType U Γ (VExpr.forallE A₂ A₂.lift) :=
    ⟨_, .forallEDF hA₂ (hA₂.weakN henv .one)⟩
  have hpin : env.HasType U Γ (.lam A₂ (.bvar 0)) (.forallE A₁ A₁.lift) :=
    HA W hΓ hΓ' hnat hA₁ty hid
  have ⟨_, hdom⟩ := ((hnat.uniqU henv hΓ hpin).forallE_inv henv hΓ).1
  exact ⟨_, hdom⟩

variable! (henv : VEnv.WF env) in
/-- **The second conjunct, named twice.**  Type pinning and sort-typed conversion strengthening
(at endpoints already typeable downstairs) are the *same statement*. -/
theorem sortConvWF_iff_argPin : SortConvStrengtheningWF env U ↔ ArgPin env U :=
  ⟨ArgPin.of_sortConvWF henv, SortConvStrengtheningWF.of_argPin henv⟩

/-! ## 3. The decomposition

`PiDescend ↔ PiDescendFst ∧ SortConvStrengthening`.  The `←` direction is this file's content;
`→` is the projection of §1 together with `SortConvStrengthening.of_piDescend`
(`NormalEqStrengthen.lean:166`, already in the tree). -/

variable! (henv : VEnv.WF env) in
/-- **The content: `PiDescend`'s second conjunct is free given sort-typed conversion
strengthening.** -/
theorem PiDescend.of_fst_argPin (H1 : PiDescendFst env U) (H2 : ArgPin env U) :
    PiDescend env U := by
  intro n k Γ Γ' f a A B W hΓ hΓ' hf ha wff wfa
  obtain ⟨A₀, B₀, hf₀⟩ := H1 W hΓ hΓ' hf ha wff wfa
  refine ⟨A₀, B₀, hf₀, ?_⟩
  -- `a` has *some* type downstairs
  obtain ⟨S, hS⟩ := wfa
  have haS : env.HasType U Γ a S := hS.hasType.1
  -- `A₀` is a type downstairs, being the domain of a Π that types `f`
  have hA₀ : env.IsType U Γ A₀ :=
    have ⟨_, hpi0⟩ := hf₀.isType henv.ordered hΓ
    (hpi0.forallE_inv henv.ordered).1
  -- upstairs, `f↑`'s two types are convertible, hence their domains are
  have hfw : env.HasType U Γ' (f.liftN n k) ((VExpr.forallE A₀ B₀).liftN n k) :=
    hf₀.weakN henv.ordered W
  have hpi : env.IsDefEqU U Γ' ((VExpr.forallE A₀ B₀).liftN n k) (.forallE A B) :=
    hfw.uniqU henv hΓ' hf
  have ⟨⟨_, hdom⟩, _⟩ := (show env.IsDefEqU U Γ'
      (VExpr.forallE (A₀.liftN n k) (B₀.liftN n (k+1))) (.forallE A B) from hpi).forallE_inv
      henv hΓ'
  -- so `a↑ : A₀↑`, whose subject and type are both lifts: `ArgPin` pins it
  have haA₀ : env.HasType U Γ' (a.liftN n k) (A₀.liftN n k) :=
    ha.defeqU_r henv hΓ' ⟨_, hdom.symm⟩
  exact H2 W hΓ hΓ' haS hA₀ haA₀

variable! (henv : VEnv.WF env) in
/-- The same off `SortConvStrengthening`, which is the form `NormalEqStrengthen.lean` states. -/
theorem PiDescend.of_fst_sortConv (H1 : PiDescendFst env U) (H2 : SortConvStrengthening env U) :
    PiDescend env U := PiDescend.of_fst_argPin henv H1 (ArgPin.of_sortConv henv H2)

variable! (henv : VEnv.WF env) in
/-- **The decomposition, as an `iff`.**  Neither conjunct is a restatement of `PiDescend`:
`PiDescendFst` truncates the conclusion, and `SortConvStrengthening` is a *consequence* of the
typing half by round 6 §6.2, so the `iff` says the whole residual of `PiDescend` beyond its own
sort fragment is Π-shape recovery. -/
theorem piDescend_iff_fst_sortConv :
    PiDescend env U ↔ PiDescendFst env U ∧ SortConvStrengthening env U :=
  ⟨fun HP => ⟨PiDescend.fst HP, SortConvStrengthening.of_piDescend henv HP⟩,
   fun ⟨h1, h2⟩ => PiDescend.of_fst_sortConv henv h1 h2⟩

variable! (henv : VEnv.WF env) in
/-- …and with `ArgPin` in place of the conversion form.  `SortDescend` is free on the right
(`PiDescend.sortDescend`), so this is an `iff` too. -/
theorem piDescend_iff_fst_argPin :
    PiDescend env U ↔ PiDescendFst env U ∧ SortDescend env U ∧ ArgPin env U :=
  ⟨fun HP => ⟨PiDescend.fst HP, PiDescend.sortDescend henv HP,
      ArgPin.of_sortConv henv (SortConvStrengthening.of_piDescend henv HP)⟩,
   fun ⟨h1, _, h3⟩ => PiDescend.of_fst_argPin henv h1 h3⟩

/-! ## 4. The circle, recorded as a theorem rather than as a claim

`§3`'s two conjuncts do not visibly reduce to one.  The move that would do it is the ascription
redex of `Strengthen.lean` §3: to pin `a`'s type at `A₀`, type the redex
`.app (.lam A₀ (.bvar 0)) a` downstairs and invert it.  `PiDescendFst` *can* be applied to that
redex -- its function is a λ, whose Π type is built downstairs -- but what it returns is the
function's type, which was already known, and the argument's typing at `A₀`, which is the
conclusion sought.

Below is that circle as a statement: `ArgPin` restricted to a `.lam A₀ (.bvar 0)` subject
follows from `ArgPin` at the argument, and conversely -- i.e. the redex carries no information
that the argument's own instance does not. -/

variable! (henv : VEnv.WF env) in
/-- **The ascription redex is information-free for type pinning.**  Typing
`.lam A₀ (.bvar 0)` at `.forallE A₀ A₀.lift` downstairs needs only `IsType Γ A₀`, which is
already `ArgPin`'s premise -- so the redex route hands back a hypothesis, not a conclusion.
This is the exact analogue of `NormalEqStrengthen.lean` §4's `sortConv_encoding_vacuous`, one
level up. -/
theorem argPin_ascription_circle {Γ : List VExpr} {A₀ : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hA₀ : env.IsType U Γ A₀) :
    env.HasType U Γ (.lam A₀ (.bvar 0)) (.forallE A₀ A₀.lift) ∧
      ∀ a : VExpr, env.HasType U Γ a A₀ ↔
        env.HasType U Γ (.app (.lam A₀ (.bvar 0)) a) A₀ := by
  have ⟨u, hu⟩ := hA₀
  refine ⟨.lamDF hu (.bvar .zero), fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hlam0 : env.HasType U Γ (.lam A₀ (.bvar 0)) (.forallE A₀ A₀.lift) :=
      .lamDF hu (.bvar .zero)
    have := hlam0.app h
    rwa [VExpr.inst_lift] at this
  · have ⟨_, _, hf, hax⟩ := h.app_inv henv hΓ
    have hnat : env.HasType U Γ (.lam A₀ (.bvar 0)) (.forallE A₀ A₀.lift) :=
      .lamDF hu (.bvar .zero)
    have ⟨⟨_, hd⟩, _⟩ := (hnat.uniqU henv hΓ hf).forallE_inv henv hΓ
    exact hax.defeqU_r henv hΓ ⟨_, hd.symm⟩

/-! ## 5. Anti-vacuity: every hypothesis above is inhabited

`docs/vacuity-ledger.md` §0.  `WeakNProjGate.exists_typingStrengthening_env` supplies a
`VEnv.WF` environment satisfying `TypingStrengthening` at every `U`; `PiDescend`,
`PiDescendFst`, `SortDescend`, `ArgPin` and `SortConvStrengthening` all follow there.

**Read the scope statement with it** (`docs/handoff-weakn.md` §3): that environment declares
`univInhab : ∀ (α : Sort u), α`, so it is inconsistent and has no uninhabited context entry --
precisely the case `Strengthen.lean` §1 already closes.  It is a *satisfiability* witness, not
evidence that any hypothesis here is easy. -/

/-- **All five hypotheses are jointly satisfiable at a `VEnv.WF` environment, for every `U`.** -/
theorem exists_env_piDescendFst_argPin :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ U,
      PiDescend env U ∧ PiDescendFst env U ∧ SortDescend env U ∧
        ArgPin env U ∧ SortConvStrengthening env U := by
  obtain ⟨env, hwf, h⟩ := exists_typingStrengthening_env
  refine ⟨env, hwf, fun U => ?_⟩
  have hp : PiDescend env U := TypingStrengthening.piDescend hwf (h U)
  have hsc : SortConvStrengthening env U := SortConvStrengthening.of_piDescend hwf hp
  exact ⟨hp, PiDescend.fst hp, PiDescend.sortDescend hwf hp, ArgPin.of_sortConv hwf hsc, hsc⟩

/-- …and there the decomposition fires with **nothing** left over: the `iff` of §3 is not
conditional on an unsatisfiable hypothesis. -/
theorem exists_env_piDescend_iff :
    ∃ env : VEnv, VEnv.WF env ∧ ∀ U,
      (PiDescend env U ↔ PiDescendFst env U ∧ SortConvStrengthening env U) := by
  obtain ⟨env, hwf, _⟩ := exists_typingStrengthening_env
  exact ⟨env, hwf, fun _ => piDescend_iff_fst_sortConv hwf⟩

/-! ## 6. Negative controls

Three.  (a) and (b) show the two conjuncts are *restrictions* rather than repackagings; (c) is
the `vacuous_at_zero` discipline of `docs/handoff-weakn.md` §5.1. -/

/-- **(a) `ArgPin`'s "type is a lift" premise is proper.**  A Π type is never in the image of
`liftN` *as a `.sort`*, and more usefully: `.forallE A B` with `B` mentioning the top variable
is not a lift at all when `A` is not.  The concrete control: `.bvar 0` is not `X.liftN 1 0` for
any `X`, so at `n = 1, k = 0` there are upstairs types to which `ArgPin` does not apply -- it
is not the (false) claim that every upstairs typing descends. -/
theorem argPin_type_restriction (X : VExpr) : VExpr.bvar 0 ≠ X.liftN 1 0 :=
  bvar0_not_liftN_one X

/-- **(b) `PiDescendFst` is a strict truncation, not a reformulation.**  Its conclusion does not
mention `a` at all, so it cannot be `PiDescend`: `PiDescend`'s conclusion determines a typing
for `a`, and `PiDescendFst`'s is satisfied by data that says nothing about `a`.  Stated as the
implication that *is* free plus the observation that the reverse needs `ArgPin` (§3), the
content is: the two differ by exactly `ArgPin`. -/
theorem piDescendFst_forgets_arg (HP : PiDescend env U) :
    PiDescendFst env U ∧ ∀ {n k : Nat} {Γ Γ' : List VExpr} {f a A B : VExpr},
      Ctx.LiftN n k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
      env.HasType U Γ' (f.liftN n k) (.forallE A B) → env.HasType U Γ' (a.liftN n k) A →
      VExpr.WF env U Γ f → VExpr.WF env U Γ a →
      ∃ A₀ B₀, env.HasType U Γ f (.forallE A₀ B₀) ∧ env.HasType U Γ a A₀ :=
  ⟨PiDescend.fst HP, fun W hΓ hΓ' hf ha w1 w2 => HP W hΓ hΓ' hf ha w1 w2⟩

/-- **(c) At `n = 0` everything above is vacuous.**  A `Ctx.LiftN 0 k` is the identity on
contexts, so `PiDescendFst`'s and `ArgPin`'s conclusions *are* their premises: all content
lives at `n ≥ 1`. -/
theorem argPin_at_zero {k : Nat} {Γ Γ' : List VExpr} {a A₀ : VExpr}
    (W : Ctx.LiftN 0 k Γ Γ') (haA₀ : env.HasType U Γ' (a.liftN 0 k) (A₀.liftN 0 k)) :
    env.HasType U Γ a A₀ := by
  cases liftN_zero_ctx_eq W; rwa [VExpr.liftN_zero, VExpr.liftN_zero] at haA₀

/-- The same for `PiDescendFst`: at `n = 0` the Π typing is the premise. -/
theorem piDescendFst_at_zero {k : Nat} {Γ Γ' : List VExpr} {f A B : VExpr}
    (W : Ctx.LiftN 0 k Γ Γ') (hf : env.HasType U Γ' (f.liftN 0 k) (.forallE A B)) :
    ∃ A₀ B₀, env.HasType U Γ f (.forallE A₀ B₀) := by
  cases liftN_zero_ctx_eq W; rw [VExpr.liftN_zero] at hf; exact ⟨_, _, hf⟩

end VEnv
end Lean4Lean
