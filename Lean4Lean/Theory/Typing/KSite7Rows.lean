import Lean4Lean.Theory.Typing.KSite7App

/-!
# Site 7's last three rows, and the assembly

`KSite7App.lean`'s `site7_ledger` docstring leaves three rows of
`KSite7.ParRedKStatement` open: `appDF` × `beta`, `appDF` × `keta`, and `etaL`.  Two of the
three are closed here **with no hypothesis at all**, and the ledger's stated reason for each
being open is wrong in both cases:

* **`etaL`** was recorded as *"open; the mirror of `etaR`, and `KSite7.etaR_inner`'s invariant
  is not symmetric"*.  It needs no invariant and no inner induction: `NormalEq.etaL`'s premise
  already lives one binder in, at `.app e'.lift (.bvar 0)`, so the case's own induction
  hypothesis applies to the *weakening* of `H2` and the answer re-wraps by `ParRedKS.lam`.
  `ChurchRosser.NormalEq.parRed`'s own `etaL` case is three lines for exactly this reason; the
  only `ParRedK`-specific ingredient is `ParRedK.weakN`, which `KEta.lean` already has.
  `NormalEq.etaL_of_parRedK` below.

* **`appDF` × `beta`** was recorded as *"needs `ChurchRosser.ParRedExt.parRed_beta` ported to
  `ParRedK`"*.  **No port is needed.**  `ParRedExt.parRed_beta`'s statement mentions the old
  relation only in its *conclusion* (`Γ ⊢ f.app a ≫* e`), never as a hypothesis, and its proof
  cases only on `NormalEq`.  So it applies verbatim in the `ParRedK` world and its answer is
  weakened by `ParRedS.toK`.  `NormalEq.appDF_beta_of_parRedK` below.

That leaves **one** row, `appDF` × `keta`, and the ledger's reading of it is also wrong: it
says *"`appDF` × `keta .here` reduces to the row above; same shape, a `KStep` at the node"*.
It does not, and `AppKetaRow` below is the honest statement of what is missing, with the
reason recorded in its docstring: `ParRedK.keta` is **not** a parallel step.  Its second
premise is a development of the *contractum*, so the case needs site 7 at a term that is
neither a sub-derivation of `H1` nor of `H2`.

## The assembly

`parRedKStatement_of_rows` puts the nine rows together: site 7 holds from
**`WeakNInvDS` and `AppKetaRow`**, nothing else.  Both residuals are bounded below (each holds
where `EtaK` is empty, so neither is refutable outright) and neither is `EtaRLiftInv`, the gate
`docs/vacuity-ledger.md` row 33 names -- that gate was replaced by `WeakNInvDS` in
`KSite7.lean` and the ledger row has not caught up.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

/-! ## The `etaL` row -/

/-- **Site 7's `etaL` row, unconditionally.**  `H1 = .etaL l1 l2` relates `.lam A e` to `e'`,
and `H2` develops `e'`.  The case's induction hypothesis is at `l2`, i.e. at
`.app e'.lift (.bvar 0)` in the context `A::Γ`, and `H2` weakened one binder is a `ParRedK`
step there -- so nothing has to be inverted and no invariant has to be maintained.

Contrast `etaR`, whose induction hypothesis runs the *other* way (`.app e'.lift (.bvar 0)` on
the left) and therefore has to reconstruct a λ from a development of an η-expansion; that is
what `KSite7.etaR_inner` does and why it needs `WeakNInvDS`.  The asymmetry is real, but it
falls on `etaR`'s side, not `etaL`'s. -/
theorem NormalEq.etaL_of_parRedK {Γ : List VExpr} {A B e e' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ e' : .forallE A B)
    (ih1 : ∀ {x : VExpr}, ParRedK (A::Γ) (.app e'.lift (.bvar 0)) x →
      ∃ t, ParRedKS (A::Γ) e t ∧ NormalEq (A::Γ) t x)
    {e₂' : VExpr} (H2 : ParRedK Γ e' e₂') :
    ∃ e₁', ParRedKS Γ (.lam A e) e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' :=
  let ⟨t, a1, a2⟩ := ih1 (.app (H2.weakN .one) .bvar)
  ⟨.lam A t, ParRedKS.lam .rfl a1, .etaL (H2.hasType hΓ l1) a2⟩

/-! ## The `appDF` × `beta` row -/

/-- **Site 7's `appDF` × `beta` row, unconditionally.**  The body is
`ChurchRosser.NormalEq.parRed`'s own `beta` case with `ParRedS` replaced by `ParRedKS` at the
two reduction positions and `ParRedExt.parRed_beta` **reused verbatim**.

Why the reuse is legitimate, stated exactly: `parRed_beta`'s type is

```
Γ ⊢ f ≡ₚ .lam A e' → Γ ⊢ f.app a : B → ∃ e, Γ ⊢ f.app a ≫* e ∧ Γ ⊢ e ≡ₚ e'.inst a
```

-- the old relation occurs **only in the conclusion**, and the proof's every `cases` is on a
`NormalEq`, never on a `ParRed`.  So it is a statement about `NormalEq` that happens to
produce a development, and `ParRedS.toK` turns that development into a `ParRedK` one.  Nothing
about the enlarged relation can invalidate it: enlarging a relation only weakens an existential
conclusion. -/
theorem NormalEq.appDF_beta_of_parRedK {Γ : List VExpr} {f A B a b A₀ eb : VExpr}
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f : .forallE A B) (l2 : Γ ⊢ .lam A₀ eb : .forallE A B)
    (l3 : Γ ⊢ a : A) (l4 : Γ ⊢ b : A)
    (ih1 : ∀ {x : VExpr}, ParRedK Γ (.lam A₀ eb) x →
      ∃ e₁', ParRedKS Γ f e₁' ∧ Γ ⊢ e₁' ≡ₚ x)
    (ih2 : ∀ {x : VExpr}, ParRedK Γ b x → ∃ e₁', ParRedKS Γ a e₁' ∧ Γ ⊢ e₁' ≡ₚ x)
    {eb' b' : VExpr} (r1 : ParRedK (A₀::Γ) eb eb') (r2 : ParRedK Γ b b') :
    ∃ e₁', ParRedKS Γ (.app f a) e₁' ∧ Γ ⊢ e₁' ≡ₚ eb'.inst b' := by
  let ⟨f', a1, a2⟩ := ih1 (.lam .rfl r1)
  let ⟨a', b1, b2⟩ := ih2 r2
  let ⟨⟨_, d1⟩, _, d2⟩ := l2.lam_inv henv hΓ
  let ⟨⟨_, u1⟩, _, u2⟩ := ((d1.lam d2).uniqU henv hΓ l2).forallE_inv henv hΓ
  refine have hΓ' := (by exact ⟨hΓ, _, d1⟩); have d2 := r1.hasType hΓ' (u2.defeq d2); ?_
  replace l3 := b1.hasType hΓ (u1.symm.defeq l3)
  let ⟨_, h1, h2⟩ := ParRedExt.parRed_beta hΓ a2
    (.app (.defeqU_l henv hΓ (a2.defeq hΓ).symm (d1.lam d2)) l3)
  exact ⟨_, (ParRedKS.app a1 b1).trans h1.toK,
    h2.trans hΓ (.instN_r hΓ' l3 b2 .zero d2)⟩

/-! ## The one remaining row: `appDF` x `keta`

`KSite7App.lean`'s `site7_ledger` records this row as two sub-rows, and its reading of both is
wrong:

* *"`appDF` x `keta .here` -- reduces to the row above; same shape, a `KStep` at the node"* --
  it does not.  `NormalEq.appDF_extra_of_descendVK` closes `H2 = .extra r1 r2 r3 r4`, whose
  development `r4` acts **only on the pattern's holes**: it is a parallel step, so the
  right-hand side it lands on is `Pattern.RHS.apply m1 m2' r.1`, a term built from the same
  rule.  `ParRedK.keta`'s second premise is a development of the *whole contractum*,
  `ParRedK G w e2'` at an arbitrary `e2'`, and no instance of `r4` produces it.
* *"`appDF` x `keta .under` -- needs an inner induction like `KSite7.etaR_inner`"* -- an inner
  induction is not enough either, for the reason below.

## Why this row is not a sub-derivation of anything, stated exactly

Site 7 is proved by induction on `H1 : NormalEq G e1 e2`, generalising over `H2`.  The `keta`
case supplies `hek : EtaK G e2 w` and `htail : ParRedK G w e2'`, and the only route through it
is: transport `hek` back across `H1` to reach some `t` with `ParRedKS G (.app f a) t` and
`NormalEq G t w`, then push `htail` across **that** `NormalEq`.  The second push is site 7
again, at a `NormalEq` which is neither `H1` nor a sub-derivation of it -- so the induction
does not descend.

The mirror organisation does not work either.  `KSite7.DomEq.parRedK` -- the same commutation
for `DomEq` -- inducts on the **`ParRedK`** derivation, and its `keta` case is three lines
precisely because `htail` *is* a sub-derivation there.  Transplanting that to `NormalEq` breaks
the two eta rows instead: `NormalEq.etaL_of_parRedK` above consumes its induction hypothesis at
`H2` **weakened and applied** (`.app (H2.weakN .one) .bvar`), which is one node *larger* than
`H2`, and `KSite7.etaR_case` likewise runs `etaR_inner` over a sequence built from `H2`.  So:

| organisation | `etaL` / `etaR` | `keta` |
| --- | --- | --- |
| induct on `H1` (this file) | descends (`l2` is a sub-derivation) | **does not descend** |
| induct on `H2` (`DomEq.parRedK`) | does not descend (`H2` grows by a binder) | descends |

Neither the lexicographic order `(H1, H2)` nor `(H2, H1)` decreases in both rows, and the sum
of the two sizes is *constant* across `etaL` (H1 loses a node, H2 gains one).  A genuine
combined measure -- or a reorganisation that removes one of the two conflicts -- is what this
row costs; it is not a missing lemma.

`AppKetaRow` is that cost, named.  It is bounded both ways below: it holds wherever `EtaK` is
empty (`appKetaRow_of_no_etaK`, so it is not refutable outright, and it is *vacuous* at every
`Params` instance this tree has -- see the honesty note there), and it is implied by site 7
itself (`appKetaRow_of_parRedKStatement`), so it is not a stronger hypothesis smuggled in.
With `WeakNInvDS` in hand the two are **equivalent**, which is the exact price of site 7. -/

/-- **Site 7's `appDF` x `keta` row, as a named residual.**  The hypotheses are exactly what
the case has in hand: the six premises of `NormalEq.appDF` and the two premises of
`ParRedK.keta` at the node.  Nothing is quantified that the case does not already fix.

This covers both `EtaK` constructors (`here` = a `K`-step at the node, `under` = an eta tower
over it); splitting them buys nothing, because `here`'s obstruction -- site 7 at the
contractum -- is already the whole of it. -/
def AppKetaRow : Prop :=
  ∀ {Γ : List VExpr} {f A B f₂ a b w e₂' : VExpr},
    OnCtx Γ (IsType env univs) →
    Γ ⊢ f : .forallE A B → Γ ⊢ f₂ : .forallE A B → Γ ⊢ a : A → Γ ⊢ b : A →
    Γ ⊢ f ≡ₚ f₂ → Γ ⊢ a ≡ₚ b →
    EtaK Γ (.app f₂ b) w → ParRedK Γ w e₂' →
    ∃ e₁', ParRedKS Γ (.app f a) e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂'

/-- Lower bound, stated honestly.  Where `EtaK` is empty the row holds because its `EtaK`
premise has no witness -- so `AppKetaRow` is **not refutable outright**, and equally it is
**vacuous** at `refParams` and at every other `Params` instance in this tree, none of which
registers an `.app` pattern.  Exactly the standing of `WeakNInvDS`
(`KSite7.weakNInvDS_of_no_etaK`): a lower bound that rules out refutation and provides no
evidence of truth. -/
theorem appKetaRow_of_no_etaK (hno : ∀ {Δ a b}, ¬ EtaK Δ a b) : AppKetaRow :=
  fun _ _ _ _ _ _ _ hek _ => absurd hek hno

theorem refParams_appKetaRow : @AppKetaRow refParams :=
  @appKetaRow_of_no_etaK refParams (fun h => refParams_no_etaK h)

/-- **Upper bound: the collapse test.**  `AppKetaRow` is a *substitution instance* of site 7 --
`H1 := .appDF …`, `H2 := .keta hek htail` -- so it is no stronger than what it is used to
prove.  Together with `parRedKStatement_of_rows` below this makes site 7 and `AppKetaRow`
equivalent given `WeakNInvDS`, i.e. the factoring is exact and hides nothing. -/
theorem appKetaRow_of_parRedKStatement (S : ParRedKStatement) : AppKetaRow :=
  fun hΓ l1 l2 l3 l4 l5 l6 hek htail =>
    S hΓ (.appDF l1 l2 l3 l4 l5 l6) (.keta hek htail)

/-- **The row's argument side costs nothing: the whole residual is on the function side.**

At a `keta .here` step -- a `K⁺` step at the node -- the row is *provable outright* whenever the
two function sides are syntactically equal, i.e. whenever `NormalEq.appDF`'s function premise is
`refl`.  The reason is that `KStep` already asks only for the major premise to be
**definitionally equal** to a matching one, so the `NormalEq` on the argument side composes
straight into `KStep.mk`'s `hdq` and the same rule fires at `.app f a` on the nose.  No descent,
no `AppKetaRow`, no hypothesis.

This is `ORCHESTRATOR.md` working rule 2 run on the residual: it localises what `AppKetaRow`
is actually paying for.  Not the argument side -- there `KStep`'s defeq slack absorbs any
`NormalEq`, `proofIrrel` included, which is exactly the mechanism
`ParRedPropRefute.not_hK_of_propMajor` shows `ParRed` lacks.  What is left is the **function**
side, where `NormalEq.etaL` may present a λ against a matching spine, and the eta tower of
`EtaK.under`; those are `NormalEq.descend`'s reason for existing, restated. -/
theorem appKetaRow_here_of_same_fun {Γ : List VExpr} {f a b w e₂' : VExpr}
    (hΓ : OnCtx Γ (IsType env univs)) (l6 : Γ ⊢ a ≡ₚ b)
    (hst : KStep Γ (.app f b) w) (htail : ParRedK Γ w e₂') :
    ∃ e₁', ParRedKS Γ (.app f a) e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' := by
  cases hst with
  | @mk p₁ p₂ r _ _ c A₀ B₀ m1 m2 r1 r2 r3 hf hdq =>
    have hab : Γ ⊢ a ≡ b : A₀ := (l6.defeq hΓ).of_r henv hΓ hdq.hasType.1
    have hstep : KStep Γ (.app f a) (r.1.apply m1 m2) := .mk r1 r2 r3 hf (hab.trans hdq)
    have hseq : ParRedKS Γ (.app f a) e₂' := .tail .rfl (.keta (.here hstep) htail)
    exact ⟨e₂', hseq, .refl (ParRedKS.hasType hΓ hseq (hf.app hab.hasType.1))⟩

/-! ## The assembly -/

/-- **Site 7 for `ParRedK`, from `WeakNInvDS` and `AppKetaRow` -- and nothing else.**

This is `NormalEq.parRed`'s statement (`ChurchRosser.lean:2286`) restated over `ParRedK`.  The
verbatim statement is refuted (`ParRedPropRefute.not_parRedStatement_of_propMajor`); this is
the replacement, and the two hypotheses are its entire cost:

* `WeakNInvDS` (`KSite7.lean:954`) -- site 1 at the `DomEq` conclusion, consumed only by the
  `etaR` row.  **Not** `EtaRLiftInv`, which `KSite7.not_etaRLiftInv_of_etaK` refutes:
  `EtaRLiftInv` demands the lifting inversion *on the nose* (`f₀ = g.lift`), which the λ-domain
  witness kills, while `WeakNInvDS` asks only for a `DomEq` to a lift, and that is what the
  witness actually produces (`KEta.lean`'s `kdom_normalEq_lam`).
* `AppKetaRow` -- the `appDF` x `keta` row, above.

Row by row: `refl`, `sortDF`, `constDF`, `proofIrrel` are `DomEq` and go through
`KSite7.parRedKStatement_of_domEq`; `lamDF`, `forallEDF`, `appDF` x congruence and
`appDF` x `extra` are `KSite7App.lean`, unconditional; `appDF` x `beta` and `etaL` are this
file, unconditional; `etaR` is `KSite7.etaR_case` against `WeakNInvDS`; `appDF` x `keta` is
`AppKetaRow`. -/
theorem parRedKStatement_of_rows (HD : WeakNInvDS) (HA : AppKetaRow) : ParRedKStatement := by
  suffices H : ∀ {Γ : List VExpr} {e₁ e₂ : VExpr}, NormalEq Γ e₁ e₂ →
      OnCtx Γ (IsType env univs) → ∀ {e₂' : VExpr}, ParRedK Γ e₂ e₂' →
      ∃ e₁', ParRedKS Γ e₁ e₁' ∧ Γ ⊢ e₁' ≡ₚ e₂' from
    fun _ _ _ _ hΓ H1 H2 => H H1 hΓ H2
  intro Γ e₁ e₂ H1
  induction H1 with
  | refl l1 => exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.refl l1) H2
  | sortDF l1 l2 l3 =>
    exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.sortDF l1 l2 l3) H2
  | constDF l1 l2 l3 l4 l5 =>
    exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.constDF l1 l2 l3 l4 l5) H2
  | proofIrrel l1 l2 l3 =>
    exact fun hΓ _ H2 => parRedKStatement_of_domEq hΓ (.proofIrrel l1 l2 l3) H2
  | appDF l1 l2 l3 l4 l5 l6 ih1 ih2 =>
    intro hΓ e₂' H2
    cases H2 with
    | app r1 r2 =>
      exact NormalEq.appDF_app_of_parRedK hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 hΓ) r1 r2
    | beta r1 r2 =>
      exact NormalEq.appDF_beta_of_parRedK hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 hΓ) r1 r2
    | extra r1 r2 r3 r4 =>
      exact NormalEq.appDF_extra_of_descendVK hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 hΓ) r1 r2 r3 r4
    | keta hek htail => exact HA hΓ l1 l2 l3 l4 l5 l6 hek htail
  | lamDF l1 l2 l3 ih1 =>
    exact fun hΓ _ H2 =>
      NormalEq.lamDF_of_parRedK hΓ l1 l2 l3 (ih1 ⟨hΓ, _, l1.hasType.1⟩) H2
  | forallEDF l1 l2 l3 l4 ih1 ih2 =>
    exact fun hΓ _ H2 =>
      NormalEq.forallEDF_of_parRedK hΓ l1 l2 l3 l4 (ih1 hΓ) (ih2 ⟨hΓ, _, l1.hasType.1⟩) H2
  | etaL l1 l2 ih1 =>
    intro hΓ e₂' H2
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    exact NormalEq.etaL_of_parRedK hΓ l1 (ih1 ⟨hΓ, _, hA⟩) H2
  | etaR l1 l2 ih1 =>
    intro hΓ e₂' H2
    have ⟨⟨_, hA⟩, _, hB⟩ := have ⟨_, h⟩ := l1.isType henv hΓ; h.forallE_inv henv
    cases H2 with
    | lam r1 r2 => exact etaR_case HD hΓ l1 l2 (ih1 ⟨hΓ, _, hA⟩) r1 r2
    | extra _ r2 => cases r2
    | keta hek _ => exact absurd hek EtaK.not_lam

/-! ## Measurement: the hole cone of the restatement

Measured with `scripts/hole-cone.lean`'s `deps` walk (`allowOpaque := true`) over the closure of
`KSite7Rows` + `ParRedPropRefute`, 2026-08-31.

| seed | cone | holes |
| --- | --- | --- |
| `ChurchRosser.NormalEq.parRed` | 4098 | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, **`NormalEq.descend`** |
| `parRedKStatement_of_rows` | 4239 | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS` |

**The restatement's cone does not contain `NormalEq.descend`.**  That is the measurable content
of this file: `DescendRefute.lean`'s `not_descendStatement` refutes `descend` at a `Params`
instance that *exists* (`refParams` over `refEnv`, given `SortUniq` and `UniqTyping` there), so
`ChurchRosser.NormalEq.parRed` depends on a statement known false at a real instance, and
`parRedKStatement_of_rows` does not depend on it at all.  `AppKetaRow` and `WeakNInvDS` are
refutable only at instances that do not exist yet -- strictly better standing.

Row by row, which rows carry `IsDefEqU.weakN_iff`:

* **clean (7 of 9):** `parRedKStatement_of_domEq` (the four `DomEq` rows),
  `NormalEq.appDF_app_of_parRedK`, `NormalEq.appDF_extra_of_descendVK`,
  `NormalEq.lamDF_of_parRedK`, `NormalEq.forallEDF_of_parRedK`, `NormalEq.etaL_of_parRedK`.
* **not clean (2):** `NormalEq.appDF_beta_of_parRedK` (through `ParRedExt.parRed_beta`) and
  `KSite7.etaR_case`, both by the single path `… → NormalEq.trans → NormalEq.weakN_iff →
  NormalEq.weakN_inv_DFC → IsDefEqU.weakN_iff`.

`KSite7App.lean`'s own measurement note is **stale on one row**: it records
`NormalEq.appDF_extra_of_descendVK` as *not* clean of `weakN_iff`.  It is clean now --
`ChurchRosser.lean`'s `NormalEq.instN₂` / `NormalEq.apply_congr` removed the entry from the
descent layer after that note was written.  So `NormalEq.trans` is the *only* remaining entry
into site 7, through exactly two rows, and `NormalEq.trans`'s own residual is its `etaR`-after-
`etaL` case (`ChurchRosser.lean`'s `weakN_inv_one_of_inhabited` bounds it to uninhabited
binders).  Discharging `WeakNInvDS` would bring `ParRed.weakN_inv`'s `extra` case back as a
third entry, as `KSite7App.lean` says. -/

/-- The `refParams` consistency check for the assembled statement: both hypotheses hold there
(vacuously), and the conclusion agrees with `KSite7.refParams_parRedKStatement`, which reaches
it by the independent route `ParRedK.toParRed` + `ChurchRosser.NormalEq.parRed`. -/
theorem refParams_parRedKStatement_of_rows : @ParRedKStatement refParams :=
  @parRedKStatement_of_rows refParams refParams_weakNInvDS refParams_appKetaRow

end VEnv
end Lean4Lean
