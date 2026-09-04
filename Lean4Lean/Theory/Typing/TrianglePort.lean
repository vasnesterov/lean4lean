import Lean4Lean.Theory.Typing.CParRedK

/-!
# The `ParRedKn` triangle: the ledger completed, and the port run

Round 2 of the `CParRedK` stream, 2026-09-04, at HEAD `3aca413` (bare `lake build` verified green
there first: 1662 jobs, exit 0).  `docs/handoff-cparredk.md` §8-§12 carries the priors,
measurements, verdicts and limits; this file carries the Lean.

`CParRedK.lean` (Round 1) built the graded complete development `CParRedKn`, proved
`CParRedKn.exists` unconditionally, and reduced `CRStatementK` to `ParRedKnTriangle`.  It then
tabulated the triangle's *new* rows as "nine, of which six closed and two open", and left the
other "sixty-four" as an unrun port of `ChurchRosser.ParRed.triangle`.

**Both halves of that accounting are corrected here, and the correction is measured.**
-/

namespace Lean4Lean

open VExpr

namespace VEnv

variable [Params]
open Params

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

/-! ## §1 The triangle at one grade, and at one subject -/

/-- `ParRedKnTriangle` at a single grade.  Splitting the grade out is not cosmetic: the outer
induction of the port is a *strong* induction on it, because `keta` on either side drops the
grade by one while every other constructor keeps it. -/
def TriangleAt (m : Nat) : Prop :=
  ∀ {n : Nat} {Γ : List VExpr} {e e' o A : VExpr}, n ≤ m →
    OnCtx Γ (IsType env univs) → Γ ⊢ e : A →
    ParRedKn n Γ e e' → CParRedKn m Γ e o → ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ o

/-- The same at one fixed subject.  This is exactly what `VExpr.brecOn`'s below-structure
supplies for a proper subterm, written as a `Prop` so that a residual can *carry* it instead of
silently omitting it (method rule 3). -/
def TriangleAtOn (m : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∀ {n : Nat} {e' o A : VExpr}, n ≤ m → OnCtx Γ (IsType env univs) → Γ ⊢ e : A →
    ParRedKn n Γ e e' → CParRedKn m Γ e o → ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ o

theorem parRedKnTriangle_of_at (H : ∀ m, TriangleAt m) : ParRedKnTriangle :=
  fun hnm hΓ he h1 h2 => H _ hnm hΓ he h1 h2

theorem TriangleAt.on {m : Nat} (H : TriangleAt m) {Γ : List VExpr} {e : VExpr} :
    TriangleAtOn m Γ e := fun hnm hΓ he h1 h2 => H hnm hΓ he h1 h2

/-! ## §2 The row count, and the axis Round 1 missed

The triangle's table is `CParRedKn`'s constructors (**ten**: Round 1 added `zero` and `keta` to
`CParRed`'s eight) against `ParRedKn`'s (**nine**: adds `keta`), so **ninety** rows, of which
`ChurchRosser.ParRed.triangle` proves `8 x 8 = 64`.  The twenty-six new rows split as

| block | rows | where |
|---|---|---|
| dev = `keta` x the eight old steps | 8 | `CParRedK.keta_root_row` (Round 1) |
| dev = `zero` x the eight old steps | 8 | `zero_dev_row`, below -- four lines |
| step = `keta` x all ten developments | 10 | `keta_step_row`, below |
| the old table | 64 | the port, §3 |

`8 + 8 + 10 + 64 = 90`, and the `keta` x `keta` corner is counted once (in the third block).

Round 1's ledger covers the **first** block only, and its prose ("nine rows where `keta` is the
development's root step ... the other sixty-four are `ParRed.triangle`'s, verbatim modulo the
grade") omits the third.  A `keta` step against a development that is *not* `keta` is a genuinely
different row: the development has not fired the K-redex, so there is no second contractum to
compare and `KetaDevAgree` does not apply.  Seven of those ten are vacuous by shape lemmas
already in `CParRedK.lean`, two are Round 1's own, and **one is new and open** -- dev = `extra`,
the only development constructor carrying neither a `¬ NonNeutralK` guard nor an excluding shape
lemma. -/

/-- **The development fires a pattern rule while the step fires `keta` at the same node.**

The mirror image of Round 1's `KetaExtraRow`, and a row Round 1's ledger does not contain.  It is
`KDiamond`-shaped in the same sense: two rules fire at one node, one of them through `KStep`'s
*converted* major premise, and `Pattern.matches_inter` cannot relate them, because the registered
pattern behind an `EtaK.here` matches `.app f c` and **not** the subject `.app f h`.

Unlike Round 1's two open rows this one **carries the induction hypotheses that its neighbours
carry** (method rule 3): the strong grade IH below `m`, which is what `keta_keta_row` needs, and
the triangle at grade `m` on each matched argument, which is what the `brecOn` below-structure
supplies at that point of the port.  Carrying them makes the residual strictly weaker, hence
strictly easier to discharge, than the same row stated bare. -/
def ExtraKetaRow : Prop :=
  ∀ {m n : Nat} {Γ : List VExpr} {p : Pattern} {r : p.RHS × p.Check}
    {e e' w A : VExpr} {m1 m2 m2'},
    (∀ k, k < m → TriangleAt k) → (∀ a, TriangleAtOn m Γ (m2 a)) →
    n + 1 ≤ m → OnCtx Γ (IsType env univs) → Γ ⊢ e : A →
    Params.Pat p r → Pattern.Matches p e m1 m2 →
    Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2 →
    (∀ a, CParRedKn m Γ (m2 a) (m2' a)) →
    EtaK Γ e w → ParRedKn n Γ w e' →
    ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ Pattern.RHS.apply m1 m2' r.1

/-- **dev = `zero`**: the grade side condition collapses the whole row.  `CParRedKn 0` is
reflexivity, `n ≤ 0` forces `n = 0`, and `ParRedKn 0` is reflexivity too
(`ParRedKn.zero_eq`, Round 1), so step and development agree on the nose. -/
theorem zero_dev_row {n : Nat} {Γ : List VExpr} {e e' o A : VExpr} (hnm : n ≤ 0)
    (_hΓ : OnCtx Γ (IsType env univs)) (he : Γ ⊢ e : A)
    (h1 : ParRedKn n Γ e e') (h2 : CParRedKn 0 Γ e o) :
    ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ o := by
  cases Nat.le_zero.1 hnm
  cases h1.zero_eq
  cases h2.zero_eq
  exact ⟨_, .rfl, .refl he⟩

/-- **step = `keta`, against all ten development constructors** -- the block Round 1's ledger
omits.  Nine of the ten are discharged here; the tenth is handed in as `HX`, and
`ExtraKetaRow` is its `Prop` form.

* `zero` -- impossible: a `keta` step has grade `n+1 ≥ 1`, and `n+1 ≤ m` forces `m ≥ 1`;
* `bvar`, `sort`, `lam`, `forallE` -- `EtaK.not_bvar/not_sort/not_lam/not_forallE`;
* `beta` -- `EtaK.not_beta` (Round 1);
* `const`, `app` -- the development's `¬ NonNeutralK` guard, refuted by `NonNeutralK.of_etaK`.
  **This is what makes the block cheap, and it is the block's one real observation**: exactly the
  two *guarded* congruences are the ones a `keta` step can reach at the same node, and the guard
  is precisely what kills them.  Round 1 proved `NonNeutralK.of_etaK` for the opposite direction
  and did not notice it settles seven rows on this side;
* `keta` -- Round 1's `keta_keta_row`, from `KetaDevAgree` and the grade IH;
* `extra` -- open. -/
theorem keta_step_row (HA : KetaDevAgree) {m n : Nat} {Γ : List VExpr} {e e' w o A : VExpr}
    (IHlt : ∀ k, k < m → TriangleAt k)
    (HX : ∀ {p : Pattern} {r : p.RHS × p.Check} {m1 : p.LPath → List VLevel}
      {m2 m2' : p.Path → VExpr},
      Params.Pat p r → Pattern.Matches p e m1 m2 →
      Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2 →
      (∀ a, CParRedKn m Γ (m2 a) (m2' a)) →
      ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ Pattern.RHS.apply m1 m2' r.1)
    (hnm : n + 1 ≤ m)
    (hΓ : OnCtx Γ (IsType env univs)) (he : Γ ⊢ e : A)
    (hek : EtaK Γ e w) (hk : ParRedKn n Γ w e') (h2 : CParRedKn m Γ e o) :
    ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ o := by
  cases h2 with
  | zero => omega
  | bvar => exact absurd hek EtaK.not_bvar
  | sort => exact absurd hek EtaK.not_sort
  | lam => exact absurd hek EtaK.not_lam
  | forallE => exact absurd hek EtaK.not_forallE
  | beta => exact absurd hek EtaK.not_beta
  | const hn => exact absurd (NonNeutralK.of_etaK hek) hn
  | app hn _ _ => exact absurd (NonNeutralK.of_etaK hek) hn
  | @keta k _ _ w₂ _ hek₂ hd =>
    exact keta_keta_row HA (IHlt k (by omega)) (by omega) hΓ he hek hek₂ hk hd
  | extra b1 b2 b3 b4 => exact HX b1 b2 b3 b4

/-! ## §3 The port

`ChurchRosser.ParRed.triangle` transposed to `ParRedKn`/`CParRedKn`, with `VExpr.brecOn` on the
subject and a *strong* induction on the grade outside it.  One structural change: where the
original inducts on the development `H2`, this one only **cases** on it, and every place the
original used an `H2`-induction hypothesis is served instead by the `brecOn` below-structure at
the corresponding subterm.  That is what lets the grade stay fixed at `m+1` through the whole
inner argument -- `induction H2` would generalise the grade, and the grade occurs in `IHlt`.

The `extra` development case is handed out as `ExtraDevRow` rather than transcribed.  That is a
budget decision, stated as such: `ParRed.triangle`'s `extra` case is an inner induction over the
*step* proving a two-way disjunction ("the pattern survives" / "a registered rule fired at a
subpattern position, resolved by `Params.pat_uniq`"), and §4 measures why a `keta` step needs a
**third** branch that neither `pat_uniq` nor `Pattern.matches_inter` can close. -/

/-- **The development fires a pattern rule, against any step.**  Nine rows: `ParRed.triangle`'s
`extra` case (eight rows) plus `ExtraKetaRow` (one).  Carried as a residual rather than
transcribed; §4 says what its `keta` branch needs and why.

It carries everything in scope at its site: the strong grade IH, and the triangle at grade `m` on
each **matched argument** -- which the port builds from the `brecOn` below-structure by an
induction over the pattern, so the residual is handed a genuine hypothesis and not an axiom. -/
def ExtraDevRow : Prop :=
  ∀ {m n : Nat} {Γ : List VExpr} {p : Pattern} {r : p.RHS × p.Check}
    {e e' A : VExpr} {m1 m2 m2'},
    (∀ k, k < m → TriangleAt k) → (∀ a, TriangleAtOn m Γ (m2 a)) →
    n ≤ m → OnCtx Γ (IsType env univs) → Γ ⊢ e : A →
    Params.Pat p r → Pattern.Matches p e m1 m2 →
    Pattern.Check.OK (IsDefEqU env univs Γ) m1 m2 r.2 →
    (∀ a, CParRedKn m Γ (m2 a) (m2' a)) →
    ParRedKn n Γ e e' →
    ∃ o', ParRedK Γ e' o' ∧ Γ ⊢ o' ≡ₚ Pattern.RHS.apply m1 m2' r.1

/-- `ExtraKetaRow` is the `step = keta` row *of* `ExtraDevRow`, so the ledger's new row and the
port's residual are the same object seen from two sides.  Proved, not asserted. -/
theorem ExtraDevRow.toKeta (H : ExtraDevRow) : ExtraKetaRow :=
  fun IHlt IHargs hnm hΓ he h1 h2 h3 h4 hek hk =>
    H IHlt IHargs hnm hΓ he h1 h2 h3 h4 (.keta hek hk)


theorem triangleAt_of (HA : KetaDevAgree) (HApp : KetaAppRow) (HExtra : KetaExtraRow)
    (HED : ExtraDevRow) {m : Nat} (IHlt : ∀ k, k < m → TriangleAt k) : TriangleAt m := by
  intro n Γ e e' o A hnm hΓ he H1 H2
  cases m with
  | zero => exact zero_dev_row hnm hΓ he H1 H2
  | succ m => ?_
  induction e using VExpr.brecOn generalizing Γ A e' o n with | _ e e_ih => ?_
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  cases H2 with
  | bvar =>
    cases H1 with
    | bvar => exact ⟨_, .rfl, .refl he⟩
    | extra _ h2 => cases h2
    | keta hek _ => exact absurd hek EtaK.not_bvar
  | sort =>
    cases H1 with
    | sort => exact ⟨_, .rfl, .refl he⟩
    | extra _ h2 => cases h2
    | keta hek _ => exact absurd hek EtaK.not_sort
  | const hn =>
    cases H1 with
    | const => exact ⟨_, .rfl, .refl he⟩
    | extra h1 h2 h3 => exact absurd (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩)) hn
    | keta hek _ => exact absurd (NonNeutralK.of_etaK hek) hn
  | app hn d1 d2 =>
    have ⟨_, _, l1, l2⟩ := he.app_inv henv hΓ
    cases H1 with
    | app r1 r2 =>
      let ⟨_, p1, n1⟩ := e_ih.1.1 hΓ l1 r1 hnm d1
      let ⟨_, p2, n2⟩ := e_ih.2.1 hΓ l2 r2 hnm d2
      have o1 := p1.hasType hΓ (r1.toParRedK.hasType hΓ l1)
      have o2 := p2.hasType hΓ (r2.toParRedK.hasType hΓ l2)
      exact ⟨_, .app p1 p2, .appDF o1 (.defeqU_l henv hΓ (n1.defeq hΓ) o1)
        o2 (.defeqU_l henv hΓ (n2.defeq hΓ) o2) n1 n2⟩
    | extra h1 h2 h3 => exact absurd (.inr (.inl ⟨_, _, _, _, h1, h2, h3⟩)) hn
    | beta => exact absurd (.inl ⟨_, _, _, rfl⟩) hn
    | keta hek _ => exact absurd (NonNeutralK.of_etaK hek) hn
  | lam d1 d2 =>
    have ⟨⟨_, l1⟩, _, l2⟩ := he.lam_inv henv hΓ
    cases H1 with
    | lam r1 r2 =>
      let ⟨_, p1, n1⟩ := e_ih.1.1 hΓ l1 r1 hnm d1
      refine have hΓ' := ⟨hΓ, _, l1⟩; let ⟨_, p2, n2⟩ := e_ih.2.1 hΓ' l2 r2 hnm d2; ?_
      have := (r1.toParRedK.defeq hΓ l1).trans
        (p1.defeq hΓ (r1.toParRedK.hasType hΓ l1)) |>.symm
      refine ⟨_, .lam p1 ?_, .lamDF this.symm (this.symm.transU_l henv hΓ (n1.defeq hΓ)) n2⟩
      exact p2.defeqDFC hΓ (.succ .zero (r1.toParRedK.defeq hΓ l1))
        (r2.toParRedK.hasType (by exact ⟨hΓ, _, l1⟩) l2)
    | extra _ h2 => cases h2
    | keta hek _ => exact absurd hek EtaK.not_lam
  | forallE d1 d2 =>
    have ⟨⟨_, l1⟩, _, l2⟩ := he.forallE_inv henv
    cases H1 with
    | forallE r1 r2 =>
      let ⟨_, p1, n1⟩ := e_ih.1.1 hΓ l1 r1 hnm d1
      refine have hΓ' := ⟨hΓ, _, l1⟩; let ⟨_, p2, n2⟩ := e_ih.2.1 hΓ' l2 r2 hnm d2; ?_
      exact ⟨_, .forallE p1 (p2.defeqDFC hΓ (.succ .zero (r1.toParRedK.defeq hΓ l1))
          (r2.toParRedK.hasType hΓ' l2)),
        .forallEDF (.trans (r1.toParRedK.defeq hΓ l1)
            (p1.defeq hΓ (r1.toParRedK.hasType hΓ l1)))
          n1 (p2.hasType hΓ' (r2.toParRedK.hasType hΓ' l2)) n2⟩
    | extra _ h2 => cases h2
    | keta hek _ => exact absurd hek EtaK.not_forallE
  | beta l1 l2 =>
    have ⟨_, _, lf, la⟩ := he.app_inv henv hΓ
    have ⟨⟨_, lA⟩, _, le⟩ := lf.lam_inv henv hΓ
    have ⟨⟨_, hw⟩, _⟩ := (lf.uniqU henv hΓ (HasType.lam lA le)).forallE_inv henv hΓ
    have la' := hw.defeq la
    obtain ⟨⟨-, ⟨-, e_ih1 : VExpr.below ..⟩, ⟨hbody, e_ih2 : VExpr.below ..⟩⟩,
      ⟨harg, e_ih3 : VExpr.below ..⟩⟩ := e_ih
    cases H1 with
    | app rf ra =>
      let ⟨_, p3, n3⟩ := harg hΓ la ra hnm l2
      cases rf with
      | lam rA re =>
        refine have hΓ' := ⟨hΓ, _, lA⟩; let ⟨_, p2, n2⟩ := hbody hΓ' le re hnm l1; ?_
        refine ⟨_, .beta (p2.defeqDFC hΓ (.succ .zero (rA.toParRedK.defeq hΓ lA))
          (re.toParRedK.hasType hΓ' le)) p3, ?_⟩
        refine .trans hΓ
          (.instN_r hΓ' (p3.hasType hΓ (ra.toParRedK.hasType hΓ la')) n3 .zero
            (p2.hasType hΓ' (re.toParRedK.hasType hΓ' le)))
          (.instN (l2.toParRedK.hasType hΓ la') .zero n2)
      | extra _ h2 => cases h2
      | keta hek _ => exact absurd hek EtaK.not_lam
    | beta re ra =>
      refine have hΓ' := ⟨hΓ, _, lA⟩
        let ⟨_, p2, n2⟩ := hbody hΓ' le re (Nat.le_of_succ_le hnm) l1; ?_
      let ⟨_, p3, n3⟩ := harg hΓ la ra (Nat.le_of_succ_le hnm) l2
      refine ⟨_, .instN p3 (ra.toParRedK.hasType hΓ la') .zero p2, ?_⟩
      refine .trans hΓ
        (.instN_r hΓ' (p3.hasType hΓ (ra.toParRedK.hasType hΓ la')) n3 .zero
          (p2.hasType hΓ' (re.toParRedK.hasType hΓ' le)))
        (.instN (l2.toParRedK.hasType hΓ la') .zero n2)
    | extra _ h2 => cases h2 with | app h | var h => cases h
    | keta hek _ => exact absurd hek EtaK.not_beta
  | keta hek hd =>
    exact keta_root_row HA HApp HExtra (IHlt m (by omega)) hnm hΓ he hek hd H1
  | @extra _ _ p r _ m1 m2 m2' l1 l2 l3 l4 =>
    refine HED (fun k hk => IHlt k (by omega)) ?_ hnm hΓ he l1 l2 l3 l4 H1
    clear l1 l3 l4 H1 r m2'
    induction p generalizing e A with
    | const => exact nofun
    | app f a ih1 ih2 =>
      let .app hm1 hm2 := l2
      have ⟨_, _, H1, H2⟩ := he.app_inv henv hΓ
      exact Sum.rec (ih1 _ H1 e_ih.1.2 hm1) (ih2 _ H2 e_ih.2.2 hm2)
    | var _ ih =>
      let .var hm1 := l2
      have ⟨_, _, H1, _⟩ := he.app_inv henv hΓ
      exact Option.rec (fun hnm' hΓ' hty h1 h2 => e_ih.2.1 hΓ' hty h1 hnm' h2)
        (ih _ H1 e_ih.1.2 hm1)

/-! ## §4 The assembly, and what the residual list is

Four residuals, and that is the whole list:

| residual | rows | origin |
|---|---|---|
| `KetaDevAgree` | dev `keta` x step `keta` | Round 1, and **fired at `quotParams`** there |
| `KetaAppRow` | dev `keta` x step congruence at an application | Round 1, open |
| `KetaExtraRow` | dev `keta` x step `extra` | Round 1, open |
| `ExtraDevRow` | dev `extra` x every step (9 rows) | **this round**, and it contains `ExtraKetaRow` |

Everything else -- 72 of the 90 rows, including all of `zero`, `bvar`, `sort`, `const`, `app`,
`lam`, `forallE`, `beta` on the development's side against every step -- is **compiled** above.
So the sentence Round 1 refused to write, and was right to refuse, can now be written in a
sharper form: the triangle is proved **modulo four named residual `Prop`s, with no unrun port**. -/

theorem triangleAt_all (HA : KetaDevAgree) (HApp : KetaAppRow) (HExtra : KetaExtraRow)
    (HED : ExtraDevRow) : ∀ m, TriangleAt m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih => exact triangleAt_of HA HApp HExtra HED (fun k hk => ih k hk)

/-- **`ParRedKnTriangle`, from four residuals.**  Round 1's hypothesis, now a theorem modulo a
closed list -- and the list is four `Prop`s in this file and `CParRedK.lean`, not an unrun
induction. -/
theorem parRedKnTriangle_of (HA : KetaDevAgree) (HApp : KetaAppRow) (HExtra : KetaExtraRow)
    (HED : ExtraDevRow) : ParRedKnTriangle :=
  parRedKnTriangle_of_at (triangleAt_all HA HApp HExtra HED)

/-- The diamond, and then `CRStatementK`, with `ParRedKnTriangle` discharged down to the four
rows.  This is `CRKProve.crStatementK_of`'s second hypothesis replaced by a *row list*. -/
theorem parRedKDiamond_of_rows (HA : KetaDevAgree) (HApp : KetaAppRow) (HExtra : KetaExtraRow)
    (HED : ExtraDevRow) : ParRedKDiamond :=
  parRedKDiamond_of_triangle (parRedKnTriangle_of HA HApp HExtra HED)

theorem crStatementK_of_rows (HS : ParRedKStatement) (HA : KetaDevAgree) (HApp : KetaAppRow)
    (HExtra : KetaExtraRow) (HED : ExtraDevRow) : CRStatementK :=
  crStatementK_of_triangle HS (parRedKnTriangle_of HA HApp HExtra HED)

/-! ## §4a Where `ExtraDevRow`'s `keta` branch actually splits -- measured, not asserted

S8.5 predicted that `ParRed.triangle`'s `extra` inner induction needs a **third** branch for a
`keta` step, because `KStep` matches its pattern at the *converted* major premise `.app f c` rather
than at the subject `.app f h`, so `Pattern.matches_inter` (which needs both patterns to match the
**same** term) and hence `Params.pat_uniq` cannot collapse the branch to the root the way they
collapse the `extra` branch.

The three lemmas below turn half of that analysis into theorems, and they split the branch
cleanly in two:

* **at the root** of the redex, `e.appDepth = p.depth = P₁.depth + 1`, the fuel is `0`, and
  `EtaK.here` is available -- this is the `KDiamond`-shaped row, and it is `ExtraKetaRow`;
* **at any strict skeleton node**, `e.appDepth ≤ P₁.depth`, the fuel is `≥ 1`, so `EtaK.here` is
  **impossible** and the step is forced to be `EtaK.under`; its contractum is therefore a `.lam`,
  which no `Pattern.Matches` accepts. So the reduct leaves the skeleton, and the inner induction's
  "the pattern survives" branch is *provably* unavailable there.

The tool is `KMeasure.EtaKn.fuel_eq` -- `k = p₁.depth + 1 - e.appDepth`, itself resting on
`Params.pat_app_depth_uniq`. Round 1 quoted `height_uniq` for the `keta` x `keta` row; the same
measure settles this, one row over. -/

/-- **`EtaK.here` cannot fire at a partial application of a registered redex.**  Its fuel is
`P₁.depth + 1 - e.appDepth ≥ 1`, and `here` has fuel `0`. -/
theorem EtaK.not_here_of_partial {Γ : List VExpr} {e t : VExpr} {P₁ P₂ : Pattern}
    {r : (Pattern.app P₁ P₂).RHS × (Pattern.app P₁ P₂).Check}
    (hp : Params.Pat (.app P₁ P₂) r) (hh : e.headConst? = some P₁.headName)
    (hle : e.appDepth ≤ P₁.depth) : ¬ KStep Γ e t := by
  intro hst
  have := (EtaKn.here hst).fuel_eq hp hh
  omega

/-- So an `EtaK` step at such a node is forced to be `under`, and its contractum is a `.lam`. -/
theorem EtaK.under_of_partial {Γ : List VExpr} {e w : VExpr} {P₁ P₂ : Pattern}
    {r : (Pattern.app P₁ P₂).RHS × (Pattern.app P₁ P₂).Check}
    (hp : Params.Pat (.app P₁ P₂) r) (hh : e.headConst? = some P₁.headName)
    (hle : e.appDepth ≤ P₁.depth) (H : EtaK Γ e w) :
    ∃ A B t, w = .lam A t ∧ Γ ⊢ e : .forallE A B ∧
      EtaK (A::Γ) (.app e.lift (.bvar 0)) t := by
  cases H with
  | here hst => exact absurd hst (EtaK.not_here_of_partial hp hh hle)
  | under hty h => exact ⟨_, _, _, rfl, hty, h⟩

omit [Params] in
/-- No pattern matches a λ: `Pattern.Matches.spineHead_const` forces a constant spine head, and a
λ's spine head is itself.  (`VExpr.headConst?` does *not* settle this -- it looks **through**
binders, so `(.lam A t).headConst? = t.headConst?` and a λ can have one.) -/
theorem matches_not_lam {p : Pattern} {A t : VExpr} {m1 m2} :
    ¬ p.Matches (.lam A t) m1 m2 := by
  intro h
  obtain ⟨c, ls, hc⟩ := h.spineHead_const
  exact absurd hc (by simp [VExpr.spineHead])

/-- **The measured reason `ExtraDevRow`'s `keta` branch needs an argument the `extra` branch does
not.**  At a strict skeleton node of a registered redex, a `keta` step's contractum is a `.lam`,
so it matches **no** pattern whatsoever -- the reduct has left the skeleton, and
`ParRed.triangle`'s "the pattern survives with reduced arguments" branch is unavailable by a
theorem rather than by an unproved case. -/
theorem etaK_leaves_skeleton {Γ : List VExpr} {e w : VExpr} {P₁ P₂ : Pattern}
    {r : (Pattern.app P₁ P₂).RHS × (Pattern.app P₁ P₂).Check}
    (hp : Params.Pat (.app P₁ P₂) r) (hh : e.headConst? = some P₁.headName)
    (hle : e.appDepth ≤ P₁.depth) (H : EtaK Γ e w) :
    ∀ (q : Pattern) m1 m2, ¬ q.Matches w m1 m2 := by
  obtain ⟨A, B, t, rfl, _, _⟩ := EtaK.under_of_partial hp hh hle H
  exact fun _ _ _ => matches_not_lam

/-- And at the **root** the same measure says the opposite: the fuel is `0` there, so `EtaK.here`
is exactly what is available and the row is `KDiamond`-shaped.  Stated as the fuel computation,
which is the only part that is a theorem. -/
theorem etaK_root_fuel_zero {Γ : List VExpr} {e w : VExpr} {P₁ P₂ : Pattern}
    {r : (Pattern.app P₁ P₂).RHS × (Pattern.app P₁ P₂).Check} {m1 m2}
    (hp : Params.Pat (.app P₁ P₂) r) (hm : (Pattern.app P₁ P₂).Matches e m1 m2)
    (H : EtaK Γ e w) : ∃ k, EtaKn k Γ e w ∧ k = 0 := by
  obtain ⟨k, hk⟩ := H.count
  refine ⟨k, hk, ?_⟩
  have hd := hm.appDepth
  have := hk.fuel_eq hp hm.headName
  simp [Pattern.depth] at hd
  omega

end VEnv

namespace VEnv

/-! ## §5 Fired

`refParams` first, because it settles a limit Round 1 recorded as open, and then `quotParams`,
which is the non-degenerate instance. -/

/-- `ExtraDevRow` is vacuous at `refParams`: `DescendRefute.refNoPat` says the instance registers
no pattern at all, so the row's `Params.Pat` premise is uninhabited. -/
theorem refParams_extraDevRow : @ExtraDevRow refParams :=
  fun _ _ _ _ _ h1 => absurd h1 refNoPat

/-- **`ParRedKnTriangle` at `refParams`, unconditionally** -- which Round 1 listed as an open
limit (§4.5: "I did **not** compile `refParams_parRedKnTriangle` -- it needs `ParRedKn → ParRed`
and `CParRedKn → CParRed` at `refParams`, which is real work").  The port makes it free: the four
residuals are all vacuous there, so the triangle follows from the *general* theorem rather than
from a translation back to `ChurchRosser.ParRed.triangle`.

It is still a **consistency check and not evidence**: at `refParams` both `KStep` and `Pat` are
empty, so every row that could be interesting is vacuous. What it does rule out is a
*joint* inconsistency of the four residuals. -/
theorem refParams_parRedKnTriangle : @ParRedKnTriangle refParams :=
  @parRedKnTriangle_of refParams refParams_ketaDevAgree refParams_ketaAppRow
    refParams_ketaExtraRow refParams_extraDevRow

section
attribute [local instance] quotParams

/-- **The port instantiated at the non-degenerate instance.**  `quotParams` is the one of
`CRKProve` §2's eight instances where the rule contracts, and where `KStep` is *not* empty
(`quotParams_kstep_eta`) -- so unlike `refParams` nothing here is vacuous by an empty premise. -/
theorem quotParams_parRedKnTriangle_of (HA : KetaDevAgree) (HApp : KetaAppRow)
    (HExtra : KetaExtraRow) (HED : ExtraDevRow) : ParRedKnTriangle :=
  parRedKnTriangle_of HA HApp HExtra HED

/-- **THE FIRING.**  The triangle, at the term `quotParams`' K-rule actually moves.

`CRKProve.quotParams_parRedK_qLiftT` reduces `qLiftT` by a `keta` step whose `EtaK` derivation is
`.under _ (.here quotParams_kstep_eta)` -- an η-tower of height one over a live `KStep`.  So the
subject is `EtaK`-reducible, `NonNeutralK` holds at it, and the development produced by
`CParRedKn.exists` has `keta` as its **root** step: this is not a rigid subject dressed up.

The conclusion is the triangle's own: a `ParRedK` leg from the step's reduct meeting the
development up to `NormalEq`. -/
theorem quotParams_triangle_fires (HA : KetaDevAgree) (HApp : KetaAppRow)
    (HExtra : KetaExtraRow) (HED : ExtraDevRow) {e' : VExpr}
    (h : ParRedK qc0T (qLiftT .zero (.succ .zero)) e') :
    ∃ n o o', CParRedKn n qc0T (qLiftT .zero (.succ .zero)) o ∧
      ParRedK qc0T e' o' ∧ NormalEq qc0T o' o := by
  obtain ⟨n, hn⟩ := h.toN
  obtain ⟨o, ho⟩ := CParRedKn.exists (n := n) qc0T_wf qLiftT0_hasType
  obtain ⟨o', p, q⟩ :=
    parRedKnTriangle_of HA HApp HExtra HED (Nat.le_refl n) qc0T_wf qLiftT0_hasType hn ho
  exact ⟨n, o, o', ho, p, q⟩

/-- The same, applied to the K-step reduct itself rather than to an arbitrary one. -/
theorem quotParams_triangle_at_keta (HA : KetaDevAgree) (HApp : KetaAppRow)
    (HExtra : KetaExtraRow) (HED : ExtraDevRow) :
    ∃ n e' o o', ParRedK qc0T (qLiftT .zero (.succ .zero)) e' ∧
      CParRedKn n qc0T (qLiftT .zero (.succ .zero)) o ∧
      ParRedK qc0T e' o' ∧ NormalEq qc0T o' o :=
  let ⟨n, o, o', ho, p, q⟩ :=
    quotParams_triangle_fires HA HApp HExtra HED quotParams_parRedK_qLiftT
  ⟨n, _, o, o', quotParams_parRedK_qLiftT, ho, p, q⟩

end

end VEnv

end Lean4Lean
