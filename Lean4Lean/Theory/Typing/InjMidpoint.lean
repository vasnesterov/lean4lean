import Lean4Lean.Theory.Typing.InjChainStep

/-!
# `ConvStep2` localised at its midpoint: three of six heads are free, and the level-alignment reading of the obstruction is wrong

`Theory/Typing/InjChainStep.lean` isolates `ConvStep2` — compose two conversions at syntactic
sorts sharing an endpoint, at *some* sort — as the single node both injectivity holes share
(`InjSpineTransport.lean`), and closes with this reading of where the work sits:

> The only route to `ConvStep2` in this file is `convStep2_of_convStep2Level`, and
> `ConvStep2Level` is `SortUniq` on the nose. … Every attempt to build the composed conversion
> in this tree's calculus goes through `IsDefEqStrong.defeqDF`, whose type premise at a sort is
> `sortDF`, whose side condition is `a ≈ b`.

**The first sentence is true of that file; the second is false of the tree.**  There is a route
that never compares the two link levels, and it was already sitting in
`Theory/Typing/BaseUniqChain.lean`: `ConvC.transport` moves a conversion along a chain one
`defeqDF` at a time, and the `defeqDF`s it builds are at *arbitrary* types, never at a pair of
syntactic sorts, so no `sortDF` and no `a ≈ b` ever appears.  Feeding it the chain that
`uniqStrongCAt_of_baseUniqCAt` produces gives

```lean
convStep2At_of_baseUniqCAt : Ordered env → BaseUniqCAt env U Y → ConvStep2At env U Y
```

— the composition step at a **fixed midpoint**, from base-type uniqueness at that one term.
Three lines, `Ordered env` its only hypothesis besides the localised one, no level equivalence
anywhere in the proof term.

## §1 What that buys: the midpoint-head decomposition

`ConvStep2` is `∀ Y, ConvStep2At env U Y` (`convStep2At_all_iff_convStep2`), and
`BaseUniqChain.baseUniqCAt_of`'s case analysis therefore transfers to it verbatim:

| midpoint head | `ConvStep2At` at it costs |
|---|---|
| `.bvar i` | **nothing** (`convStep2At_bvar`) |
| `.sort l` | **nothing** (`convStep2At_sort`) |
| `.const c ls` | **nothing** (`convStep2At_const`) |
| `.lam D b` | `BaseUniqCAt` at the **body** (`convStep2At_lam`) |
| `.app f a` | `ConvPiInv` + `BaseUniqCAt` at the **function** (`convStep2At_app`) |
| `.forallE D b` | `ConvSortInv` + `BaseUniqCAt` at **domain and body** (`convStep2At_forallE`) |

Three of `VExpr`'s six heads cost nothing at all, and a fourth costs only a proper subterm.
`MidFree` names the closure of the three free heads under `.lam`, and
`convStep2At_of_midFree` discharges the whole family from `Ordered env` alone — the first
`sorryAx`-free, hypothesis-free supply of *any* instance of `ConvStep2` in this tree.

`convStep2At_sort_discharges` is the collapse test.  `InjChainStep.convStep2_fires` exhibits an
instance of `ConvStep2`'s **premises** at `Γ = []` with the two link levels syntactically
different, as evidence that the hypothesis is not degenerate; that instance has midpoint
`.sort .zero`, so its **conclusion** is now a theorem, with the two endpoints syntactically
different expressions and no hypothesis but `Ordered env`.

So the obstruction is not "the interior links have arbitrary midpoints".  It is exactly
**Π-headed and application-headed midpoints**, and for those the cost is at proper subterms plus
one chain-inversion hypothesis.

## §2 The bounds, both ways — and the verdict

Upper bounds on the residual:

* `convStep2_of_baseUniqC` / `convStep2_of_baseUniq` — `BaseUniqC` (equivalently, through
  `baseUniqC_of_baseUniq`, `ProofRetypeHeads.BaseUniq`) implies `ConvStep2`;
* `convStep2_of_convInv` — so do `ConvSortInv ∧ ConvPiInv`, through `baseUniqC_of`.

Lower bounds, from `InjChainStep` §4–5:

* `convInv_iff_convStep2` — over `SortInv ∧ PiInv`, `ConvSortInv ∧ ConvPiInv` **is**
  `ConvStep2`;
* `baseUniqC_iff_convStep2` — over `SortInv ∧ PiInv`, `BaseUniqC` **is** `ConvStep2`.

**Verdict, stated plainly: globally this is a restatement, not a reduction.**  Modulo the two
bridge entries `SortInv` and `PiInv`, the statements

    ConvStep2   BaseUniq   BaseUniqC   ConvSortInv ∧ ConvPiInv   UniqStrong   SortUniq

are one node, and this file adds two of the arrows that close that circle rather than breaking
it.  What is *not* a restatement is §1: the midpoint decomposition is unconditional, and three
of its six heads are discharged outright.

## §3 A `SortUniq` that was being left on the table

`ProofRetypeHeads.lean` §4 answers `docs/handoff-injectivity.md` §4B.5 — *are the four
`retypes` residuals strictly weaker than the corner?* — "in the negative **up to `SortUniq`**",
because its `uniqStrong_of_baseUniq` assumes `SortUniq` on top of `BaseUniq`.  The qualifier can
be dropped:

```lean
sortUniq_of_baseUniq_sortInv : Ordered env → BaseUniq env U → env.SortInv U → env.SortUniq U
uniqStrong_of_baseUniq_sortInv : Ordered env → BaseUniq env U → env.SortInv U → UniqStrong env U
```

and, going through `IsDefEqStrong.retypes` rather than `BaseUniq`,

```lean
convStep2_of_retypes : Ordered env → BetaRetype env U → EtaRetype env U → ProofRetype env U →
  ExtraRetype env U → ConvStep2 env U
sortUniq_of_retypes : … → env.SortInv U → PiInv env U → env.SortUniq U
```

`SortInv` is a single entry of `Injectivity.RigidShapeUniq` (the `sort`/`sort` one, the one
`rigidShapeUniq_of_sortUniq` already removes from hole B), and it is strictly below `SortUniq`
on the recorded arrows (`SortUniqDown.SortInv.of_sortUniq` one way, and nothing back short of
`SortUniqDown.sortUniq_of`, which also wants `UniqTy`).  So the answer to §4B.5 is now: **the
four residuals are not weaker than the corner, modulo `SortInv ∧ PiInv`** — and `SortUniq` need
not be assumed to say it.  `convStep2_of_retypes` is the one-line proof; note it never touches
a level, which is the same point as §0.

## §4 Why the two costly heads are still circular — precisely

`baseUniqCAt_forallE` applies `ConvSortInv` to the chain
`uniqStrongCAt_of_baseUniqCAt (BaseUniqCAt D)`, i.e. to `peelChain`'s two walks joined by
`BaseUniqCAt` at `D`.  The interior nodes of a `peelChain` walk are the type arguments of the
`HasTypeStrong.defeq` wrappers in `D`'s typing derivation: they are **types of the subject**,
not subterms of it.  So the recursion that discharges `BaseUniqCAt` — structural on the term —
does not reach them, and there is no measure in which "term plus its own types" descends.  That
is the shape of the remaining obstruction, and it is *not* the shape
`convStep2Level_iff_sortUniq` suggests: the residual is not a level comparison, it is a
reachability question about which terms can appear as intermediate types in a derivation.

Two routes that this makes precise and closes:

* **Collapse a chain link-by-link with `SortInv` instead of `ConvSortInv`.**  Needs every
  interior node of the chain to be a syntactic sort.  Nothing forces that: an interior node is
  an arbitrary type of the subject, and knowing a conversion out of a sort has a sort at its
  other end is `Injectivity.IsDefEqU.sort_forallE_inv` and `const_sort_inv`, i.e. hole B —
  which `InjSpineTransport` shows needs `ConvStep2`.
* **Apply `PiInv` link-by-link instead of `ConvPiInv`.**  Same failure with `.forallE` for
  `.sort`: `PiInv`'s premise is one `IsDefEqU`, i.e. one type for the whole conversion, and a
  chain has one per link.

## §5 Non-vacuity, and what does *not* move

`convStep2At_sort_discharges` is a derivation, not a firing test, so §1's free heads are
non-vacuous by construction.  No census movement, no cone movement: this file is imported by
nothing, and every statement in it is either unconditional or takes its inputs as hypotheses.

## §6 Axiom check

    #print axioms Lean4Lean.VEnv.convStep2At_of_baseUniqCAt   -- [propext, Quot.sound]
    #print axioms Lean4Lean.VEnv.convStep2At_bvar
    #print axioms Lean4Lean.VEnv.convStep2At_sort
    #print axioms Lean4Lean.VEnv.convStep2At_const
    #print axioms Lean4Lean.VEnv.convStep2At_lam
    #print axioms Lean4Lean.VEnv.convStep2At_app
    #print axioms Lean4Lean.VEnv.convStep2At_forallE
    #print axioms Lean4Lean.VEnv.baseUniqCAt_of_midFree
    #print axioms Lean4Lean.VEnv.convStep2At_of_midFree
    #print axioms Lean4Lean.VEnv.convStep2_of_baseUniqC
    #print axioms Lean4Lean.VEnv.convStep2_of_baseUniq
    #print axioms Lean4Lean.VEnv.convStep2_of_convInv
    #print axioms Lean4Lean.VEnv.convStep2_of_retypes
    #print axioms Lean4Lean.VEnv.sortUniq_of_retypes
    #print axioms Lean4Lean.VEnv.sortUniq_of_baseUniqC_sortInv
    #print axioms Lean4Lean.VEnv.sortUniq_of_baseUniq_sortInv
    #print axioms Lean4Lean.VEnv.uniqStrong_of_baseUniq_sortInv
    #print axioms Lean4Lean.VEnv.convInv_iff_convStep2
    #print axioms Lean4Lean.VEnv.baseUniqC_iff_convStep2
    #print axioms Lean4Lean.VEnv.convStep2At_all_iff_convStep2   -- [propext]
    #print axioms Lean4Lean.VEnv.convStep2At_sort_discharges
    #print axioms Lean4Lean.VEnv.baseUniqC_of_baseUniq           -- [propext]

None mentions `sorryAx`, despite `Injectivity.lean` being imported through `InjChainStep`:
nothing here consumes `piInvStratApp_axiom`, `WF.sortUniq'`, `WF.rigidShapeUniqNS`,
`IsProof.defeqU` or `WF.uniq'`.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- `ConvStep2` at a fixed midpoint `Y`. -/
def ConvStep2At (env : VEnv) (U : Nat) (Y : VExpr) : Prop :=
  ∀ {Γ : List VExpr} {X Z : VExpr} {a b : VLevel}, CtxStrong env U Γ →
    env.IsDefEqStrong U Γ X Y (.sort a) → env.IsDefEqStrong U Γ Y Z (.sort b) →
    ∃ u, env.IsDefEqStrong U Γ X Z (.sort u)

theorem convStep2_of_convStep2At (h : ∀ Y, ConvStep2At env U Y) : ConvStep2 env U :=
  fun hΓ h1 h2 => h _ hΓ h1 h2

theorem ConvStep2.at (h : ConvStep2 env U) (Y : VExpr) : ConvStep2At env U Y :=
  fun hΓ h1 h2 => h hΓ h1 h2

/-- **The composition step at a midpoint, from base-type uniqueness at that midpoint alone.** -/
theorem convStep2At_of_baseUniqCAt (henv : Ordered env) {Y : VExpr}
    (hbu : BaseUniqCAt env U Y) : ConvStep2At env U Y := by
  intro Γ X Z a b hΓ h1 h2
  exact ⟨a, h1.trans
    ((uniqStrongCAt_of_baseUniqCAt hbu hΓ h1.hasType'.2 h2.hasType'.1).symm.transport henv hΓ h2)⟩

/-! ## The six midpoint heads -/

theorem convStep2At_bvar (henv : Ordered env) {i : Nat} : ConvStep2At env U (.bvar i) :=
  convStep2At_of_baseUniqCAt henv baseUniqCAt_bvar

theorem convStep2At_sort (henv : Ordered env) {l : VLevel} : ConvStep2At env U (.sort l) :=
  convStep2At_of_baseUniqCAt henv baseUniqCAt_sort

theorem convStep2At_const (henv : Ordered env) {c : Lean.Name} {ls : List VLevel} :
    ConvStep2At env U (.const c ls) :=
  convStep2At_of_baseUniqCAt henv baseUniqCAt_const

theorem convStep2At_lam (henv : Ordered env) {D b : VExpr}
    (hbody : BaseUniqCAt env U b) : ConvStep2At env U (.lam D b) :=
  convStep2At_of_baseUniqCAt henv
    (baseUniqCAt_lam henv (uniqStrongCAt_of_baseUniqCAt hbody))

theorem convStep2At_app (henv : Ordered env) (hpi : ConvPiInv env U) {f a : VExpr}
    (hfn : BaseUniqCAt env U f) : ConvStep2At env U (.app f a) :=
  convStep2At_of_baseUniqCAt henv
    (baseUniqCAt_app henv hpi (uniqStrongCAt_of_baseUniqCAt hfn))

theorem convStep2At_forallE (henv : Ordered env) (hsi : ConvSortInv env U) {D b : VExpr}
    (hdom : BaseUniqCAt env U D) (hbody : BaseUniqCAt env U b) :
    ConvStep2At env U (.forallE D b) :=
  convStep2At_of_baseUniqCAt henv
    (baseUniqCAt_forallE hsi (uniqStrongCAt_of_baseUniqCAt hdom)
      (uniqStrongCAt_of_baseUniqCAt hbody))

/-! ## The midpoints that are free outright -/

/-- **The midpoint heads at which the composition step costs nothing.**  Exactly the heads
`BaseUniqChain.baseUniqCAt_of`'s recursion discharges without `ConvSortInv` or `ConvPiInv`:
`.bvar`, `.sort`, `.const`, and `.lam` over such a body. -/
def MidFree : VExpr → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lam _ b => MidFree b
  | .forallE _ _ => False
  | .app _ _ => False

theorem baseUniqCAt_of_midFree (henv : Ordered env) :
    ∀ {e : VExpr}, MidFree e → BaseUniqCAt env U e := by
  intro e
  induction e with
  | bvar => exact fun _ => baseUniqCAt_bvar
  | sort => exact fun _ => baseUniqCAt_sort
  | const => exact fun _ => baseUniqCAt_const
  | app => exact fun h => h.elim
  | forallE => exact fun h => h.elim
  | lam _ _ _ ihb => exact fun h => baseUniqCAt_lam henv (uniqStrongCAt_of_baseUniqCAt (ihb h))

/-- **`ConvStep2` at a free midpoint, from `Ordered env` and nothing else.** -/
theorem convStep2At_of_midFree (henv : Ordered env) {Y : VExpr} (h : MidFree Y) :
    ConvStep2At env U Y :=
  convStep2At_of_baseUniqCAt henv (baseUniqCAt_of_midFree henv h)

/-! ## Global forms -/

theorem BaseUniqC.at (hbu : BaseUniqC env U) (e : VExpr) : BaseUniqCAt env U e :=
  fun hΓ h1 h2 => hbu hΓ h1 h2

theorem baseUniqC_of_baseUniq (hbu : BaseUniq env U) : BaseUniqC env U :=
  fun hΓ h1 h2 => have ⟨_, h⟩ := hbu hΓ h1 h2; .one h

theorem convStep2_of_baseUniqC (henv : Ordered env) (hbu : BaseUniqC env U) :
    ConvStep2 env U :=
  convStep2_of_convStep2At fun Y => convStep2At_of_baseUniqCAt henv (hbu.at Y)

theorem convStep2_of_baseUniq (henv : Ordered env) (hbu : BaseUniq env U) :
    ConvStep2 env U :=
  convStep2_of_baseUniqC henv (baseUniqC_of_baseUniq hbu)

theorem convStep2_of_convInv (henv : Ordered env) (hsi : ConvSortInv env U)
    (hpi : ConvPiInv env U) : ConvStep2 env U :=
  convStep2_of_baseUniqC henv (baseUniqC_of henv hsi hpi)

/-! ## The four `retypes` residuals, priced -/

/-- **`ConvStep2` from the four computation-rule residuals of `IsDefEqStrong.retypes`.**

`RetypeAdmissible.lean` reduces `retypes` to `BetaRetype`, `EtaRetype`, `ProofRetype` and
`ExtraRetype`, and leaves open (its §"Consequences", and `docs/handoff-injectivity.md` §4B.5)
whether the four are *strictly* weaker than the corner.  They are not, modulo the two bridge
entries: `retypes` re-indexes `Y ≡ Z` at the type `.sort a` that the left conversion already
supplies, and `trans` then fires — so the four give `ConvStep2`, and
`sortUniq_of_retypes` gives universe uniqueness back. -/
theorem convStep2_of_retypes (henv : Ordered env)
    (hbeta : BetaRetype env U) (heta : EtaRetype env U)
    (hproof : ProofRetype env U) (hextra : ExtraRetype env U) : ConvStep2 env U := by
  intro Γ X Y Z a b hΓ h1 h2
  exact ⟨a, h1.trans (h2.retypes henv hbeta heta hproof hextra hΓ (.inl h1.hasType'.2))⟩

/-! ## `SortUniq` from `BaseUniqC` and `SortInv` -/

theorem sortUniq_of_baseUniqC_sortInv (henv : Ordered env) (hbu : BaseUniqC env U)
    (hsi : env.SortInv U) : env.SortUniq U := by
  intro Γ e u v hΓ _ _ h1 h2
  have hΓ' : CtxStrong env U Γ := .strong henv hΓ
  exact convSortInv_of_convStep2 (convStep2_of_baseUniqC henv hbu) hsi hΓ'
    (uniqStrongCAt_of_baseUniqCAt (hbu.at e) hΓ'
      (h1.strong henv hΓ).hasType'.1 (h2.strong henv hΓ).hasType'.1)

theorem sortUniq_of_baseUniq_sortInv (henv : Ordered env) (hbu : BaseUniq env U)
    (hsi : env.SortInv U) : env.SortUniq U :=
  sortUniq_of_baseUniqC_sortInv henv (baseUniqC_of_baseUniq hbu) hsi

theorem uniqStrong_of_baseUniq_sortInv (henv : Ordered env) (hbu : BaseUniq env U)
    (hsi : env.SortInv U) : UniqStrong env U :=
  uniqStrong_of_baseUniq henv (sortUniq_of_baseUniq_sortInv henv hbu hsi) hbu

/-- **The answer to `handoff-injectivity.md` §4B.5**, without the "up to `SortUniq`" qualifier
that `ProofRetypeHeads.lean` §4 had to carry. -/
theorem sortUniq_of_retypes (henv : Ordered env)
    (hbeta : BetaRetype env U) (heta : EtaRetype env U)
    (hproof : ProofRetype env U) (hextra : ExtraRetype env U)
    (hsi : env.SortInv U) (hpi : PiInv env U) : env.SortUniq U :=
  sortUniq_of_convStep2 henv (convStep2_of_retypes henv hbeta heta hproof hextra) hsi hpi

/-! ## Both-ways bounds -/

theorem baseUniqC_iff_convStep2 (henv : Ordered env) (hsi : env.SortInv U) (hpi : PiInv env U) :
    BaseUniqC env U ↔ ConvStep2 env U := by
  refine ⟨convStep2_of_baseUniqC henv, fun hcs => ?_⟩
  have hsu : env.SortUniq U := sortUniq_of_convStep2 henv hcs hsi hpi
  intro Γ e A B hΓ h1 h2
  exact baseUniqC_of henv (convSortInv_of_sortUniq henv hsu)
    (convPiInv_of_sortUniq_piInv henv hsu hpi) hΓ h1 h2

/-- **The two chain-inversion hypotheses, together, are exactly `ConvStep2`** — over the two
bridge entries.  `→` is §"Global forms"; `←` is `InjChainStep` §4. -/
theorem convInv_iff_convStep2 (henv : Ordered env) (hsi : env.SortInv U) (hpi : PiInv env U) :
    (ConvSortInv env U ∧ ConvPiInv env U) ↔ ConvStep2 env U :=
  ⟨fun ⟨h1, h2⟩ => convStep2_of_convInv henv h1 h2,
   fun hcs => ⟨convSortInv_of_convStep2 hcs hsi, convPiInv_of_convStep2 henv hcs hpi⟩⟩

theorem convStep2At_all_iff_convStep2 : (∀ Y, ConvStep2At env U Y) ↔ ConvStep2 env U :=
  ⟨convStep2_of_convStep2At, fun h Y => h.at Y⟩

/-! ## Non-vacuity: the instance `InjChainStep.convStep2_fires` advertises is now a theorem -/

/-- **The collapse test, passing.**  `InjChainStep.convStep2_fires` exhibits the two premises of
`ConvStep2` at `Γ = []` with the two link levels syntactically different, as evidence that the
*hypothesis* is non-degenerate.  At that instance the midpoint is `.sort .zero`, so
`convStep2At_sort` discharges the conclusion outright: no `ConvStep2`, no `SortUniq`, no
`ConvSortInv`, no `VEnv.WF`, and the two endpoints are syntactically different expressions. -/
theorem convStep2At_sort_discharges (henv : Ordered env) :
    ((VExpr.sort (.imax .zero .zero) : VExpr) ≠ .sort (.max .zero .zero)) ∧
    ∃ u, env.IsDefEqStrong 0 [] (.sort (.imax .zero .zero)) (.sort (.max .zero .zero))
      (.sort u) := by
  refine ⟨by intro h; exact absurd h (by simp), ?_⟩
  have h1 : env.IsDefEqStrong 0 [] (.sort (.imax .zero .zero)) (.sort .zero)
      (.sort (.succ (.imax .zero .zero))) := .sortDF ⟨trivial, trivial⟩ trivial VLevel.imax_zero
  have h2 : env.IsDefEqStrong 0 [] (.sort .zero) (.sort (.max .zero .zero))
      (.sort (.succ .zero)) := .sortDF trivial ⟨trivial, trivial⟩ (by rfl)
  exact convStep2At_sort henv trivial h1 h2

end VEnv
end Lean4Lean
