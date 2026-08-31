import Lean4Lean.Theory.Typing.Strong

/-!
# Universe uniqueness, and what it buys

`Theory/Typing/Injectivity.lean`'s open statements are usually described as needing "the
Church–Rosser theorem".  Writing the inductions out shows they need **two** separate things,
and only one of them is about reduction:

1. **Normalisation** — for `IsDefEqStrong.trans`: a term convertible with a sort reduces to
   a sort.  There is no way around this one.
2. **Universe uniqueness** — `VEnv.SortUniq` below: `Γ ⊢ e : .sort u` and `Γ ⊢ e : .sort v`
   force `u ≈ v`.

This file isolates (2) and shows what it alone is worth.  The one theorem here,
`VEnv.sort_not_proof`, closes the `proofIrrel` case of `IsDefEqU.sort_inv` outright — the
case whose refutation was previously described as needing `sort_inv` itself.  It also
supplies exactly the level-alignment step that `IsDefEqU.forallE_inv_stratified`'s
`forallEDF` and `symm` cases stall on (see that lemma's docstring).  So, granted (2), the
Π half of the inversion family reduces to the single `trans` case — and the *sort* half
reduces to nothing at all, because (2) implies `sort_inv` outright (`SortUniqDown.lean`,
and the "Read this first" section below).  **(1) and (2) are therefore not "two separate
things": (2) subsumes the sort-flavoured half of (1).**

**`SortUniq` is a hypothesis, not a theorem.**  *(Superseded — see correction 0 below.
`Theory/Typing/UniqSort.lean` proves it for every `VEnv.WF` environment, relative to
`IsDefEqU.forallE_inv_stratified` alone.  The rest of this paragraph is the pre-existing
state and is kept because its cross-references are still accurate.)*  Nothing in this
repository exhibits one, for any environment.  It is the `VExpr`-side statement of
`Experimental/Reflect/Capstone.lean`'s `sort_uniq_of_hasType` — which is not available, its
`Params`-style side condition being unsatisfiable — and it is what
`SetModel/Interp.lean`'s `LevelAssign.srt_sound` field demands (that field asks a *single*
chosen level to agree with *every* type of a term, which is (2) restated).  So read every
result below as a reduction between open statements, not as progress on either.

`SortUniq` is stated for types only (`e` at a sort), which is all the consumers need; the
`srt`-flavoured version for arbitrary terms is strictly stronger and is not used here.

## Read this first: three corrections, all machine-checked

**0. `SortUniq` is now a theorem, relative to Π-injectivity alone.**
`Theory/Typing/UniqSort.lean`'s `VEnv.WF.sortUniq'` proves `env.SortUniq U` for every
`VEnv.WF` environment, with `IsDefEqU.forallE_inv_stratified` as the *only* open input —
`IsDefEqU.sort_inv` is not in its cone.  The route is to carry universe uniqueness **as an
extra conjunct in `IsDefEq.uniq`'s own induction invariant** rather than to import it; all
eight of `uniq`'s appeals to `sort_inv` are applied to its own induction hypothesis, so the
conjunct replaces them.  So the two paragraphs below still describe the statement correctly,
but "nothing in this repository exhibits one" is **superseded**: `propLoop_sortUniq`
exhibits one at `CycleConv.propLoopEnv`.

**1. `SortUniq` as stated below is FALSE.**  It carries no hypothesis on `env`, and one
definitional-equality rule `.sort .zero ≡ .sort .zero : .sort 2` refutes it —
`VEnv.sortUniq_badEnv` (`Theory/Typing/SortUniqDown.lean`).  All three guards discussed under
"Two guards" hold at that witness; the missing guard is on the *environment*, not on the
context or the levels.  It is a missing-guard defect and not a refutation of the intended
fact: `VEnv.badEnv_not_wf` machine-checks that the witness environment is not `VEnv.WF`, by
the already-proved `VEnv.WF.instL_lhs_ne_sort`.  The statement that can be targeted is
`∀ env, env.WF → env.SortUniq U`, which is what `SortUniqFacts.WF.sortUniq` states, what
`UniqSort.WF.sortUniq'` proves, and what every consumer can supply.  The definition is left
unguarded because `Typing/CycleConv.lean` (another stream's file) takes it as a hypothesis.

**2. `SortUniq` implies `IsDefEqU.sort_inv`.**

**1. `SortUniq` as stated below is FALSE.**  It carries no hypothesis on `env`, and one
definitional-equality rule `.sort .zero ≡ .sort .zero : .sort 2` refutes it —
`VEnv.sortUniq_badEnv`.  All three guards discussed under "Two guards" hold at that witness;
the missing guard is on the *environment*, not on the context or the levels.  It is a
missing-guard defect and not a refutation of the intended fact: `VEnv.badEnv_not_wf`
machine-checks that the witness environment is not `VEnv.WF`, by the already-proved
`VEnv.WF.instL_lhs_ne_sort`.  The statement that can be targeted is
`∀ env, env.WF → env.SortUniq U`, which is what `SortUniqFacts.WF.sortUniq` states and what
every consumer can supply.  The definition is left unguarded because
`Typing/CycleConv.lean` (another stream's file) takes it as a hypothesis.

`VEnv.sort_inv_of_sortUniq` (`Theory/Typing/SortUniqDown.lean`) derives sort injectivity from `SortUniq` alone, `sorryAx`-free
and with no normalisation argument: `IsDefEqU` is type-indexed, so a conversion
`.sort u ≡ .sort v` hands over one type `A` inhabited by both endpoints, and `SortUniq`
applied twice (once through `HasTypeStrong.sort_type` below) finishes.  `sort_inv`'s `trans`
case is never reached.

So the two obligations `Injectivity.lean` names — `sort_inv`'s `trans` and `SortUniq` — are
not independent: the second subsumes the first.  With `SortUniqFacts.WF.sortUniq` this gives
the sandwich (`UniqTy`, `SortInv` are the hypothesis-packaged forms in `SortUniqDown.lean`)

    UniqTy ∧ SortInv  →  SortUniq  →  SortInv

so `SortUniq` and `sort_inv` are the same statement *modulo unique typing* — and correction 0
supplies the unique typing.  **Neither is the thing to target: the whole corner bottoms out
at `IsDefEqU.forallE_inv_stratified`.**  `docs/handoff-sortuniq.md` has the measurements.

## The model route to `SortUniq` is closed, and to `SortInv` it is open and EXACT

**CORRECTION (2026-08-31).**  This section used to be headed "There is no model route to
`SortUniq`" and to close with a note that it was "the one claim in this file that is not
machine-checked".  Both are now out of date, in opposite directions:

* The negative half **is** machine-checked, and by a sharper route than the cumulativity
  sketch below.  `hasChains_refutes_levelSeparating` (`Theory/SemanticRouteClosed.lean:235`)
  proves that `LevelSeparating` — the model property that was supposed to deliver `SortUniq`
  — is *false* in any model with chains, i.e. in the intended one.  `SortUniq` is measured
  **dead** semantically, not merely unproven.
* But the model is **not** useless here, and saying "no model route" was too strong.  What
  survives is `U_injOn` and `semantic_sortInv` — the model settles `SortInv` *where it can see
  the conversion*.  Combined with the implication chain above
  (`UniqTy ∧ SortInv → SortUniq → SortInv`), the gap the model leaves includes **unique
  typing**, which is syntactic.

  **CORRECTION (later the same day, and this one is mine).**  The line above used to read: "What
  the model delivers is `SortInv`, exactly: `sortEqRaw_iff` is an `iff`, so the semantic side of
  this corner is *finished*, not approximated."  That over-read the `iff`.  `sortEqRaw_iff` is
  about `SortEqRaw`, which mentions **no context and no valuation `ρ`**, so it never certified
  `SortEqSupply` — the statement `semantic_sortInv` and `semantic_sortInv_packaged` actually
  consume.  And the packaged form of that supply is **vacuous**: `sortInvSupply_vacuous`
  (`Theory/Typing/InjSortPiModel.lean`) proves its hypothesis false for *every* `env` and every
  `nv`, because `interpCtx` has no valuation for the perfectly legitimate context
  `[∀ p : Prop, p]` — its denotation is `∅` in every model, on both branches of the proof split —
  while reflexivity of `.sort .zero` supplies a conversion there anyway.

  So the semantic side of this corner is **not** finished.  Every semantic route into it owes a
  **valuation obligation** for the context the judgement lives in.  That debt is not
  level-flavoured, no instrument in this tree sees it, and `docs/vacuity-ledger.md` rows 23–24 are
  its first measurement.

The cumulativity argument below remains correct and is kept as the intuition.

**`SortUniq` is not a semantic consequence of Lean's rules**, so no argument from
`Theory/SetModel/` — or from any model — can establish it.  The check is short:

* Add a cumulativity rule `Γ ⊢ e : .sort u → u ≤ v → Γ ⊢ e : .sort v`.  Any model whose
  universes are nested validates it — the standard construction, and the one
  `~/lean-type-theory/soundness.tex` builds from n-inaccessibles.
* In the resulting system `SortUniq` is **false**, guards and all: take `Γ = []`,
  `e = .sort .zero`, `u = .succ .zero`, `v = .succ (.succ .zero)`.  `OnCtx [] _` holds
  trivially, both levels are `WF` at any `U` (no parameters), the first typing is the `sort`
  rule and the second is cumulativity — and `1 ≉ 2`.

So `SortUniq` separates Lean from a system its own models also satisfy.  It holds *because
Lean has no cumulativity*, which is a syntactic fact about the rule set, and only a syntactic
argument can reach it.

**What this costs the plans that name `SortUniq`.**  It has been described in this repo as
the highest-value obligation, with four independent consumers.  Three of them — this file's
inversion cone, a confluence development, and `IsDefEq.uniq` — are syntactic and are
unaffected.  The fourth is not: `SetModel/Interp.lean`'s `LevelAssign.srt_sound` **is**
`SortUniq` restated, so it cannot be discharged by a semantic argument *inside* the model
development either.  It has to arrive from the syntactic side.  The model development should
carry it as an import, and nobody should spend a session deriving it semantically — the
request is unanswerable in principle, not merely hard.

**The useful half of the same check — and its conclusion is RETRACTED.**  `sort_not_proof`
below — currently *derived* from `SortUniq` — **does** survive cumulativity, which produces
`.sort u : .sort v` and never `.sort u : p : Prop`.  This paragraph used to continue: "so the
model route is closed for `SortUniq` and open for `sort_not_proof`, and `sort_not_proof` is the
statement worth asking the model stream for."  **That inference is invalid and the conclusion is
false.**  Surviving a negative check means a model cannot *refute* the statement; it does not
follow that a model can *prove* it.  The model route to `sort_not_proof` is measured **closed**:
`Theory/SetModel/NotProofNoModel.lean`'s `sortNotProof_of_propSplit` obtains `sort_not_proof`
from `PropSplit` with **no interpretation at all**, so the semantic construction is strictly
dominated by its own hypothesis and building it to get `sort_not_proof` is circular
(`ORCHESTRATOR.md`, "The model route to `sort_not_proof` is CLOSED"; independently prefigured in
prose by `Theory/Typing/UniqueTypingN.lean`'s `PropTypeAgreeN` section).  Do not ask the model
stream for `sort_not_proof`; the live semantic target is `PropTypeAgreeN`, and its own primitive
is `SortForallEDisjoint`.

`sort_not_proof` remains the statement two of `unique.tex`'s three uses of unique typing reduce
to (`docs/options-circularity-breakers.md`) — that part stands.

**And it is not the only way to pay hole B's transport tax.**  The reading that made an
*independent* `sort_not_proof` the sole route to cashing in the five-conjunct decomposition of
`WF.rigidShapeUniqNS` (`docs/vacuity-ledger.md` row 30) is too pessimistic:
`Theory/Typing/InjSpineTransport.lean` shows the `ProofTransport` that
`RigidNodeCircle.rigidShapeUniqNS_of_family` consumes is only ever instantiated at a *constant
spine*, and that restricted form follows from `ConvPiInv` alone — hence from `ConvStep2 ∧ PiInv`,
with no `SortUniq`, no `SortInv` and no `sort_not_proof`.

**The model USED to be parameterised on it — that circularity is fixed.**  `Theory/SetModel/`
once carried `(L : LevelAssign env nv)` through every section of `InterpSound.lean` with
nothing constructing one, and `LevelAssign.srt_sound` *is* `SortUniq` restated.  So the
parameter contained the very hole the model was being used to fill.  This is now
machine-checked rather than argued: `levelAssign_gives_sortUniq`
(`Theory/SemanticRouteClosed.lean:136`) derives `SortUniq` from a `LevelAssign` outright.

It is also **repaired**.  The live parameter is `PropSplit`
(`Interp.lean:408`, `:462`, and every section of `InterpSubst.lean`, `Cnst.lean`,
`CnstRecursion.lean`, `FalseProp.lean`), which is exactly the proof-splitting criterion this
paragraph asked for: it does not require a canonical level per term.  `LevelAssign` survives
only in `Interp.lean`'s legacy section at :285.

Recorded as row 7 of `docs/vacuity-ledger.md`, where it is the entry for a failure mode no
instrument in this repo can see: **a cone cannot see a hypothesis**, so a parameter that
assumes its own conclusion registers as zero holes and zero axioms.

*The cumulativity sketch above is analysis, not a Lean proof; making that particular argument
rigorous would cost a scratch copy of `IsDefEq` with the cumulativity rule added and a re-run
of the model's soundness proof.  It is no longer worth doing, because the stronger negative
result is already machine-checked: see `hasChains_refutes_levelSeparating`.*

## Two guards, and why they are there

`SortUniq` carries `OnCtx Γ (env.IsType U)` and `WF U` on both levels.  Neither is
decoration.  `SetModel/LevelAssignUnsat.lean` machine-checks that the *unguarded* analogue
of this condition — `LevelAssign`'s original `lvl_sound` — is not merely unproved but
**unsatisfiable for every environment**: `IsDefEq.bvar` has no side condition, so a context
may hold `.sort (.param U)` and derive `Γ ⊢ .bvar 0 : .sort (.param U)`, a level no `WF U`
level is equivalent to.  Guarding is what keeps this hypothesis from being empty for a
reason that has nothing to do with the mathematics.  Both consumers below have the guards
available for free.

`Theory/Typing/SortUniqFacts.lean` machine-checks the other direction: `SortUniq` follows
from `IsDefEq.uniq` and `IsDefEqU.sort_inv`.  So assuming it is not assuming anything beyond
the family it is used to attack — it is an *upper* bound on the hypothesis's strength, and
the reason to believe it is satisfiable at all.
-/

namespace Lean4Lean
namespace VEnv

/-- **Universe uniqueness.**  Two sorts inhabited by the same type agree.

Equivalently `IsDefEq.uniq` composed with `IsDefEqU.sort_inv`, restricted to sorts — but
stated separately because both of those are downstream of, or equal to, the statements this
is used to attack. -/
def SortUniq (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e : VExpr} {u v : VLevel},
    OnCtx Γ (env.IsType U) → u.WF U → v.WF U →
    env.HasType U Γ e (.sort u) → env.HasType U Γ e (.sort v) → u ≈ v

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {u v : VLevel} {p : VExpr} {b : Bool}

/-- **The type of a sort is a sort, one level up** — granted universe uniqueness.

Without `huniq` this is *not* routine, contrary to how it reads.  The induction's `defeq`
case has the equation `A ≡ B` at the level the derivation chose and the inductive hypothesis
at the level `A` was found to inhabit, and retyping either to the other is exactly
`huniq`. -/
theorem HasTypeStrong.sort_type (huniq : env.SortUniq U) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasTypeStrong U Γ (.sort u) p b) :
    ∃ u' w, u ≈ u' ∧ w.WF U ∧ env.IsDefEq U Γ (.sort (.succ u')) p (.sort w) := by
  generalize eq : VExpr.sort u = e at H
  induction H with cases eq
  | sort' _ h2 h3 =>
    -- `w` must be pinned by the equation, not by the `WF` slot: `(w.succ.succ).WF` and
    -- `w.WF` are definitionally equal, so unifying on the `WF` slot first picks the wrong `w`.
    refine ⟨_, _, h3, ?_, IsDefEq.sortDF h2 h2 rfl⟩
    exact h2
  | base _ ih => exact ih hΓ rfl
  | defeq hu hAB hA _ _ _ _ ih3 =>
    obtain ⟨u', w, h1, hw, h2⟩ := ih3 hΓ rfl
    exact ⟨u', w, h1, hw,
      h2.trans (.defeqDF (.sortDF hu hw (huniq hΓ hu hw hA.hasType h2.hasType.2)) hAB.defeq)⟩

/-- **A sort is not a proof** — granted universe uniqueness.

This is the `proofIrrel` case of `IsDefEqU.sort_inv`.  The argument is Carneiro's
(`~/lean-type-theory/unique.tex:266`): `p` would have to be both `.sort .zero` and
`.sort (u+2)`, and `0 ≈ u+2` is false at any valuation. -/
theorem sort_not_proof (huniq : env.SortUniq U) (henv : Ordered env)
    (hΓ : OnCtx Γ (env.IsType U))
    (hp : env.HasType U Γ p (.sort .zero)) (hu : env.HasType U Γ (.sort u) p) : False := by
  obtain ⟨u', w, _, hw, h2⟩ := ((hu.strong henv hΓ).hasType'.1).sort_type huniq hΓ
  have hw0 : w ≈ VLevel.zero := huniq hΓ hw trivial h2.hasType.2 hp
  have hu' : (VLevel.succ u').WF U := h2.sort_inv_l henv
  have hw2 : w ≈ (VLevel.succ (VLevel.succ u')) :=
    huniq hΓ hw (by exact hu') h2.hasType.1 (HasType.sort (by exact hu'))
  have := hw0.symm.trans hw2
  exact absurd (congrFun this []) (by simp [VLevel.eval])

/-! ## The lower bound: `SortUniq → sort_inv` -/

/-- **`SortUniq` implies sort injectivity**, with no normalisation argument.

This is `IsDefEqU.sort_inv`'s exact statement (`Theory/Typing/Injectivity.lean`), whose two
open cases are `trans` — "a term convertible with a sort reduces to a sort" — and
`proofIrrel`.  Neither is touched here: the argument never inspects the conversion
derivation at all.  It uses only that `IsDefEq` is **type-indexed**, so the conversion hands
over one type `A` inhabited by both sorts, and then `SortUniq` twice.

`#print axioms Lean4Lean.VEnv.sort_inv_of_sortUniq` reports no `sorryAx`. -/
theorem sort_inv_of_sortUniq (huniq : env.SortUniq U) (henv : Ordered env)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := by
  obtain ⟨A, H⟩ := H
  have hu : env.HasType U Γ (.sort u) A := H.trans H.symm
  have hv : env.HasType U Γ (.sort v) A := H.symm.trans H
  have hvwf : v.WF U := H.sort_inv_r henv
  -- `A`, the type shared by both endpoints, is convertible to a sort — this is the step
  -- that needs `huniq` (`HasTypeStrong.sort_type`, `SortUniq.lean`).
  obtain ⟨u', w, huu', hw, h2⟩ := ((hu.strong henv hΓ).hasType'.1).sort_type huniq hΓ
  have hsu' : (VLevel.succ u').WF U := h2.sort_inv_l henv
  -- Now `.sort v` inhabits both `.sort (.succ u')` and `.sort (.succ v)`; `huniq` again.
  have key : VLevel.succ u' ≈ VLevel.succ v :=
    huniq hΓ hsu' (by exact hvwf) (IsDefEq.defeqDF h2.symm hv) (HasType.sort hvwf)
  exact huu'.trans (VLevel.succ_congr_iff.1 key)

end VEnv
end Lean4Lean
