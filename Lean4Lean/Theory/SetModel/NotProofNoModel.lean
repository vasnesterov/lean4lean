import Lean4Lean.Theory.SetModel.FalseProp
import Lean4Lean.Theory.Typing.NotProof
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# The model cannot be the source of `sort_not_proof`

**This file is the answer to "get `VEnv.SortUniq` or `sort_not_proof` from the semantic
side", and the answer is no — not because the semantic argument is hard, but because the
model's own parameter already implies the conclusion by pure syntax.**  Everything below is
machine-checked; §2 is the closure result and §4 is the transfer obstruction.

## The brief's premise, corrected

`Theory/Typing/SortUniq.lean` observes that `SortUniq` is refuted by adding cumulativity,
which every nested-universe model validates, and concludes that no model route to `SortUniq`
exists.  It then adds that `sort_not_proof` **does** survive cumulativity, and suggests it
"is the statement worth asking the model stream for".

The first half is right and is unaffected by anything here.  The second half is a
non-sequitur, and this file is where it is paid for: *surviving cumulativity* means only
that a model **cannot refute** `sort_not_proof`.  It says nothing about a model **proving**
it, and the two questions have different answers.

## 1. The right target is `PropTypeAgree`, not `SortUniq`

`SetModel/PropSplitAudit.lean` already contains the statement that `sort_not_proof` is an
instance of: `VEnv.PropTypeAgree`, "the types of a term agree on being propositions".  §1
below proves

    PropTypeAgree  →  sort_not_proof                (`sortNotProof_of_propTypeAgree`)
    PropTypeAgree  →  forallE_not_proof             (`forallENotProof_of_propTypeAgree`)

`sorryAx`-free, and with `SortUniq` **nowhere in the hypotheses** — which is a genuine
strengthening of `Theory/Typing/SortUniq.lean`'s `sort_not_proof` and
`Theory/Typing/NotProof.lean`'s `forallE_not_proof`, both of which take `env.SortUniq U`.
The derivation is three lines: instantiate `PropTypeAgree` at `e := .sort u`, whose two
types are the proposition `p` and the canonical `.sort (.succ u)`, and read off
`0 = 0 ↔ u + 2 = 0`.

Also note what the new proofs *drop*: `sort_not_proof` needs `OnCtx Γ` and
`HasTypeStrong.sort_type` (an induction that needs `SortUniq` in its `defeq` case);
`sortNotProof_of_propTypeAgree` needs neither, only `Ordered env` for `sort_inv_l`.

## 2. The model's parameter *is* the syntactic import (the closure result)

`SetModel/Interp.lean`'s `PropSplit` is the parameter that every model statement in the tree
is quantified over: `interp`, `Sound`, `soundAbove`, `sound_nil`, `interp_falseProp`, all of
them take `L : PropSplit envF nv`.  Its `proof_sound` field is a **biconditional** between a
predicate of `(ls, Γ, e)` and `u.eval ls = 0` for *every* type `A` of `e`.  Two instances of
one biconditional at the same left-hand side compose, and what they compose to is
`PropTypeAgree` verbatim:

    propTypeAgree_of_propSplit :  PropSplit env nv  →  env.PropTypeAgree nv
    propUniq_of_propSplit     :  PropSplit env nv  →  env.PropUniq nv

Together with `PropSplitAudit.exists_propSplit` (the converse) this is an **equivalence**:

    nonempty_propSplit_iff_agree : Nonempty (PropSplit env nv) ↔ PropUniq env nv ∧ PropTypeAgree env nv

So the audit's §3 "lower bound — satisfiability *reduces to* two named syntactic statements"
is not a reduction with slack: it is an equality of content.  And composing with §1:

    sortNotProof_of_propSplit :  PropSplit env nv  →  Ordered env  →  ¬ (a sort is a proof)

*with no interpretation, no `SetStructure`, no ZFC, no chain of inaccessibles, and no
`Stable`.*  Any model argument for `sort_not_proof` must first exhibit an `L`, and the mere
existence of `L` gives the conclusion by the four-line syntactic route above.  **The
semantic construction is therefore strictly dominated: it cannot prove anything about
`sort_not_proof` that its own hypothesis does not already prove more cheaply.**  That is the
precise sense in which the model route is closed, and it is a theorem, not an impression.

**Prior art in this repo, and the credit belongs there.**  This conclusion was already stated
as prose in `Theory/Typing/UniqueTypingN.lean` §"Is `PropTypeAgreeN` closable at the index?":
"the model route is closed for a different reason: `Theory/SetModel/` is parameterised on
`LevelAssign` … and a cut-down model bottoms out at `sort_not_proof` — which is
`PropTypeAgreeN` at a sort".  What is new here is only that the statement is now
machine-checked, at the re-parameterised `PropSplit` rather than at `LevelAssign`, and as an
*equivalence* rather than an implication.  Two independent derivations agreeing is the point;
the discovery is not.

## 3. The published reference agrees, and says so explicitly

`~/lean-type-theory/soundness.tex:34` opens the interpretation with

> "An important consequence of **unique typing** is the lvl and sort functions on well typed
> types and terms, respectively"

and `soundness.tex:290` discharges the compatibility case of the soundness theorem with

> "When a case split on `⟦ℓ⟧=0` is done, **by unique typing** it must be the same for both
> sides."

Those two are exactly `PropUniq` and `PropTypeAgree` (the `lvl`/`sort` functions are the
stronger `LevelAssign` form of the same input).  Carneiro's dependency order is
`unique.tex` → `soundness.tex`, and his proof of "a sort is not a proof"
(`unique.tex:266`, the `proofIrrel` sub-case of definitional inversion at `n+1`) is
**syntactic** and appeals to *unique typing at `n`* — the stratified induction this repo is
already running.  There is no model argument for it in the reference, and the reference's
model could not host one.

## 4. The transfer obstruction, machine-checked

Suppose §2 were circumvented (a `PropSplit` built by a syntactic recursion mirroring
`inferType`, which `SetModel/StableAudit.lean` floats).  The transfer would still fail, and
§4 below is the reason in one lemma.

Soundness is `Sound M L Γ e₁ e₂ A`, whose every field is `∀ ρ ∈ interpCtx M L Γ, …`.  At a
context with an uninhabited entry there is no such `ρ`, so **every field holds vacuously,
for arbitrary `e₁ e₂ A`, with no typing premise at all**:

    sound_of_interpCtx_empty     : (∀ ρ, ρ ∉ interpCtx M L Γ) → Sound M L Γ e₁ e₂ A
    sound_falseProp_ctx_trivial  : Sound M L [falseProp] e₁ e₂ A

The second is unconditional — `interp_falseProp` (`SetModel/FalseProp.lean`) gives
`⟦∀ p : Prop, p⟧ ∅ = ∅` with no hypotheses, so `interpCtx M L [falseProp]` is empty.
Consequently the total semantic information available at `Γ = [falseProp]` is `True`, and
any implication `Sound M L [falseProp] … → X` is a proof of `X` outright.

That matters because `sort_not_proof` is consumed at **arbitrary** contexts: every call site
in `Theory/Typing/Injectivity.lean` supplies only `hΓ : OnCtx Γ (env.IsType U)`, which
`[falseProp]` satisfies (`falseProp` is a type).  So the one instance the semantic argument
would need is exactly an instance at which the semantics says nothing.

Closing over the context does not rescue it either.  Abstracting `Γ ⊢ .sort u : p` to
`[] ⊢ λΓ. .sort u : ΠΓ. p` moves the instance to the empty context, where `interpCtx` is
`{∅}` — but the term is then a `lam`, not a sort, so the semantic obligation is no longer
"`U κ m ≠ pt`" (which is true and proved below, `U_ne_pt`) but "`pt` is not an element of
any set in `U κ (k+1)`" (which is **false**: `pt ∈ {pt} ∈ U κ 0 ⊆ U κ (k+1)` by `U_mono`,
and that is precisely why cumulativity is semantically valid).  So the shape that has a
provable semantic obligation is stuck at the wrong context, and the shape that reaches the
right context has no provable semantic obligation.

§4b discharges the sort-shaped obligation outright, so the diagnosis is not "the semantic
argument is hard": `sortDenot_not_mem_propDenot` is the whole of `sort_not_proof` **at one
valuation**, proved with no unique typing and no confluence.  What is missing is only the
quantifier, and §4 is the machine-checked statement that the quantifier is empty exactly
where the hole is consumed.

## Where a free `PropTypeAgree` would land

For anyone pricing the remaining target, the route out of the corner is (attributions are
exact, because two of the steps are other files' prose and not machine-checked):

* `PropTypeAgree → sort_not_proof` and `→ forallE_not_proof`, dropping both `SortUniq` and
  `OnCtx Γ` — §1 below, machine-checked.  This is a *strengthening* of
  `Typing/SortUniq.lean`'s `sort_not_proof` and `Typing/NotProof.lean`'s
  `forallE_not_proof`, which both take `huniq : env.SortUniq U` and `hΓ`.
* `sort_not_proof` from an independent source `→ sort_inv`, using `WF.rigidShapeUniq` alone.
  This is `Typing/PiLevelPin.lean`'s closing note (§"Where the demand actually comes from"),
  stated there as prose; it is **not** machine-checked, and the file's own machine-checked
  route to `sort_inv` (`sort_inv_of_sortUniq`) still goes through `SortUniq` wholesale.
* `sort_inv` (+ `piInv_axiom`, a theorem modulo `rigidShapeUniq`) `→ SortUniq`, and
  `PiLevelPin.piInvStratApp_iff_sortUniq` identifies `SortUniq` with
  `forallE_inv_stratified` itself.

So `PropTypeAgree` — *not* `sort_not_proof`, and *not* `SortUniq` — is the sharp remaining
target in this direction.  §2 is the reason it cannot come from the model: the model's own
parameter is equivalent to it (`nonempty_propSplit_iff_agree`).

## 5. Where the residual value is: the missing context guard

`PropUniq` and `PropTypeAgree` are stated with **no hypothesis on `Γ`** — not `OnCtx`, not
`CtxClosed`.  Every unique-typing result in this tree carries `OnCtx Γ (env.IsType U)`
(`IsDefEq.uniq`, `uniqU`, `IsDefEqU.sort_inv`, `WF.sortUniq'`, …), because the inductions
need the context's entries to be types.  So as stated the model's syntactic import is *not*
implied by the syntactic development's own goal, and this is the same missing-guard shape
that `SetModel/LevelAssignUnsat.lean` caught twice.

§5 proves the guarded form outright:

    WF.propTypeAgreeOn : env.WF → OnCtx Γ (env.IsType nv) → (the PropTypeAgree conclusion)
    WF.propUniqOn      : env.WF → OnCtx Γ (env.IsType nv) → (the PropUniq conclusion)

from `IsDefEq.uniqU` and `IsDefEqU.sort_inv`.  These are `sorryAx`-tainted through the
tree's existing holes and add none of their own; the point is not that they are free but
that **the guarded import costs nothing beyond what the syntactic corner is already
targeting**, while the unguarded import is an extra, unpaid-for statement about junk
contexts.

The gap between them is *strengthening*: an unguarded `Γ` differs from a guarded one by
entries that the derivation never looks up, and removing those is `IsDefEqU.weakN_iff`
(`Theory/Typing/UniqueTyping.lean`, one of the tree's 14 holes).  `PropTypeAgreeOnCtx` below
names the guarded statement so the model stream can import it, and
`propTypeAgree_of_onCtx_of_strengthen` states the exact bridge as a hypothesis-shaped
lemma.

**Recommended repair**: add `OnCtx Γ (env.IsType nv)` to `PropSplit.prop_sound` and
`PropSplit.proof_sound`, and carry `OnCtx` instead of (or beside) `CtxClosed` in
`soundAbove`'s induction — the induction already builds `⟨hΓ, _, h.hasType⟩` at every binder,
which is exactly `OnCtx`'s cons.  With that, `PropSplit`'s residual syntactic import becomes
`WF.propUniqOn` + `WF.propTypeAgreeOn` below, i.e. *nothing new*.

**Measured cost of that repair, because an earlier version of this paragraph implied it was
local, and it is not.**  No file here is owned by another stream — `Interp.lean`,
`PropConv.lean` and `RegPiSat.lean` are all freely editable — but the edit is a cascade, not a
local change:

* `soundAbove` itself is cheap: four `have hΓA : CtxClosed (A :: Γ) := ⟨hΓ, hclA⟩` lines
  become `OnCtx` conses, and `ctxClosed_of_isType` (already in `SoundInduction.lean`, just
  below `soundAbove`) recovers the `CtxClosed` the other cases still use.  The entry point
  `SoundInduction.sound` already *has* the `OnCtx` and currently throws it away.
* The cost is at the **consumers of the two fields**, which reach them through `isProp_iff` /
  `isProof_iff`: **64 call sites**, about forty of them in `SetModel/QuotInterp.lean` at
  hand-built contexts such as `[.bvar 1, quotRelTy, .sort u]`.  Each one would have to
  discharge a fresh `OnCtx Γ (env.IsType nv)` obligation for its own context, and those
  obligations are not currently proved anywhere.
* So the repair is real and worth doing, but it is a `QuotInterp`-sized job with a
  `PropSplit`-signature flag day in the middle, not the few lines the paragraph above
  suggests.  Priced here so that it is funded deliberately.

## Axiom check

`#print axioms` reports a subset of `[propext, Classical.choice, Quot.sound]` — in
particular **no `sorryAx`** — for
`sortNotProof_of_propTypeAgree`, `forallENotProof_of_propTypeAgree`,
`propTypeAgree_of_propSplit`, `propUniq_of_propSplit`, `nonempty_propSplit_iff_agree`,
`sortNotProof_of_propSplit`, `not_mem_interpCtx_falseProp`, `sound_of_interpCtx_empty`,
`sound_falseProp_ctx_trivial`, `U_ne_pt`, `sortDenot_not_mem_propDenot`,
`propTypeAgree_equivZero`, `propAgree_pointwise_not_from_equivZero`, `isType_falseProp`
and `onCtx_falseProp`.  Only §5's two lemmas are tainted, through
`IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniq`, and they add no `sorry`; the
census is unchanged by this file.
-/

namespace Lean4Lean

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-! ## 1. `sort_not_proof` from `PropTypeAgree`, without `SortUniq` -/

/-- **A sort is not a proof — granted `PropTypeAgree` rather than `SortUniq`.**

The same conclusion as `Theory/Typing/SortUniq.lean`'s `VEnv.sort_not_proof`, from a
strictly weaker hypothesis (`SetModel/PropSplitAudit.lean`'s `PropTypeAgree`) and with the
`OnCtx Γ` premise dropped.  `Ordered env` survives only to run `sort_inv_l`.

The two types of `.sort u` are the proposition `p` and the canonical `.sort (.succ u)`,
whose own sorts are `.zero` and `.succ (.succ u)`; `PropTypeAgree` says those agree on being
zero, and `u + 2 ≠ 0`. -/
theorem sortNotProof_of_propTypeAgree (hT : env.PropTypeAgree nv) (henv : env.Ordered)
    {Γ : List VExpr} {u : VLevel} {p : VExpr}
    (hp : env.HasType nv Γ p (.sort .zero))
    (hup : env.HasType nv Γ (.sort u) p) : False := by
  have hu : u.WF nv := hup.sort_inv_l henv
  have h1 : env.HasType nv Γ (.sort u) (.sort (.succ u)) := HasType.sort hu
  have h2 : env.HasType nv Γ (.sort (.succ u)) (.sort (.succ (.succ u))) :=
    HasType.sort (show (VLevel.succ u).WF nv from hu)
  have key := hT (ls := []) (u := .zero) (u' := .succ (.succ u)) trivial
    (show (VLevel.succ (.succ u)).WF nv from hu) hup h1 hp h2
  simp [VLevel.eval] at key

/-- **A Π is not a proof — granted `PropTypeAgree` rather than `SortUniq`.**

The mirror of the above, and of `Theory/Typing/NotProof.lean`'s `forallE_not_proof`.  Where
that lemma recovers the Π's canonical typing from `HasTypeStrong.forallE_type` (an induction
whose `defeq` case is where `SortUniq` is spent), this one takes the domain and codomain
typings as premises — which is what every call site has, since they are the premises that
made the Π well-formed in the first place. -/
theorem forallENotProof_of_propTypeAgree (hT : env.PropTypeAgree nv)
    {Γ : List VExpr} {A B p : VExpr} {u v : VLevel} (hu : u.WF nv) (hv : v.WF nv)
    (hA : env.HasType nv Γ A (.sort u)) (hB : env.HasType nv (A::Γ) B (.sort v))
    (hp : env.HasType nv Γ p (.sort .zero))
    (hf : env.HasType nv Γ (.forallE A B) p) : False := by
  have h1 : env.HasType nv Γ (.forallE A B) (.sort (.imax u v)) := IsDefEq.forallEDF hA hB
  have h2 : env.HasType nv Γ (.sort (.imax u v))
      (.sort (.succ (.imax u v))) := HasType.sort ⟨hu, hv⟩
  have key := hT (ls := []) (u := .zero) (u' := .succ (.imax u v)) trivial
    (show (VLevel.succ (.imax u v)).WF nv from ⟨hu, hv⟩) hf h1 hp h2
  simp [VLevel.eval] at key

end VEnv

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 2. The model's parameter is exactly the syntactic import -/

section Circle

variable {env : VEnv} {nv : ℕ}

/-- **`PropSplit` implies `PropTypeAgree`.**  `proof_sound` is a biconditional whose
left-hand side does not mention the type; two instances at the same term compose.

This is the converse `SetModel/PropSplitAudit.lean` did not state, and it is what makes the
model route to `sort_not_proof` circular. -/
theorem propTypeAgree_of_propSplit (L : PropSplit env nv) : env.PropTypeAgree nv :=
  fun hw hw' he he' hA hA' =>
    (L.proof_sound hw he hA).symm.trans (L.proof_sound hw' he' hA')

/-- **`PropSplit` implies `PropUniq`**, by the same composition on `prop_sound`. -/
theorem propUniq_of_propSplit (L : PropSplit env nv) : env.PropUniq nv :=
  fun hw hw' hA hA' => (L.prop_sound hw hA).symm.trans (L.prop_sound hw' hA')

/-- **The audit's lower bound is an equivalence.**  `PropSplitAudit.exists_propSplit` builds
a `PropSplit` from `PropUniq ∧ PropTypeAgree`; the two lemmas above recover them.  So the
model's parameter carries *exactly* the content of the two syntactic statements — no slack in
either direction. -/
theorem nonempty_propSplit_iff_agree :
    Nonempty (PropSplit env nv) ↔ env.PropUniq nv ∧ env.PropTypeAgree nv :=
  ⟨fun ⟨L⟩ => ⟨propUniq_of_propSplit L, propTypeAgree_of_propSplit L⟩,
   fun ⟨h1, h2⟩ => exists_propSplit h1 h2⟩

/-- **The closure result: the model route is strictly dominated.**

From the model's parameter alone — no `interp`, no `SetStructure`, no ZFC, no chain of
inaccessibles, no `Stable` — `sort_not_proof` follows by §1.  So a semantic proof of
`sort_not_proof` would be a proof from a hypothesis that already implies it by four lines of
syntax, which is no progress on the hole.

This is the machine-checked form of "a model is not a candidate source for
`sort_not_proof`". -/
theorem sortNotProof_of_propSplit (L : PropSplit env nv) (henv : env.Ordered)
    {Γ : List VExpr} {u : VLevel} {p : VExpr}
    (hp : env.HasType nv Γ p (.sort .zero))
    (hup : env.HasType nv Γ (.sort u) p) : False :=
  VEnv.sortNotProof_of_propTypeAgree (propTypeAgree_of_propSplit L) henv hp hup

end Circle

/-! ## 4. The transfer obstruction: soundness is vacuous where the hole is consumed -/

section Vacuous

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

/-- **Soundness is free at a context no valuation satisfies.**  Both fields of `Sound` are
`∀ ρ ∈ interpCtx M L Γ, …`, so an empty `interpCtx` discharges them for *arbitrary*
`e₁ e₂ A` — no typing premise, no well-formedness, nothing. -/
theorem sound_of_interpCtx_empty {Γ : List VExpr} (h : ∀ ρ : V, ρ ∉ interpCtx M L Γ)
    {e₁ e₂ A : VExpr} : Sound M L Γ e₁ e₂ A :=
  ⟨fun ρ hρ => absurd hρ (h ρ), fun ρ hρ => absurd hρ (h ρ)⟩

/-- **`[∀ p : Prop, p]` is an uninhabited context.**  `interp_falseProp` gives
`⟦falseProp⟧ ∅ = ∅` unconditionally, and the only valuation of the empty context is `∅`. -/
theorem not_mem_interpCtx_falseProp (ρ : V) : ρ ∉ interpCtx M L [falseProp] := by
  intro h
  obtain ⟨ρ₀, hρ₀, v, hv, rfl⟩ := (mem_interpCtx_cons M L).mp h
  rw [interpCtx_nil] at hρ₀
  rcases mem_singleton_iff.mp hρ₀ with rfl
  rw [interp_falseProp] at hv
  simp at hv

/-- **The semantic content available at `Γ = [falseProp]` is `True`.**

Every soundness conclusion holds there for arbitrary `e₁ e₂ A`, so any implication
`Sound M L [falseProp] … → X` is a proof of `X` outright.  `sort_not_proof` is consumed at
arbitrary `OnCtx` contexts, `[falseProp]` is one of them, and this is why a model argument
cannot reach it even if §2's circularity were circumvented. -/
theorem sound_falseProp_ctx_trivial {e₁ e₂ A : VExpr} :
    Sound M L [falseProp] e₁ e₂ A :=
  sound_of_interpCtx_empty not_mem_interpCtx_falseProp

end Vacuous

/-! ## 4b. The *semantic* half of "a sort is not a proof" is discharged

§4 says the obstruction is the transfer, not the semantics.  That claim is only worth
something if the semantic obligation is actually provable, so here it is.  A sort denotes a
universe (`interp_sort`), and no universe of the sequence is `•`; hence a sort's denotation
is never an element of a `Prop`'s denotation.  This is `sort_not_proof`'s content *at a
single valuation* — and it needs no unique typing, no `SortUniq`, no confluence.

What is missing is only the quantifier: to conclude the syntactic statement one needs the
instance at *some* valuation of the context in which the hole is consumed, and §4 shows that
at `[falseProp]` there is none. -/

section SemanticObligation

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

/-- **No universe of the sequence is `•`.**  `U κ 0 = ℘ {•}` contains `∅`, and
`U κ (j+1)` contains `U κ 0`; either way the universe is nonempty, while `• = ∅`. -/
theorem U_ne_pt {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ) {m : ℕ} (hm : m ≤ n) :
    U κ m ≠ (pt : V) := by
  intro hc
  match m with
  | 0 =>
    have h : (∅ : V) ∈ (UProp : V) := empty_mem_UProp
    rw [U_zero, pt_def] at hc
    rw [hc] at h
    simp at h
  | j + 1 =>
    have h : U κ 0 ∈ U κ (j + 1) := U_mem_of_lt hκ (Nat.succ_pos j) hm
    rw [hc, pt_def] at h
    simp at h

/-- **A sort's denotation is not an element of a `Prop`'s denotation.**

The semantic obligation behind `VEnv.sort_not_proof`, discharged: if `p` is a proposition
then `⟦p⟧ρ ⊆ {•}`, so `⟦.sort u⟧ρ ∈ ⟦p⟧ρ` would force `U κ (u.eval ls) = •`, refuted by
`U_ne_pt`.  Compare the `lam`-shaped instance discussed in §4, whose obligation is *false*
(`• ∈ {•} ∈ U κ 0 ⊆ U κ (k+1)`) — the sort shape is the only one that works, and it is the
one §4 shows cannot be transferred. -/
theorem sortDenot_not_mem_propDenot {n : ℕ} (hκ : IsInaccessibleChain n M.κ)
    {Γ : List VExpr} {u : VLevel} (hu : u.eval M.ls ≤ n) {p : VExpr} {ρ : V}
    (hp : (interp M L Γ p).toFun ρ ⊆ ({pt} : V))
    (h : (interp M L Γ (.sort u)).toFun ρ ∈ (interp M L Γ p).toFun ρ) : False := by
  have heq : (interp M L Γ (.sort u)).toFun ρ = (pt : V) := mem_singleton_iff.mp (hp _ h)
  rw [interp_sort] at heq
  exact U_ne_pt hκ hu heq

end SemanticObligation

end SetModel

/-! ## 5. The guarded import, and the strengthening bridge -/

namespace VEnv

variable {env : VEnv} {nv : ℕ}

/-- **`PropTypeAgree`, guarded by `OnCtx`.**  The form every unique-typing result in the
tree can supply, and the form `PropSplit`'s fields should have asked for. -/
def PropTypeAgreeOnCtx (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ : List VExpr} {e A A' : VExpr} {u u' : VLevel} {ls : List ℕ},
    OnCtx Γ (env.IsType nv) → u.WF nv → u'.WF nv →
    env.HasType nv Γ e A → env.HasType nv Γ e A' →
    env.HasType nv Γ A (.sort u) → env.HasType nv Γ A' (.sort u') →
    (u.eval ls = 0 ↔ u'.eval ls = 0)

/-- **The guarded import is a theorem**, modulo the tree's existing holes and adding none.

Two types of one term are convertible (`IsDefEq.uniqU`), so each is convertible to the other
through the sort the premise names; `IsDefEqU.sort_inv` turns that into `u ≈ u'`, which is
equality of `eval` at every valuation.

`sorryAx`-tainted through `IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniq`, i.e.
through the corner this file is about — which is the point: **the guarded import is not an
extra obligation.** -/
theorem WF.propTypeAgreeOn (henv : env.WF) : env.PropTypeAgreeOnCtx nv := by
  intro Γ e A A' u u' ls hΓ hu hu' he he' hA hA'
  -- `A ≡ A'` as types of `e`
  have hAA' : env.IsDefEqU nv Γ A A' := he.uniqU henv hΓ he'
  obtain ⟨W, hW⟩ := hAA'
  -- `A` inhabits both `W` and `.sort u`; likewise `A'` inhabits `W` and `.sort u'`
  have h1 : env.IsDefEqU nv Γ W (.sort u) := (hW.trans hW.symm).uniqU henv hΓ hA
  have h2 : env.IsDefEqU nv Γ W (.sort u') := (hW.symm.trans hW).uniqU henv hΓ hA'
  have h3 : env.IsDefEqU nv Γ (.sort u) (.sort u') :=
    IsDefEqU.trans henv hΓ h1.symm h2
  have h4 : u ≈ u' := IsDefEqU.sort_inv henv hΓ h3
  rw [VLevel.equiv_def.mp h4 ls]

/-- **`PropUniq`, guarded by `OnCtx`** — the companion import. -/
def PropUniqOnCtx (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ : List VExpr} {A : VExpr} {u v : VLevel} {ls : List ℕ},
    OnCtx Γ (env.IsType nv) → u.WF nv → v.WF nv →
    env.HasType nv Γ A (.sort u) → env.HasType nv Γ A (.sort v) →
    (u.eval ls = 0 ↔ v.eval ls = 0)

/-- **The guarded `PropUniq` is a theorem**, modulo the same existing holes and adding none.

Note this does *not* go through `WF.propTypeAgreeOn`'s diagonal: `PropUniq` is about the
sorts of a *type* and `PropTypeAgree` about the types of a *term*, so the diagonal
instantiation needs an inhabitant of `A` (that is `SetModel/PropUniqFromFalse.lean`'s route,
which pays for it with the goal's own `hfalse`).  With `OnCtx` in hand the direct route is
shorter: two sort-typings of `A` are convertible by `uniqU`, and `sort_inv` finishes. -/
theorem WF.propUniqOn (henv : env.WF) : env.PropUniqOnCtx nv := by
  intro Γ A u v ls hΓ _ _ h1 h2
  have h3 : env.IsDefEqU nv Γ (.sort u) (.sort v) := h1.uniqU henv hΓ h2
  rw [VLevel.equiv_def.mp (IsDefEqU.sort_inv henv hΓ h3) ls]

/-- **The bridge from the guarded import to the unguarded one, stated exactly.**

`PropTypeAgree` quantifies over *every* `Γ`, including contexts whose entries are not types.
The hypothesis named here is what closes that gap: every typing in an arbitrary context can
be moved to a context that is `OnCtx`.  That is a *strengthening* statement — the entries a
derivation never looks up can be replaced or removed — and strengthening is
`IsDefEqU.weakN_iff`, one of the tree's open holes.

Stated as a hypothesis rather than proved, so that the reduction is checkable and the
remaining obligation is a single named statement.  See §5 of this file's docstring for the
alternative (guard `PropSplit`'s fields instead, and this bridge is not needed at all). -/
theorem propTypeAgree_of_onCtx_of_strengthen (hg : env.PropTypeAgreeOnCtx nv)
    (hstr : ∀ {Γ : List VExpr} {e A : VExpr}, env.HasType nv Γ e A →
      ∃ Γ' : List VExpr, OnCtx Γ' (env.IsType nv) ∧
        ∀ {e' A' : VExpr}, env.HasType nv Γ e' A' ↔ env.HasType nv Γ' e' A') :
    env.PropTypeAgree nv := by
  intro Γ e A A' u u' ls hu hu' he he' hA hA'
  obtain ⟨Γ', hΓ', hiff⟩ := hstr he
  exact hg hΓ' hu hu' (hiff.mp he) (hiff.mp he') (hiff.mp hA) (hiff.mp hA')


/-! ### §4's load-bearing step, machine-checked

`§4` turns on `[falseProp]` being an admissible context for the consumers of
`sort_not_proof`: every call site in `Theory/Typing/Injectivity.lean` supplies exactly
`OnCtx Γ (env.IsType U)` and nothing else.  These two lines check that `[falseProp]` meets
it — at *every* environment, with no `WF` hypothesis — so the vacuity of §4 is not an
artifact of a context the syntactic side would reject. -/

/-- `∀ p : Prop, p` is a type, at every environment: `.sort (.imax 1 0)`. -/
theorem isType_falseProp : env.IsType nv [] falseProp :=
  ⟨.imax (.succ .zero) .zero,
    IsDefEq.forallEDF (HasType.sort (l := .zero) trivial) (IsDefEq.bvar .zero)⟩

/-- **`[falseProp]` is an `OnCtx`-well-formed context** — the hypothesis every consumer of
`sort_not_proof` supplies — and by `sound_falseProp_ctx_trivial` it is one at which the model
says nothing.  That pair is the transfer obstruction. -/
theorem onCtx_falseProp : OnCtx [falseProp] (env.IsType nv) := ⟨trivial, isType_falseProp⟩

/-! ## 6. The syntactic stream is already attacking the model's parameter — but the two
shapes are not interchangeable

`Theory/Typing/PropConv.lean` and `Theory/Typing/RegPiSat.lean` (another stream's files)
develop `PropTypeAgreeN`, `PropUniqN`, `PropConvInv`, `SortNotProp` and `PropNotProof`:
index-relativised statements about the *same* content, with a large amount already closed
(`propTypeAgree_of` closes six of seven typing cases; `regPi_false` refutes one of the
hypotheses outright and `RegPiOn`/`Regular` repair it).  Neither file mentions the model, so
this is worth recording explicitly: **by §2 that development is, verbatim, an attack on the
satisfiability of `SetModel`'s own parameter.**

`RegPiSat.lean` §5 independently reports a *cycle* on that side —
`PropConvInv → SortNotProp → PropNotProof → PropConvInv`, at one fixed index with no
descent.  §2 here reports a cycle on the semantic side.  The two are separate measurements
of the same corner, and they agree.

**But the statements do not compose as they stand, and the obstruction is at the level
layer.**  The model's `PropTypeAgree` is stated *pointwise in `ls`*
(`u.eval ls = 0 ↔ u'.eval ls = 0` for every `ls`), whereas the syntactic development's
`IsPropN env U n Γ A` is `Γ ⊢ₙ A : .sort .zero`, i.e. the `≈ .zero` shape.  One direction is
free (`propTypeAgree_equivZero`); the other is **refuted at the level layer**
(`propAgree_pointwise_not_from_equivZero`): `u = .param 0` and `u' = .param 1` are both `WF 2`
and satisfy `u ≈ .zero ↔ u' ≈ .zero` (both sides false), yet at `ls = [0, 1]` the pointwise
iff fails.

So a completed `PropTypeAgreeN` does **not** by itself discharge `PropSplit`'s import, and
the gap is not about typing: it is that the model asks the question separately at each level
valuation while the syntactic statement asks it once, universally.  Two ways to close it —
both *mathematically* cheap, and the first one measured below is a large mechanical edit:

* Weaken `PropSplit`'s fields to the single valuation the interpretation uses.  Nothing in
  `Interp.lean` evaluates a level at any `ls` other than `M.ls`, so the `∀ ls` in
  `prop_sound`/`proof_sound` is unused generality; specialising it leaves the import a
  one-valuation statement.  (Still not the `≈ .zero` shape — see the next item — but it is
  the honest strength of what the model consumes.)  **Cost**, since the same correction as in
  §5 applies: the valuation is a *field-level* `∀ ls`, so pinning it means giving `PropSplit`
  an `ls₀` parameter and matching it against `M.ls` at every use — **82 occurrences of
  `PropSplit env(F) nv` across 20 files**, and 42 of `IsPropAt`/`IsProofAt`.  Mechanical, but
  a flag day.
* Or note that the derivations the syntactic side inverts carry *closed* levels wherever the
  environment's declarations do, in which case `eval` is constant in `ls` and the two shapes
  coincide.  That is a statement about the declarations, not about the judgement, and it is
  not proved anywhere in the tree.

Recording this now is the point: the two streams look composable from their docstrings and
are not, and the discrepancy is invisible unless the two shapes are put side by side. -/

/-- **The model's pointwise form implies the `≈ .zero` form.**  The easy direction of the
shape comparison in §6. -/
theorem propTypeAgree_equivZero (hT : env.PropTypeAgree nv)
    {Γ : List VExpr} {e A A' : VExpr} {u u' : VLevel} (hu : u.WF nv) (hu' : u'.WF nv)
    (he : env.HasType nv Γ e A) (he' : env.HasType nv Γ e A')
    (hA : env.HasType nv Γ A (.sort u)) (hA' : env.HasType nv Γ A' (.sort u')) :
    u ≈ (.zero : VLevel) ↔ u' ≈ (.zero : VLevel) := by
  simp only [VLevel.equiv_def, VLevel.eval]
  exact forall_congr' fun _ => hT hu hu' he he' hA hA'

/-- **The converse fails at the level layer.**  `u ≈ .zero ↔ u' ≈ .zero` — the shape
`Theory/Typing/PropConv.lean`'s `IsPropN` produces — does not give the pointwise iff that
`PropSplit.proof_sound` consumes.  Witness: `.param 0` and `.param 1`, both `WF 2`, neither
`≈ .zero`, disagreeing at `ls = [0, 1]`.

Consequence: closing `PropTypeAgreeN` does not close `PropSplit`'s import.  This is a gap
between two streams' targets and not a defect in either. -/
theorem propAgree_pointwise_not_from_equivZero :
    ∃ u u' : VLevel, u.WF 2 ∧ u'.WF 2 ∧
      (u ≈ (.zero : VLevel) ↔ u' ≈ (.zero : VLevel)) ∧
      ¬ ∀ ls, (u.eval ls = 0 ↔ u'.eval ls = 0) := by
  refine ⟨.param 0, .param 1, by decide, by decide, ?_, ?_⟩
  · have h0 : ¬ (VLevel.param 0 ≈ (.zero : VLevel)) := by
      intro h; exact absurd (VLevel.equiv_def.mp h [1, 1]) (by simp [VLevel.eval])
    have h1 : ¬ (VLevel.param 1 ≈ (.zero : VLevel)) := by
      intro h; exact absurd (VLevel.equiv_def.mp h [1, 1]) (by simp [VLevel.eval])
    exact ⟨fun h => absurd h h0, fun h => absurd h h1⟩
  · intro h
    exact absurd ((h [0, 1]).mp (by simp [VLevel.eval])) (by simp [VLevel.eval])

end VEnv

end Lean4Lean
