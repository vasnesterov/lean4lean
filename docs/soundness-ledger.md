# Soundness ledger: what the model's soundness proof consumes

For each of the thirteen constructors of `VEnv.IsDefEq`
(`Lean4Lean/Theory/Typing/Basic.lean`), what the soundness induction needs — and
in particular which *injectivity* facts, since that is what the injectivity
stream should prioritise.

Statements are machine-checked in `Lean4Lean/Theory/SetModel/InterpSound.lean`;
the case analysis below is **analysis, not a completed proof**, and is marked as
such. Weakening and substitution, which several cases consume, *are* proved
(`SetModel/InterpSubst.lean`, sorry-free).

## Status

**Eleven of the thirteen cases are proved**, sorry-free, in
`SetModel/InterpSound.lean`, each with its induction hypotheses as explicit
arguments so it is checked against exactly the premises the real induction
supplies. **None uses any injectivity fact.**

| Proved | Lemma |
|---|---|
| `bvar` | `bvar_sound` |
| `sortDF` | `sortDF_sound` |
| `appDF` | `appDF_sound_eq`, `appDF_sound_type` |
| `lamDF` | `lamDF_sound_eq` |
| `forallEDF` | `forallEDF_sound_eq` |
| `defeqDF` | `defeqDF_sound` |
| `beta` | `beta_sound` |
| `eta` | `eta_sound` |
| `proofIrrel` | `proofIrrel_sound` |
| `symm`, `trans` | immediate from the IHs (`Eq.symm`, `Eq.trans`) |

**All thirteen cases are now covered.** `lamDF`/`forallEDF` part 3 are
`lamDF_sound_type`, `forallEDF_sound_prop`, `forallEDF_sound_type`; `constDF`
and `extra` are `constDF_sound_eq`/`_type` and `extra_sound_eq`/`_type`, proved
from `ModelData.Coherent`, which is the specification the constant-assignment
construction has to meet.

What remains is not a case but a *construction*: `ModelData.cnst` itself,
together with a proof of `Coherent`, by induction over the declaration list.

Two corrections to earlier versions of this ledger, both found by doing the
proofs, are recorded below: **part 2** and **context conversion**.

## Headline

**No injectivity fact beyond `IsDefEqU.sort_inv` appears in any case.**
Confirmed by proof for `beta` and `eta`; analysis for the other eleven.

`sort_inv` is already packaged as `LevelAssign` (`SetModel/Interp.lean`). The
other two `sorry`s in `Theory/Typing/Injectivity.lean` —
`IsDefEqU.forallE_inv` and `IsDefEqU.sort_forallE_inv` — do not appear.

The reason is structural, not luck. Both are **inversion** principles: they
recover the components of a `∀` from a definitional equality between two `∀`s.
Soundness never inverts, because every congruence rule *names* the components in
its premises:

- `appDF` has premise `Γ ⊢ f ≡ f' : forallE A B` with `A`, `B` named, so the
  induction hypothesis already concerns the right domain and codomain;
- `lamDF` and `forallEDF` state their body premises in the **same** extended
  context `A :: Γ` for both sides, so the two interpretations are compared at the
  same valuations;
- `defeqDF` needs only part 4 applied to the type, which is an induction
  hypothesis.

So the recommendation to the injectivity stream is: after `sort_inv`, nothing
else is needed *by the model*. `forallE_inv` and `sort_forallE_inv` are still
wanted by other consumers (`IsDefEq.uniq`, the refinement layer), but they are
not on the critical path to the interpretation.

## The four parts, and why there are only three

Carneiro proves four things by one simultaneous induction
(`soundness.tex:216`):

1. a proposition denotes a subset of `{•}`;
2. a proof denotes `•`;
3. `⟦Γ ⊢ e⟧ ρ ∈ ⟦Γ ⊢ α⟧ ρ`;
4. `Γ ⊢ e₁ ≡ e₂ : α` implies `⟦e₁⟧ ρ = ⟦e₂⟧ ρ`.

**Correction, twice revised.** The first version claimed part 2 is a corollary of
parts 1 and 3. The second version said it is a genuine branch. The settled
position, from carrying out the proofs, is:

**Part 1 is a corollary of part 3** — and needs no induction at all.
`⟦sort u⟧ρ = U κ (u.eval)`, and `U κ 0` is literally `UProp = ℘ {•}`, so
`⟦e⟧ρ ∈ ⟦sort u⟧ρ` with `u.eval = 0` *is* `⟦e⟧ρ ⊆ {•}` by `mem_UProp_iff`. That
is `propSound_of_mem_sort`. It needs only the judgement `Γ ⊢ e : sort u`, which
is a premise wherever part 1 is used — `proofIrrel` is the example, and it is
now proved from part 3 alone.

**Part 2 is a corollary of part 3 plus part 1 for the type**, which needs
validity (`IsDefEq.isType`, available and sorry-free in `Theory/Typing/`). It is
still convenient to carry through the induction, because `beta` and `eta`
consume it directly for a premise, but it is not independent content. That is
`proofSound_of`.

The old argument for part 2 being irreducible was that part 1 for the *type* is
not a subderivation. True, but validity supplies it, so the only cost is a
dependency on `IsDefEq.isType` rather than a fourth induction.

The tempting argument is: if `α` is a proposition then `⟦α⟧ρ ⊆ {•}` by part 1 and
`⟦e⟧ρ ∈ ⟦α⟧ρ` by part 3, so `⟦e⟧ρ = •`. But part 1 is about the *subject* of a
judgement, and this needs it for the *type* — i.e. for `Γ ⊢ α : sort u`, which is
**not a subderivation** of `Γ ⊢ e : α`. Recovering it would need validity plus a
separate induction, and there is no gain: proving part 2 directly is easy in every
case, because the interpretation returns `•` structurally in the `app` and `lam`
clauses. Both `beta` and `eta` consume part 2 for a premise term in their proof
branch, so it has to be carried regardless.

`PropSound`/`ProofSound` in `InterpSound.lean` are stated accordingly, each
conditional on the relevant split (`L.IsProp` / `L.IsProof`).

## A consistency fact used throughout

For `Γ ⊢ f : forallE A B`, the split for `app` (on `srt Γ f`) and the split for
`forallE` (on `lvl (A::Γ) B`) **agree**:

```
srt Γ f  ≈  lvl Γ (forallE A B)  ≈  imax (lvl Γ A) (lvl (A::Γ) B)
```

and `imax u v` evaluates to `0` exactly when `v` does. So `f` is a proof iff `B`
is a proposition. This follows from `srt_sound`, `lvl_sound` and level
arithmetic — no injectivity. It is used in `appDF`, `lamDF` and `beta`.

## A requirement the ledger did not have: context conversion

`lamDF` and `forallEDF` type their body premise in `A :: Γ`:

```
Γ ⊢ A ≡ A' : sort u  →  A::Γ ⊢ body ≡ body' : B  →  Γ ⊢ lam A body ≡ lam A' body' : forallE A B
```

but the right-hand side's interpretation uses `A' :: Γ`. So the interpretation
must not distinguish contexts differing by a definitional equality.

This is **not** an injectivity fact — it is a stability property of the level
assignment, in the same family as `LevelAssign.Stable` — so the headline is
unaffected. But it is a genuine extra obligation on whoever constructs a
`LevelAssign`, and it was missing from earlier versions of this ledger.

`SetModel/InterpSound.lean` packages it as `CtxInvariant`, a relation on
contexts that the level assignment cannot see, closed under extending both sides
by a common type, and proves `interp_ctxInvariant`: the interpretation is
constant along any such relation. For well-typed input the obligation is
discharged by `srt_sound`/`lvl_sound` together with context conversion
(`IsDefEq.defeqDFC` in `Theory/Typing/`).

## Case by case

| Rule | Part 3 (`⟦e⟧ ∈ ⟦A⟧`) | Part 4 (`≡` ⟹ `=`) | Injectivity |
|---|---|---|---|
| `bvar` | valuation is typed (`mem_interpCtx_cons`) + **weakening** for the `.lift` in `Lookup` | — | none — **proved** |
| `symm` | — | IH | none |
| `trans` | — | IH | none |
| `sortDF` | `U_mem_succ`; **the only place the universe bound is spent** | `l ≈ l'` gives equal evaluations | none — **proved** |
| `constDF` | `cnst` coherence | `ls ≈ ls'` + `cnst` coherence | none |
| `appDF` | IH gives `⟦f⟧ρ ∈ ⟦forallE A B⟧ρ`; apply at `⟦a⟧ρ`; **substitution** for `B.inst a` | IHs + `srt_congr` for the split | none — **proved** |
| `lamDF` | graph is a function into `⋃⟦B⟧`; split agreement | IHs + **context conversion** | none — part 4 **proved** |
| `forallEDF` | `U_mem_succ` at `imax u v` | IHs + **context conversion** | none — part 4 **proved** |
| `defeqDF` | IH part 4 on the type gives `⟦A⟧ρ = ⟦B⟧ρ` | IH | none — **proved** |
| `beta` | — | **substitution** + part 3 for `e'` (entanglement) + part 2 for `e` + `mkLam_value` | none — **proved** |
| `eta` | — | **weakening** for `e.lift` + part 2/3 for `e` + `function_eq_graph` | none — **proved** |
| `proofIrrel` | — | part 1 (derived from part 3) gives `⟦p⟧ρ ⊆ {•}`; part 3 puts both in it | none — **proved** |
| `extra` | `cnst` coherence with `env.defeqs` | same | none |

### The two cases that could have refuted the ledger — both now proved

**`beta` (`beta_sound`).** `⟦(λA.e) e'⟧ρ = (graph) ‘ ⟦e'⟧ρ = ⟦e⟧(snoc ρ ⟦e'⟧ρ) =
⟦e[e'/0]⟧ρ`. The middle step needs `⟦e'⟧ρ ∈ ⟦A⟧ρ` — part 3 for `e'`, exactly the
entanglement Carneiro flags; in `InterpSubst.lean` it is the `top` field of
`AgreeInst`, stated rather than proved, so substitution is available to the
induction without circularity. The proof branch (`λA.e` is a proof) needs part 2
for `e`. Both branches use only substitution, `mkLam_value`, and the split
agreement. **No inversion.**

**`eta` (`eta_sound`).** After weakening, `⟦λA. (e↑) (bvar 0)⟧ρ` is
`{⟨v, ⟦e⟧ρ ‘ v⟩ | v ∈ ⟦A⟧ρ}`, and this equals `⟦e⟧ρ` because an internal
function equals its own graph (`function_eq_graph`). **This needed no new
set-theoretic extensionality principle**: `value_eq_of_kpair_mem` and
`kpair_value_mem`, already in `SetModel/Rank.lean` for other reasons, are
exactly enough. The `Prop` branch is immediate (both sides are `•`, by part 2
for `e`). **No inversion.**

Supporting facts proved alongside: `mkLam_mem_function` (the `lam` clause really
is an internal function on its domain) and `mkLam_value` (applying it is
substitution into the body).

## The universe bound is spent in exactly two places

This should not be folklore, so it is recorded precisely.

1. **`sortDF_sound`**, through `U_mem_succ : U κ i ∈ U κ (i+1)`, needing
   `i = l.eval M.ls < n`.
2. **`forallEDF_sound_type`**, through `mkForallType_mem_U`, needing
   `i < n` where `i + 1` is the target index `(imax u v).eval`.

They are *not* the same mechanism, and an earlier summary that said both go
through `U_mem_succ` was wrong. `sortDF` is a universe being an element of the
next universe. `forallEDF` part 3 is a *closure* fact: the dependent product is
assembled by `repl_mem_vsetV'` (replacement, hence regularity), `sUnion_mem_U`
(free) and `function_mem_U` (limit-ness), and lands in the same stage its
components do. So the two spend the bound against different tiers of
`SetModel/Universe.lean`'s closure table.

Nothing else spends it. In particular **`forallEDF_sound_prop` spends nothing**:
a `∀` over a proposition lands in `U₀` for an arbitrary domain, so the `Prop`
layer of a derivation contributes zero to `n`. That is the model's statement of
impredicativity and it is what makes the bound tight rather than merely finite.

## Full ingredient list

| Ingredient | Consumed by | Status |
|---|---|---|
| `interp_liftN` (weakening) | `bvar`, `eta` | **proved** |
| `interp_inst` (substitution) | `appDF` part 3, `beta` | **proved** |
| `AgreeInst` entanglement | `beta` | **hypothesis by design** |
| `LevelAssign.lvl_congr` / `srt_congr` | every congruence case | **proved** |
| `LevelAssign.Stable` | `bvar`, `beta`, `eta`, `appDF` | hypothesis |
| `CtxInvariant` (context conversion) | `lamDF`, `forallEDF` | hypothesis — **new** |
| validity (`IsDefEq.isType`) | part 2 from part 1 + part 3 | available, sorry-free |
| `U_mem_succ` + explicit bound | `sortDF`, `forallEDF` | **proved** |
| `piProp_mem_UProp` | part 1, `forallE` case | **proved** |
| validity (`Γ ⊢ e : A → IsType Γ A`) | `appDF`, to level the `∀` | available, `Theory/Typing/` |
| `function_eq_graph` (a function is its graph) | `eta` | **proved** |
| `ModelData.Coherent` | `constDF`, `extra` | specification **stated**; construction **open** |
| `IsDefEqU.sort_inv` | packaged as `LevelAssign` | **open**, one `sorry` |
| `IsDefEqU.forallE_inv` | — | **not needed** |
| `IsDefEqU.sort_forallE_inv` | — | **not needed** |

## The induction is assembled — `SetModel/SoundInduction.lean`

All thirteen cases are now tied together. `soundAbove` is proved, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`, along with two corollaries:
`sound` (from the ordinary judgement) and `sound_nil` (at the empty context,
the form the coherence induction consumes).

Three things had to change to make the induction go through, and each is a fact
about the *statement*, found by attempting the proof.

### 1. `Sound` carries two parts, not four

Parts 1 and 2 are corollaries, and now literally so:

* **Part 1 from part 3.** If the type is `.sort u` with `u` evaluating to `0`
  then `⟦A⟧ρ = U κ 0 = ℘{•}`, so `⟦e⟧ρ ∈ ⟦A⟧ρ` *is* `⟦e⟧ρ ⊆ {•}`.
  (`Sound.prop`.)
* **Part 2 from parts 1 and 3.** (`Sound.proof`.)

The guard on part 1 also had to move. It was `L.IsProp M Γ e`; but `L.lvl Γ e` is
total, so it returns junk at terms that are not types and `L.IsProp` is
junk-satisfiable — a field guarded that way is unprovable at those instances.
The guard is now on the *judgement*: `A = .sort u` with `u` evaluating to `0`.
Every rule that needs part 1 carries exactly such a premise.

A consequence worth noting: `Sound.symm` is three lines, because part 3 for the
right-hand side follows from part 4 and part 3 for the left. The `symm` rule of
the induction is a one-liner.

### 2. The induction runs on `IsDefEqStrong`, and that removes two `sorry`s

`appDF` has to know whether `B` is a proposition — that is the branch `interp`
takes — which means it needs `A::Γ ⊢ B : .sort v`. From plain `IsDefEq.appDF`
that is `forallE_inv`. `IsDefEqStrong` (`Theory/Typing/Strong.lean`) carries it
as a premise, and `IsDefEq.strong` converts, needing only `Ordered env` and a
well-formed context. **`Strong.lean` is sorry-free.**

So the ledger's headline is now stronger than it was:

> Soundness consumes **no** injectivity fact at all. `sort_inv` is spent on
> constructing `LevelAssign`, and nowhere else. `forallE_inv` and
> `sort_forallE_inv` are not needed even indirectly.

`IsDefEqStrong` also hands over `A'::Γ ⊢ body ≡ body' : B` in `lamDF`, which is
what the context-conversion hypothesis needs, and the full sort data for `beta`
and `eta`.

### 3. The universe bound is a threshold, not a property of the judgement

`SoundBound` bounded the levels of the *conclusion*. That cannot work, and the
counterexample is small: in `appDF` the domain `A` does not occur in the
conclusion at all, so

```
f : A → B     with  A : Sort 100,  B : Prop
```

has a conclusion whose levels are all `≤ 1` and a subderivation that needs the
100th inaccessible. No bound on the conclusion is inherited by the premises.

Nor can the bound be moved onto `L`: `L.lvl Γ (.sort k) = k+1` for every `k`, so
no single `n` bounds a fixed environment's assignment. The bound is
irreducibly per-derivation.

What is true is that a derivation mentions finitely many levels. `SoundAbove`
says exactly that:

```
∃ m : ℕ, IsInaccessibleChain m M.κ → Sound M L Γ e₁ e₂ A
```

The threshold is produced by the induction — each case takes the maximum of its
premises' thresholds and the levels the rule itself names. The `∃` is over
derivations and stands *outside* the quantification over models, so this is the
schema form, not an `∃ k` about the model. Inheritance is then free, which is
what makes the induction possible at all.

The bound is still spent in exactly the two places the earlier analysis
identified: `sortDF` (threshold `l.eval ls + 1`) and `forallEDF`'s type branch
(threshold `max u.eval v.eval`). Every other case contributes nothing of its
own.

## The non-injectivity obligations — the handoff specification


This is the list of everything a `LevelAssign` / `ModelData` construction owes,
i.e. what has to be supplied before soundness is unconditional. None of it is an
injectivity fact.

| Obligation | Where declared | What it says |
|---|---|---|
| `LevelAssign.lvl_sound`, `srt_sound` | `Interp.lean` | the assignment agrees with the typing rules — this *is* `sort_inv`, in functional form |
| `LevelAssign.Stable` (4 fields) | `InterpSubst.lean` | the assignment commutes with weakening and substitution |
| `CtxInvariant L R` + `R (A'::Γ) (A::Γ)` for `A ≡ A'` | `InterpSound.lean`, `SoundInduction.lean` | the assignment cannot distinguish definitionally equal contexts |
| `ModelData.Coherent` (3 fields) | `InterpSound.lean` | constants inhabit their types; `env.defeqs` holds in the model |
| `AxiomsValidated` | `InterpSound.lean` | each axiom in the declaration list has an inhabited type in the model |
| `CoherentOn.const_congr` | `InterpSound.lean` | **new** — equivalent level arguments give the same value |

The first three are automatic for an assignment built the natural way — a
syntactic recursion mirroring `inferType` — and for well-typed input follow from
`sort_inv` together with `IsDefEq.weakN` / `instN` / `defeqDFC`. The last two are
genuine constructions, described below.

## `Coherent` needed a fifth obligation, and the reason is not a technicality

Attempting the `cnst` induction turned up that **`ModelData.Coherent` is not
provable for an arbitrary well-formed environment.** `Coherent.const_type` says a
constant's value inhabits its declared type. `VDecl.WF`'s `.axiom` case requires
only that the declared type *is a type* — not that it is inhabited. So

```
axiom bad : False
```

extends a well-formed environment to a well-formed environment, `⟦False⟧ρ = ∅`,
and no choice of `cnst` can satisfy `const_type`. This is a fact about the
statement, not about the proof: no induction fixes it.

The fix is the right one and was always implicit in the main theorem.
`kernel_sound` assumes `∀ d ∈ ds, Declaration.IsAxiomFree d` on the user's
declarations and admits only the standard prelude's three axioms — and the model
validates all three already:

| Axiom | Model-side validation |
|---|---|
| `propext` | `propext_of_mem_UProp` (`SetModel/Universe.lean`) |
| `Classical.choice` | `exists_choiceFunction_mem_U` — an internal choice function one stage up |
| `Quot.sound` | `eqvClosure`, `setQuotient`, `exists_quotient_lift` |

So `AxiomsValidated` is not new work; it is the place where work already done
gets attached. It is a hypothesis about the *declaration list*, not about the
model, which is why it belongs on the handoff side of the boundary.

## `Coherent` had to move to the empty context

Attempting the induction turned up a second problem, smaller than the axiom one
but equally fatal to the induction as originally stated. `Coherent`'s three
fields quantified over an arbitrary context `Γ` and `ρ ∈ interpCtx M L Γ`. But
`Γ`'s own types may mention a constant the induction has not yet declared, so
extending `cnst` changes the *hypothesis* of the field, not just its conclusion —
and the step cannot be taken.

Everything a declaration declares is closed, so the fix is to state all three
fields at `Γ = []`, `ρ = ∅`, and recover the general-context form where it is
consumed. That recovery is `interp_closed_ctx`: a closed term has the same
denotation in every context. It is a corollary of weakening, so it costs
`LevelAssign.Stable` — already an obligation — and nothing else.
`constDF_sound_type`, `extra_sound_eq` and `extra_sound_type` now take
`env.Ordered` and `L.Stable` and go through it. All still green.

## The step of the induction is now proved

Two new lemmas in `InterpSound.lean` carry out the actual step, for the two ways
a declaration changes the environment:

* **`coherentOn_addConst`** — adding a constant at a name the environment does
  not yet use preserves everything already established. The one fact it needs is
  that an earlier declaration's type mentions only earlier constants, which is
  new (see below).
* **`coherentOn_addDefEq`** — `addDefEq` does not touch `constants`, so nothing
  has to be transported and the two new obligations are exactly the equation and
  its typing.

`CoherentOn M L env` separates the environment being talked about from the
environment of the level assignment, so a single `L` for the *final* environment
serves the whole induction and nothing is ever rebuilt.

## A missing syntactic fact, now supplied: `Lean4Lean/Theory/SetModel/Consts.lean`

`coherentOn_addConst` needs **an earlier declaration's type cannot mention a
later declaration's constant**, and the repo did not have it. It is the exact
analogue, for constants, of `Ordered.closed` / `Ordered.closedC` in
`Theory/Typing/Lemmas.lean`, which say the same thing for de Bruijn indices, and
it is proved the same way:

| | de Bruijn version (existing) | constant version (new) |
|---|---|---|
| predicate | `VExpr.ClosedN` | `VExpr.ConstsIn` |
| context form | `CtxClosed` | `CtxConstsIn` |
| `IsDefEq` induction | `IsDefEq.closedN'` | `IsDefEq.constsIn` |
| tied off by | `Ordered.closed` | `Ordered.constsIn` |
| corollary used | `Ordered.closedC` | `Ordered.constsInC`, `Ordered.constsInD` |

Nothing in `Consts.lean` is set-theoretic. It lives under `SetModel/` only
because `Theory/Typing/` is owned by another stream; it would be at home next to
`Ordered.closed`, and should be moved there when that file is free.

## Building `cnst` turned up two more statement facts, and one blocker

### Blocker: `VDecl.mutualDef` refutes `leanTTConsistent`

`VDecl.WF.mutualDef` typechecks each member's *value* in `env'` — the
environment that already carries the block's own constants. So a member may be
defined to be itself, and

```
def f : (∀ p : Prop, p) := f
```

is a well-formed, axiom-free declaration step. The counterexample is
machine-checked in `Lean4Lean/Theory/MutualDefUnsound.lean`: `selfRef_wf` shows
the step is `VDecl.WF` over *any* environment where the name is free, and
`selfRef_inconsistent` shows the result types an inhabitant of `falseProp`.

**This is not an implementation divergence.** Both kernels agree, and both are
right:

* a **safe** mutual block is rejected outright by the C++ kernel
  (`src/kernel/environment.cpp`, `add_mutual`) and by `Lean4Lean.addMutual`;
* a **`partial`/`unsafe`** block is accepted by both, and
  `partial def bad : False := bad` really does land in the environment.

That is sound for Lean because such constants carry a `DefinitionSafety` tag the
kernel refuses to use while checking a safe declaration. **The abstract theory
models no such tag** — `VConstant` is `⟨uvars, type⟩` — so the fragment
`Theory/Consistency.lean` calls "pure", which lists `mutualDef`, is not
consistent.

The fix is a specification decision, not a proof, and it is not mine to take.
Two shapes: drop `mutualDef` from `VDecl` and keep `partial`/`unsafe`
declarations out of the `VEnv` entirely (`TrEnv'.mutualDef` is already only
reachable with `safety := .unsafe`), or give `VConstant` a safety flag and state
consistency for the safe fragment. Until one lands, `ModelData.Coherent` is not
provable for any environment containing a `mutualDef` step — there is no fixed
point for `cnst` — and neither is `leanTTConsistent`.

### `cnst` had to be reindexed by level *syntax*

`ModelData.cnst` was `Name → List ℕ → V`, indexed by the level arguments'
evaluations at `M.ls`. That makes `constDF`'s part 4 free, and it makes the
assignment **unconstructible**: a definition's value would have to satisfy
`cnst c (us.map (·.eval ls)) = ⟦value.instL us⟧`, so `⟦value.instL us⟧` would
have to depend on `us` only through its evaluation. That is true for well-typed
input, but proving it is a whole induction over the derivation, because the
proof-splitting decisions `L.srt Γ (f.instL us)` are functions of the *syntax*
and only their evaluations agree.

`cnst` is now `Name → List VLevel → V`. The obligation moves to a new
`Coherent` field, `const_congr`, and soundness discharges it in one line:
`IsDefEq.instL_r` (`Theory/Typing/Strong.lean`) gives
`env.IsDefEq nv [] (e.instL ls) (e.instL ls') (A.instL ls)` for `ls ≈ ls'`
pointwise, and `sound_nil` turns that into equality of denotations.

### `Coherent` was unsatisfiable without a level bound

`const_type` quantified over *all* level arguments `ls`. Take
`axiom foo.{u} : Sort u`. Then it demands `cnst foo [w] ∈ U κ (w.eval M.ls)` for
every `w` — including `w` whose evaluation runs past the end of the chain, where
`κ` is an arbitrary function and `U κ i` can be empty. No assignment satisfies
that, for any environment declaring a universe-polymorphic constant.

`CoherentOn` now carries a bound `n` and its three substantive fields are
guarded by `∀ l ∈ ls, l.eval M.ls < n`. Soundness takes
`hC : ∀ n, IsInaccessibleChain n M.κ → CoherentOn M L env₀ n`, and the `constDF`
and `extra` cases raise their own threshold to `lvlBound` of the level arguments
they are given. This is the same threshold discipline as `SoundAbove`, now
applied to the constant assignment as well — and it is forced for the same
reason.

### Soundness is now relative to a sub-environment

`soundAbove` takes `hle : env₀ ≤ envF` and runs on a derivation in `env₀` while
`L` remains the assignment for the final environment. Without this the coherence
induction cannot use soundness at an earlier stage at all, since `Coherent`'s
statement is tied to `L`'s own environment. Every use of `lvl_sound`/`srt_sound`
goes through `HasType.mono hle`.

## `cnst`: the assignment is defined and the definitional step is proved

`SetModel/Cnst.lean`. Two things landed, both sorry-free.

**`cnstOf`** — the assignment, by structural recursion on the declaration list
in the order `VEnv.WF'` gives. Every form that adds a block of constants goes
through the same parameterised step (`oracleExtend`), so no constructor list is
hardcoded outside `cnstOf` itself. `.mutualDef` has no image; the line will
delete with the constructor.

**`coherentOn_defConst` / `coherentOn_defEq`** — the `.def` and `.opaque` steps,
which are the ones only the model side can write, because they are the ones that
consume soundness:

* `const_congr` from `IsDefEq.instL_r` — instantiating at pointwise-equivalent
  level lists gives definitionally equal terms — plus `sound_nil`;
* `const_type` from `IsDefEq.instL` and `VDefVal.WF`, plus `sound_nil`;
* the defining equation from `VLevel.inst_map_id`, which turns
  `.const c (params uvars)` instantiated at `us` into `.const c us`, so the
  left-hand side's denotation *is* the value `defExtend` assigned;
* the transport between old and new assignment from `interp_cnst_congr` and
  `Ordered.constsIn`.

### The threshold moved inside `Coherent`, and that simplified everything

The previous entry gave `CoherentOn` a bound parameter `n`. That was wrong in an
instructive way: the construction of a `.def`'s value goes through `sound_nil`,
whose threshold depends on the *level instantiation*, so a single `n` for the
whole structure forced a shift `chain (n + k)` with `k` extracted from the
declaration list — which in turn would have required `soundAbove` to produce its
threshold as an explicit function rather than an `∃`.

Wrapping each field individually removes all of it:

```
def Above (M : ModelData V) (P : Prop) : Prop := ∃ m, IsInaccessibleChain m M.κ → P
```

Each `Coherent` field is `Above M (…)`, thresholds compose by `max` exactly as
they already did in the induction, and `SoundAbove` is now literally
`Above M (Sound …)`. The `constDF` and `extra` cases obtain the constant's own
threshold and fold it into theirs.

### A weaker invariant than `Ordered`, for the intermediate stages

`coherentOn_addConst` used to want `env.Ordered`. That is too strong for the
stages *inside* a block: adding an inductive's constructors passes through an
environment where the block's types are declared but its recursors are not, and
that is not `Ordered`. It only ever used two consequences, so those are now the
hypothesis — `VEnv.ConstsClosed` (`SetModel/Consts.lean`), preserved by each
individual `addConst` and implied by `Ordered`.

### The list forms are proved

`coherentOn_addConstList` and `coherentOn_addDefEqFold`, both sorry-free.
Between them they cover every way any declaration form extends the environment,
`addInduct'` included — it is three `addConstList` folds and one `addDefEq`
fold.

The defeq fold needs no bookkeeping at all: `addDefEq` never touches
`constants`, so each equation contributes exactly its own two obligations. The
constant list needs one fact, `addConstList_fresh`: *every* name of a block is
fresh for the environment the block is added to, not just the first — each later
name is fresh for a larger environment, and `addConst` failing on a taken name
gives it. That is what lets `interp_oracleExtend_eq` transport a denotation
across the whole block at once, which in turn is what lets `OracleOK` be stated
at the assignment the *finished* block produces rather than at each intermediate
stage.

### `.unsafeDef` stayed, under a purity predicate

The `mutualDef` fix landed as a rename rather than a removal: `VDecl.unsafeDef`
carries the same block, `VDecl.isPure` excludes it (and `.axiom`), and
`Theory/Consistency.lean` states consistency for the pure fragment.
`TrEnv'.unsafeDef` is gated on a non-`safe` `DefinitionSafety`, so the safe
fragment never sees it.

For `cnstOf` that means one line mapping `.unsafeDef` to the tail assignment,
and the coherence theorem will carry `∀ d ∈ ds, d.isPure` — a hypothesis, not a
vacuous case. There is no alternative: a self-referential block has no
assignment, so any theorem covering it would be false.

### Introduction rules for `∀`-denotations

The oracle has to *produce* elements of `⟦ci.type⟧` for constants that are
primitive, so it needs the two introduction rules for the `forallE` clause —
the only place the model builds a witness from scratch rather than from a term.
Both proved:

* `pt_mem_interp_forallE_prop` — propositional codomain. A `Prop` denotes a
  subset of `{•}`, so inhabiting `⟦∀ x : A, B⟧` is exactly proving `B`
  pointwise; there is no function to build.
* `mkLam_mem_interp_forallE` — proper codomain. Any definable pointwise-correct
  function gives an element, as its graph.

Plus `oracleOK_of` and `oracleOK_prop`, which discharge both `Above` wrappers by
`Above.pure`: every primitive the model supplies is built outright rather than
approximated, so no chain length is needed for the oracle's own obligations.

### Finding: `.axiom` and `.quot` are **not** independent of `.induct`

We had assumed the axiom and `Quot` obligations could be discharged against
`SetModel/Universe.lean` alone, without waiting for the inductive interpretation.
That is false, and the check is mechanical — collect the constants occurring in
each primitive's type:

| primitive | constants in its type |
|---|---|
| `Quot` | — |
| `Quot.mk` | `Quot` |
| `Quot.lift` | `Eq`, `Quot` |
| `Quot.ind` | `Quot`, `Quot.mk` |
| `quotDefEq` (its `type`) | `Eq` |
| `propext` | `Iff`, `Eq` |
| `Classical.choice` | `Nonempty` |
| `Quot.sound` | `Eq`, `Quot`, `Quot.mk` |

**`Quot` is the only primitive whose type mentions nothing else.** Every other
one — the remaining three `Quot` operations, the ι-rule for `Quot.lift`, and all
three standard axioms — has a type mentioning `Eq`, `Iff` or `Nonempty`, whose
denotations come from the `.induct` oracle.

So `propext`'s obligation is not "truth values are extensional"
(`propext_of_mem_UProp`, which is the set-theoretic core and is proved) but
"`⟦Eq α a b⟧ = {•}` exactly when `⟦a⟧ = ⟦b⟧`, and `⟦Iff p q⟧ = {•}` exactly when
`⟦p⟧ = ⟦q⟧`" — statements *about the inductive interpretation*, which is what
`Theory/Consistency.lean` already warns about when it says the prelude must pin
the genuine declarations of `Eq`, `Iff` and `Nonempty` rather than constants of
the right type. The set-theoretic core is then what closes the argument, not
what constitutes it.

### A design constraint found while sizing `Quot`'s own witness

`Quot : {α : Sort u} → (α → α → Prop) → Sort u` cannot be interpreted by
`setQuotient` uniformly. `setQuotient_mem_U` is stated at `U κ (i+1)`, and that
is not an artefact: at `u = 0` the quotient of a subset of `{•}` is a set of
equivalence classes, and `{•}` is not a member of `℘{•}` — the set-theoretic
quotient of a proposition is not a proposition. The interpretation has to split
on `u.eval = 0` and give the proof-irrelevant answer there (`{•}` if the domain
is inhabited, `∅` otherwise), matching Lean, where `Quot r : Prop` for
`α : Prop` and any inhabited `Prop` is `True`.

### The prelude specifications — `SetModel/PreludeSpec.lean`

Stated, deliberately not proved: `EqSpec`, `IffSpec`, `NonemptySpec`, the exact
statements the `.induct` oracle must meet for `propext` and `Classical.choice`.
Each is a `Prop`-valued definition, so the file is a specification written before
the interpretation it constrains, not an assumption.

Note what they say beyond `const_type`. `const_type` only asks that a constant's
value inhabit its declared type; the specs pin *which* function it is. That
extra content is precisely what `Theory/Consistency.lean` means when it insists
the prelude pin the genuine declarations rather than constants of the right
type.

**Verdict: all three come out true, and none needs a side condition.** That was
the point of writing them, so the negative result is worth recording. The one
degenerate case that had to be inspected is `EqSpec` at `u.eval = 0`: the domain
is then a member of `UProp`, hence a subset of `{•}`, so both elements are `•`
and the equation says `{•}` — which is right, a `Prop` has at most one proof. It
comes out consistent rather than needing a guard.

The chain of reduction, recorded so it is not rediscovered:

* `propext` ← `IffSpec` (turns an inhabitant of `⟦a ↔ b⟧` into `a = b`) and
  `EqSpec` at level `.succ .zero` with `α := UProp` — note the level: `@Eq` is
  applied at `α := Prop = Sort 0`, which lives in `Sort 1`.
* `Classical.choice` ← `NonemptySpec` (turns an inhabitant into `α ≠ ∅`) and
  `exists_choiceFunction_mem_U`. This is the only one of the three whose
  obligation touches the chain: `i < n` and `𝗔𝗖`.
* `Quot.sound` additionally needs the `Quot` interpretation.

`propext_of_mem_UProp` does not appear in any of these. It is what will be spent
*proving* `IffSpec`, not what `propext`'s obligation reduces to.

### `Quot`'s value — `SetModel/QuotInterp.lean`

`quotRel`, `quotVal`, `quotVal_mem_U`, all proved. `quotVal` splits on the
universe index: the honest `setQuotient` by the *equivalence closure* of the
relation above `Prop`, and the proof-irrelevant answer at `Prop` itself.

### One requirement, stated in three vocabularies

Worth connecting once so a future reader does not have to notice it three times.
The same requirement appears as:

* **`Theory/Consistency.lean`** — the prelude must pin the *genuine* inductive
  declarations of `Eq`, `Iff` and `Nonempty`, not merely constants of the right
  type.
* **`kernel_sound`'s design note** — `propext` over a nonstandard `Eq` would
  honestly prove `False`.
* **`SetModel/PreludeSpec.lean`** — the specs say strictly more than
  `Coherent.const_type`. `const_type` asks only that a constant's value *inhabit*
  its declared type; the specs pin *which function it is*.

That gap — inhabiting the type versus being the intended element of it — is the
whole content of the requirement, and it is why the standard axioms cannot be
validated against `SetModel/Universe.lean` alone.

### `Quot`'s value layer, and what it cost

`quotRel`, `quotEqv`, `quotVal`, with `quotVal_mem_U` and full joint
definability (`quotRel_definable`, `eqvStep_definable₃`, `quotEqv_definable`,
`setQuotient_definable₂`, `quotVal_definable`). All proved.

This was expected to be mechanical and was not. Everything the model puts inside
a `mkLam` must be `ℒₛₑₜ`-definable **jointly in all its arguments**, because the
fibre map varies with the domain element — a strictly stronger demand than
anything `Universe.lean` needed, where `eqvStep_definable` fixes the carrier and
relation and is definable only in the stage. Plain `definability` reaches none
of the joint versions. Three things were needed together:

1. the `mem_ext_iff` route — restate `T = f a b` as a membership formula, then
   call `definability` (already the idiom used by `eqvStep_definable` itself);
2. passing `sep`'s definability argument **explicitly** instead of through its
   `autoParam`, because the `autoParam` runs `definability` without the local
   hypotheses that make it succeed;
3. **replacing `lfp` by its Π₁ characterisation.** `eqvClosure` is `lfp`, hence
   `⋂ˢ` of the prefixed points, and `⋂ˢ`'s membership condition carries a
   nonemptiness *existential*. That existential is what makes `definability`
   diverge — it is the difference between the version that fails and the version
   that succeeds. `quotEqv` states the same set by its universal property and
   goes through.

Without (2) and (3) the failure is
`aesop: internal error during proof reconstruction: goal N was not normalised`,
i.e. Foundation gap #1, which is therefore broader than "arity ≥ 4 composition":
it is also triggered by an existential nested under a set quantifier.

**Generalisable lesson:** a least fixed point is fine to *reason* with and bad to
*compute inside a definable function*. Where a definable version is needed,
state the fixed point by its universal property instead. `Ind` and `indRec`
(`SetModel/Inductive.lean`) are also `lfp`s, so the same substitution will be
needed when the `.induct` oracle is built.

### The "value layer / plumbing" boundary does not exist

I split `Quot`'s work into a value layer (done) and mechanical plumbing (the two
`mkLam` applications). That split is wrong, and the second attempt at
"mechanical" is what showed it.

**`mkLam`'s fibre map is itself a value-layer object.** Each nested λ introduces
a new composite function needing its own joint-definability proof, and
`definability` cannot compose the proofs already established — each needs a
bespoke `mem_ext_iff` restatement, harder as the nesting deepens. For `Quot`
(two λs) the two outstanding obligations are

* `ℒₛₑₜ-function₂ (fun _ r ↦ quotVal α r i)`, the dummy-argument weakening of
  `quotVal_definable₁`;
* `ℒₛₑₜ-function₁ (fun α ↦ mkLam … (snoc ∅ α))`, the outer fibre map.

Neither goes through — although the *abstract* form of the first,
`ℒₛₑₜ-function₁ f ⊢ ℒₛₑₜ-function₂ (fun _ y ↦ f y)`, does when `f` is an opaque
hypothesis. Isolating that difference is the diagnosis: `definability`
re-unfolds `quotVal` instead of using the supplied lemma, so supplying more
lemmas does not help.

**What is missing is a small library of `mkLam` definability combinators**,
above all a joint form

```
mkLam_definable₂ :
  (G definable in (a, ρ)) → (F definable in (a, ρ, v)) →
  ℒₛₑₜ-function₁ (fun a ↦ mkLam (G a) _ (F a) _ (ρ a))
```

making each nested λ one application rather than a bespoke proof.

This is the third finding in a row from the same source, and they compound:
joint definability is needed at all (found building `quotRel`); `lfp` must be
replaced by its Π₁ form (found building `quotEqv`); and nesting needs
combinators (found here). All three are prerequisites for the `.induct` oracle,
where a constructor or recursor is a *deeper* nest than `Quot` is. Estimating
`.induct` as "the model side is finished and waiting" was too optimistic on
exactly this axis.

### The pattern: uniform in ZFC, not uniform across `Sort 0`

That split is the **third** time this session a statement that reads uniformly
has needed a level-sensitive case analysis:

1. `forallE`'s codomain — impredicative `mkForallProp` versus `mkForallType`,
   split on whether the codomain is a `Prop`.
2. `Coherent`'s level bound — `U κ i` is a real universe only below the chain
   length, so `const_type` cannot quantify over all level arguments.
3. `Quot` — `setQuotient_mem_U` is stated at `U κ (i+1)` and that is not an
   artefact: the one equivalence class of `{•}` is `{•}`, so the quotient is
   `{{•}}`, which is not a subset of `{•}`. The set-theoretic quotient of a
   proposition is not a proposition.

The pattern is worth naming, and is now a **standing check**: **a construction
that is uniform in ZFC is rarely uniform across `Sort 0` versus `Sort (u+1)`,
because `Prop` is proof-irrelevant and impredicative while the higher universes
are neither.** In each case the uniform statement was not merely harder to prove
— it was false, and the case split is what makes it true.

So: *before proving any new uniform statement about the interpretation, evaluate
it at `u = 0` first.* Five minutes, with the same payoff profile as the pre-proof
truth check that has now caught five false statements.

### What is left of `cnst`

* the outer induction over `VEnv.WF'`, assembling the per-form steps;
* the oracle's obligations for the three forms whose values the model supplies:
  `.axiom` (the three standard axioms, all already validated in
  `SetModel/Universe.lean`), `.quot` (same file), `.induct` (`IndStage.lean` and
  `IndCard.lean`, still to be connected to `VInductDecl'`).

`addInduct'` is `addIndTypes ▸ addIndCtors ▸ addIndRecs ▸ addIndRules` — three
`addConstList` folds and one `addDefEq` fold — so the list step lemmas cover it
with no new shape. Checked against `Theory/Inductive/Decl.lean`: a constructor's
type mentions only the block's *types* (declared in the previous phase), and a
recursor's type mentions types and constructors (both declared earlier), so the
phase-wise hypothesis "each type mentions only constants of the environment at
the start of this phase" holds. No interface mismatch.

## The remaining open items, ranked




1. **`IsDefEqU.sort_inv`** — gives `LevelAssign`, hence the interpretation.
   Single `sorry`, highest value in the project.
2. **Connecting the `.induct` case.** No longer blocked: `VDecl.induct`
   carries `VInductDecl'` and `VDecl.WF` uses `env.addInduct'`, both complete
   (`Theory/Inductive/Decl.lean`). The set-theoretic side has been finished and
   waiting — `SetModel/IndStage.lean` and `SetModel/IndCard.lean` supply the
   family, its constructors, its recursor and its ι-rule, all as members of the
   right stage. What remains is matching the two shapes up. Watch the
   elimination universe: it is not uniform across inductives — a small
   eliminator such as `Nonempty` fails large elimination and its recursor takes
   one universe parameter where `Eq`'s takes two.
3. **`VDecl.mutualDef`** — decided: the constructor is being removed and
   `partial`/`unsafe` declarations will get no `VEnv` image. Another stream owns
   the change.
4. **`ModelData.cnst` and `ModelData.Coherent`** — an induction over the
   declaration list, which `VEnv.WF'` already orders. This is where the
   well-foundedness that Carneiro's `|c| = |e| + 1` clause needs actually lives;
   displacing it here is what made the term recursion in `SetModel/Interp.lean`
   structural, and discharging it is what makes that trade honest.

   The induction now splits cleanly by `VDecl`:

   | Declaration | Value of `cnst` | Status |
   |---|---|---|
   | `.axiom` | supplied by `AxiomsValidated` | ready |
   | `.def`, `.opaque`, `.example`, `.mutualDef` | `⟦ci.value⟧` at the earlier assignment | ready |
   | `.quot` | `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and `quotDefEq` | ready — `addQuot` is concrete, model side in `Universe.lean` |
   | `.induct` | whatever `addInduct` introduces | blocked on item 2 |

   The step is proved (`coherentOn_addConst`, `coherentOn_addDefEq`) and so is
   soundness (`SoundInduction.lean`), which the `.def` step consumes at a
   strictly earlier environment; what remains is the outer recursion. Two further lemmas
   were built this stage, both proved in `InterpSound.lean`:

   * **`interp_cnst_congr`** — the interpretation is environment-independent in a
     precise sense: `interp M L Γ e` depends on `M.cnst` only at the constants
     that actually occur in `e` (`ConstsAgree`). So as the environment grows
     along `ds`, earlier terms keep their denotations — the induction only ever
     *extends* `cnst`, and nothing has to be revisited.
   * **`LevelAssign.mono`** — a `LevelAssign` for a larger environment restricts
     to any smaller one, so a single `L` for the final environment can be fixed
     up front and reused at every stage, rather than rebuilt.

   Item 4 is independent of item 1 and of the injectivity stream; it is *not*
   independent of items 2 and 3. Soundness — its other prerequisite — is done.
