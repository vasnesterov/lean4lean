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
| `AgreeInst` entanglement | `beta` | **hypothesis by design** — satisfiability **unmeasured**; `docs/vacuity-ledger.md` §6 |
| ~~`LevelAssign.lvl_congr` / `srt_congr`~~ | every congruence case | **the parameter is gone** — `LevelAssign` as stated is `IsEmpty` (`no_levelAssign`). Live: `PropSplit`, measured satisfiable and non-trivial (`exists_propSplit`, `propSplit_not_constant`) |
| `PropSplit.Stable` (was `LevelAssign.Stable`) | `bvar`, `beta`, `eta`, `appDF` | hypothesis, **measured**: the unguarded form was unsatisfiable (`no_stable`); the guarded one is satisfiable and *exactly* characterised (`exists_stable_propSplit`, `propSplitOf_stable_iff`) |
| `CtxInvariant` (context conversion) | `lamDF`, `forallEDF` | hypothesis, **measured**: trivially satisfiable ALONE (take `R := Eq`), so only the pair with `hRd` means anything — and that pair is machine-checked consistent (`ctxInvariant_prop_agrees`) |
| validity (`IsDefEq.isType`) | part 2 from part 1 + part 3 | available, sorry-free |
| `U_mem_succ` + explicit bound | `sortDF`, `forallEDF` | **proved** |
| `piProp_mem_UProp` | part 1, `forallE` case | **proved** |
| validity (`Γ ⊢ e : A → IsType Γ A`) | `appDF`, to level the `∀` | available, `Theory/Typing/` |
| `function_eq_graph` (a function is its graph) | `eta` | **proved** |
| `ModelData.Coherent` | `constDF`, `extra` | specification **stated**; construction **open** |
| `IsDefEqU.sort_inv` | ~~packaged as `LevelAssign`~~ — that packaging is refuted; see the correction below | **open**, one `sorry` |
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
| ~~`LevelAssign.lvl_sound`, `srt_sound`~~ | `Interp.lean` | **refuted**: no `LevelAssign` exists, at any environment and any parameter count (`no_levelAssign`). Replaced by `PropSplit.prop_sound` |
| `PropSplit.Stable` (4 fields) | `InterpSubst.lean` | the split commutes with weakening and substitution. The `env.HasType` guard on the `instN` fields is **load-bearing** — without it the field is unsatisfiable (`no_stable`), and its docstring says so |
| `CtxInvariant L R` + `R (A'::Γ) (A::Γ)` for `A ≡ A'` | `InterpSound.lean`, `SoundInduction.lean` | the split cannot distinguish definitionally equal contexts. Only the **pair** is meaningful: `CtxInvariant` alone holds of `R := Eq` |
| `ModelData.Coherent` (3 fields) | `InterpSound.lean` | constants inhabit their types; `env.defeqs` holds in the model |
| `AxiomsValidated` | `InterpSound.lean` | each axiom in the declaration list has an inhabited type in the model |
| `CoherentOn.const_congr` | `InterpSound.lean` | **new** — equivalent level arguments give the same value |

The last two are genuine constructions, described below.

### CORRECTION (2026-08-31): "the first three are automatic" was false

This paragraph used to continue: *"The first three are automatic for an assignment built the
natural way — a syntactic recursion mirroring `inferType` — and for well-typed input follow
from `sort_inv` together with `IsDefEq.weakN` / `instN` / `defeqDFC`."*

They were not automatic; two of the three were **unsatisfiable as stated**, and the natural
recursion is exactly what cannot exist:

* `no_levelAssign` (`Theory/SetModel/LevelAssignUnsat.lean:106`) proves
  `IsEmpty (LevelAssignUnguarded env nv)` — `lvl_wf` and `lvl_sound` contradict each other at a
  context holding an out-of-range universe parameter. So "an assignment built the natural way"
  had no instances at all.
* `no_stable` (same file, :172) refutes `Stable.lvl_instN` as originally stated: `Ctx.InstN`
  declares `e₀` as a parameter its `zero` constructor never mentions, so the field could be
  pointed at an arbitrary substituted term. Repaired by an `env.HasType` guard.
* `CtxInvariant` survived, but "automatic" was still the wrong word: it is *trivially*
  satisfiable in isolation (`R := Eq`), and its content lives entirely in the companion
  hypothesis `hRd`. That pair is consistent, machine-checked, and for a reason worth reading
  (`Theory/SetModel/CoherentWitness.lean`).

The generalisation, from that file, is the diagnostic to apply to the rest of this ledger:

> The defect signature is a structure quantifying over a relation **parameter** that the
> relation's own constructors never constrain.

Also corrected earlier this round: this file's `coherentOn_addConstList` /
`coherentOn_addInduct` entries stated `hocc` at the pre-block environment, where it is
unsatisfiable (`addConstList_hocc_unsat`, `hocc_unsat_eqIndDecl`). Full registry, with what is
and is not measured, in **`docs/vacuity-ledger.md`**.

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

### The combinator library, and `Quot`'s `const_type`

`SetModel/Definability.lean` — ten lemmas in the five categories scoped in
advance: projections, environment reads, argument substitution/weakening, and
the three binder formers precomposed. The boundedness claim held; nothing was
added beyond the list except `mkLam_mem_interp_forallE'`, which belongs to the
"binder formers" category.

`quotFn_mem` — **`Quot`'s `const_type` obligation — is proved.** Two nested λs,
each one application.

Three things made it work, and only the first was anticipated:

1. **Explicit `.comp` instead of search.** The failure was the *depth* symptom,
   not the bug: `DefinableFunction₂.comp` is registered and applies, `aesop`
   just could not find it within fifty rule applications. Applying it by hand
   discharges in one step. So the library is not new mathematics — it is the
   compositions the interpretation already uses, each stated once.

2. **Read the environment, do not capture.** `interp`'s own `lam` clause writes
   its fibre map as a function of `ρ`, recovering bound variables with `ρ ‘ k`
   rather than capturing them from an enclosing binder. The first attempt at
   `Quot` captured `α` directly, which is what made every layer need a bespoke
   proof. Rewritten in the environment-passing style, the nesting composes.

3. **Prove the introduction rule schematically.** Applying
   `mkLam_mem_mkForallType` at a concrete call site makes `whnf` unify two
   `ℒₛₑₜ`-definability *proof terms*, which at that size hangs.
   `mkLam_mem_interp_forallE'` states the same thing with those proofs as
   variables, so the hard unification happens once, against metavariables.

### A new instance of the `isDefEq` hazard: do not ascribe coercion indices

Found by bisection while the above was failing, and worth its own line because
the diagnosis is counter-intuitive. This loops:

```lean
have hval : (snoc ∅ α) ‘ ((0 : ℕ) : V) = α := snoc_value_at_len M L hnil
```

and this does not:

```lean
have hval := snoc_value_at_len M L (v := α) hnil
rw [List.length_nil] at hval
```

The lemma's index is `((Γ.length : ℕ) : V)`. Ascribing `((0 : ℕ) : V)` asks
`whnf` to reconcile two *coercion shapes*, which unfolds the set-theoretic
numerals; rewriting `List.length_nil` at the `ℕ` level instead is one syntactic
step. **Take the lemma's own form and adjust the index afterwards.** The
symptom is indistinguishable from the `mkLam` unification blow-up — both are
`whnf` timeouts at the theorem header — which is why bisecting to the individual
`have` was necessary rather than reasoning about which step "looked expensive".

### Measured: what one more λ costs

`Quot` has two nested λs, `Quot.mk` three, so `Quot.mk` is the first real
measurement of `.induct`'s function layer — a constructor is the same
construction one level deeper.

**On the definability axis the growth is linear, and there is no new *kind* of
work.** Going from two λs to three needed exactly:

| | `Quot` (2 λs) | `Quot.mk` (3 λs) |
|---|---|---|
| new primitives needing a `mem_ext_iff` definability lemma | `quotRel`, `quotEqv`, plus `eqvStep₃`, `setQuotient₂` | `eqvClass₃` |
| value definability | `quotVal_definable` | `quotMkVal_definable` — same proof shape, arity 3 |
| fibre substitution | 1 × `definable₂_comp₁` | 1 × `DefinableFunction₃.comp`, same shape |

I had extrapolated that each extra λ would need *new* substitution combinators
and that this was the nonlinearity. **That was wrong**, and testing it rather
than reasoning about it is what showed so: arity 3 went through with the same
pattern as arity 2, because `DefinableFunction₃.comp` already exists and applies
by hand exactly as `₂.comp` does.

**The real cost driver is codomain shape, not nesting depth.** What `Quot.mk`
needs that `Quot` did not is nothing to do with depth:

* its codomain is `Quot α r` — a *constant application*, not a sort — so the
  typing derivation needs `constDF` plus two `appDF`s and their `inst`
  computations, where `Quot`'s spine was `sortDF`/`bvar`/`forallEDF` throughout;
* connecting `⟦Quot α r⟧` to `quotVal` needs value-computation lemmas
  (`mkLam_value` chains down the nest), which `Quot` never needed because its
  codomain was a universe.

**For `.induct` this is good news and it is specific.** A constructor's codomain
is `I params indices` — a constant application — so every constructor pays the
`constDF`/`appDF` cost *once*, and it does not compound with the number of
fields. The per-field cost is one `.comp` and one `mkLam`, i.e. linear.

**The one hard ceiling is arity.** Foundation's `DefinableFunction` abbreviations
and their `comp` lemmas stop at **₅** (`DefinableRel` reaches ₆). A constructor
with more than about four fields exceeds the supported API and must drop to the
raw `DefinableFunction (k := n)` form with hand-rolled composition. That is a
friction ceiling rather than an impossibility, but it is where the linear
estimate stops being valid, and it is worth knowing before the constructor layer
is scheduled.

### The `u = 0` check caught a fourth, and this one changes the witness *shape*

Run on `Quot.mk : ∀ (α : Sort u) (r : α → α → Prop) (a : α), Quot α r` before
building anything:

* `Quot α r` has sort `u`;
* `∀ (a : α), Quot α r` has sort `imax u u`;
* `∀ (r : …), …` has sort `imax _ (imax u u)`;
* `∀ (α : Sort u), …` has sort `imax (u+1) (…)`.

At `u.eval = 0` every `imax` collapses to `0`, so **the whole type of `Quot.mk`
is a proposition** and its denotation is a subset of `{•}`. The witness cannot
be a nest of three λs — it must be `•`.

The three earlier splits changed the *value* of a construction. This one changes
the *shape of the witness*: a nested-λ witness is not harder to prove here, it
is wrong, and nothing in the `u ≠ 0` development hints at it. The check cost
five minutes and would otherwise have surfaced as an unprovable goal at the
bottom of a three-deep nest.

### `Quot.mk` progress, and what the spine lemmas cost

Landed and green: the value layer (`quotMkVal` + definability + membership), the
`mkLam_value` chain (`quotFn_value`, `quotFib_value`) that computes `Quot`'s
denotation at a point, the codomain typing derivation (`quotConst_type`,
`quotMkCod_type` — `constDF` plus two `appDF`s), and the spine
(`quotMkInner_type`, `quotMkMid_type`).

Two things worth recording from the derivation:

* **The `inst`/`lift` computations came out on the nose — and have now three
  times running.** This is worth stating as a positive expectation rather than a
  repeated surprise: **the de Bruijn arithmetic of a constructor's spine lines up
  by construction in this development.** `appDF` produces a codomain of the form
  `B.inst (.bvar k)`, and the argument's context type is the correspondingly
  lifted expression; these are syntactically equal, so the next `appDF` fires
  with no rewriting. A transport lemma becoming necessary would be a signal that
  something is off, not routine work. `appDF` produces the
  codomain type `(∀ r, Sort u).inst (.bvar 2)`, and the argument `.bvar 1` has
  context type `(quotRelTy.lift).lift`. These are syntactically equal, so the
  second `appDF` applies with no rewriting at all. That is worth knowing before
  the constructor layer: the de Bruijn arithmetic of a constructor's spine
  lines up by construction rather than needing transport lemmas.
* **The spine lemmas are stated over an arbitrary context tail** (`Δ`), because
  the `bvar` lookups only see the prefix. That makes them reusable at any depth,
  which is what `Quot.ind` and `quotDefEq` will need.

What remains for `Quot.mk` is the membership obligation itself, in both
branches: `pt_mem_interp_forallE_prop` three times at `u.eval = 0`, and the
nested `mkLam` route otherwise, both bottoming out at
`⟦Quot α r⟧ρ = quotVal α r i` via the value chain.

### `Quot.mk` is complete, and `Quot.ind` will need something new

`quotMkFn_mem` — **`Quot.mk`'s `const_type` obligation, both branches** — is
proved. The witness splits on the level (`•` at `Prop`, three λs above it), and
both branches bottom out at the same two facts: `interp_quotMkCod`, which
computes `⟦Quot α r⟧` by two `interp_app_type` steps and two `mkLam_value` steps
down `Quot`'s own nest, and `quotMkVal_mem`.

**The `u = 0` check on `Quot.ind` comes out the other way, and that is
informative.** Its type is

```
∀ (α : Sort u) (r : α → α → Prop) (β : Quot α r → Prop),
  (∀ a : α, β (Quot.mk α r a)) → ∀ q : Quot α r, β q
```

whose innermost body `β q` is a `Prop` *by construction* — `β` lands in
`Sort .zero` — so every `imax` in the five-binder spine collapses to `0` at
**every** `u`. The whole type is a proposition, the witness is `•`
unconditionally, and there is no level split. Contrast `Quot` and `Quot.mk`,
whose codomains are `Sort u` and therefore did need one. The check is not a
ritual: it distinguishes these cases rather than always firing.

**So the rule has a sharper form than "check at `u = 0`":**

> Ask whether the codomain's `Prop`-ness is **by construction** or **by
> instantiation**. If a codomain is literally `Sort .zero` in the syntax, the
> `imax`es collapse uniformly and there is no split. If it is `Sort u` for a
> bound `u`, expect one.

That tells the next person *when* to expect a split rather than to test every
time — `Quot` and `Quot.mk` are the second kind, `Quot.ind` the first.

**What `Quot.ind` needs that the first two did not**: the bottom of the nest is
`• ∈ ⟦β q⟧` for an arbitrary `q ∈ quotVal α r i`, while the hypothesis binder
supplies `• ∈ ⟦β (Quot.mk α r a)⟧` only for `a ∈ α`. Bridging those is
**surjectivity of `Quot.mk`**.

`quotVal_surj` — proved. It is the first of the four `Quot` obligations to need
a real fact about `setQuotient` rather than membership arithmetic, and the risk
worth flagging in advance was the degenerate branch, which has already produced
one non-uniformity here.

**It came out uniform**, and the reason is worth recording because it is not an
accident of the proof: at `Prop` the quotient is `{•}` when the carrier is
inhabited and `∅` otherwise, so possessing an element of it *forces the carrier
nonempty* and that element is `•` — which is exactly what `Quot.mk` denotes
there. The surjection is witnessed by any inhabitant of the carrier, and one
exists precisely because the quotient was inhabited. Above `Prop` it is
`mem_setQuotient_iff` directly. One statement, both branches.

### `Quot.ind`'s spine is typed, and a check on the way turned up why the
### degenerate witness is safe

The five-binder spine is complete and green: `quotIndBeta`, `quotIndMkAp`,
`quotIndHyp`, `quotIndQ` and the body `β q`, with typing derivations for each and
for the four nested `forallE`s above them. `quotMkConst_type` joins
`quotConst_type`. The `inst`/`lift` alignment held through five more `appDF`s —
three for `Quot.mk α r a` and two for `Quot α r` — with no transport.

One derivation did need help, and it is a different failure from the coercion
family: `Lookup` returns the context entry *lifted*, and `lift` does not compute
through a `def`. `((quotIndBeta u).lift).lift.lift` is not syntactically a
`forallE`, so `appDF` cannot see the function type. The fix is to ascribe the
spelled-out lifted expression in a `have` — cheap, because no `interp` is
involved. Worth knowing before the constructor layer, where every spine entry is
a named definition.

**And the check that matters.** Working out what `Quot.ind` needs at the bottom
of its nest exposed a question about `Quot.mk`'s witness: at `u.eval = 0` it is
`•`, so `⟦Quot.mk α r a⟧` would be `((• ‘ α) ‘ r) ‘ a` — junk — where
`Quot.ind`'s hypothesis binder needs it to be `quotMkVal α r a 0 = •`.

It is fine, and the reason is structural rather than lucky: at `u.eval = 0` the
partial application `Quot.mk α r : ∀ a : α, Quot α r` has sort `imax u u`, which
evaluates to `0`, so it *is a proof* and `interp_app_proof` fires — giving `•`
**regardless of what `cnst Quot.mk` is**. The junk never surfaces because the
proof splitting short-circuits it.

So: **`interp`'s proof splitting is what makes a degenerate `Prop` witness safe.**
Had the interpretation not split on proofs, `•` would have been type-correct at
`Prop` and would still have broken `Quot.ind`.

Stated once, as `interp_app_of_proof_sorted` (`SetModel/Cnst.lean`), rather than
rediscovered per constant: *whether `f` is a proof is decided by `L.srt Γ f` and
`M.ls` alone — `M.cnst` does not appear* — so if `f`'s type is a proposition,
`⟦f a⟧ρ = •` **no matter what the assignment gives to any constant occurring in
`f`.** That is a fact about `interp`, and every `Prop`-valued constructor of an
inductive will sit in exactly this position.

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
truth check. It has now caught **four** level-sensitive splits, and the fourth
(`Quot.mk`) changed the shape of the witness rather than the value of a
construction — so the check is not only about getting a definition right, it is
about not building the wrong object at all.

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

## `LevelAssign` was unsatisfiable — found by audit, now repaired

A tree-wide audit of instance-free classes asked whether a `LevelAssign` could
be built for a small concrete environment without `sort_inv`. The answer turned
out to be sharper than the question: **no `LevelAssign` existed for any
environment, at any parameter count, because two of its fields contradicted each
other.**

`lvl_wf` demanded `(lvl Γ A).WF nv` for every `Γ`, with no hypothesis that `Γ`
is well-formed. `lvl_sound` demanded `lvl Γ A ≈ u` whenever
`env.HasType nv Γ A (.sort u)`, with no hypothesis on `u`. But `IsDefEq.bvar`
has no side condition, so a context may hold `.sort (.param nv)` — not `WF nv` —
and then `Γ ⊢ .bvar 0 : .sort (.param nv)` is derivable. One field forces
`lvl Γ (.bvar 0) ≈ .param nv`, the other forces it `WF nv`, and no `WF nv` level
is equivalent to `.param nv`: its evaluation reads only the first `nv` entries
of the valuation, while `.param nv` reads the `nv`-th.

Machine-checked in `SetModel/LevelAssignUnsat.lean` (`no_levelAssign`), stated
against a local copy of the pre-repair structure so it stays checkable.

**The repair**, applied: `lvl_sound` gains `u.WF nv`.

```
lvl_sound : ∀ {Γ A u}, u.WF nv → env.HasType nv Γ A (.sort u) → lvl Γ A ≈ u
```

It cost the consumers nothing. The soundness induction runs on `IsDefEqStrong`,
whose every rule already carries `u.WF uvars` explicitly — the information was
threaded all along and the structure simply failed to ask for it. Fallout was
five files and entirely mechanical: `LevelAssign.mono`, `lvl_uniq`, `lvl_congr`,
`isProp_iff`/`isProof_iff` (the hypothesis goes *last*, so the implicit level is
fixed by the typing derivation before the WF proof is elaborated), the three
`Cnst.lean` introduction rules, and two `QuotInterp` call sites. `srt_sound`
needed no repair: it relates `srt Γ e` to `lvl Γ A`, both already constrained to
be `WF nv`, so there is no conflict.

### What the audit's narrow question actually answers to

Even at `VEnv.empty` the obligations are **not vacuous**: `sortDF`, `bvar`,
`forallEDF`, `lamDF`, `appDF`, `beta`, `eta` and `defeqDF` all fire without any
constants, so the empty environment still carries the full pure type theory.
After the repair, satisfiability is exactly:

* `lvl_sound` ⟺ **`sort_inv` for that environment** — two `WF` sort-typings of
  the same term have equivalent levels. The existing `LevelAssign.lvl_uniq`
  proves the converse in one line, so these are equivalent, not merely related.
* `srt_sound` ⟸ unique typing (two types of a term are defeq, hence have
  equivalent levels via `lvl_congr`).

So a witness is still blocked on `sort_inv`, at `VEnv.empty` as much as
anywhere. What changed is that the target is now *achievable* rather than
contradictory: before the repair, proving `sort_inv` would not have produced a
`LevelAssign`, because none exists.

### Why this was invisible

Every consumer of `LevelAssign` takes one as input; its only producer was
`LevelAssign.mono`, which takes one and returns one. No declaration in 547 ever
forced the fields to be jointly satisfied. This is the exact failure mode the
audit was commissioned to find, and the lesson generalises: **a structure whose
producers all consume the same structure has never had its fields tested.**
`CoherentOn` is in that position too — six producers, all six taking a
`CoherentOn` — and is the next one to check.

## `CoherentOn` is fine — and testing it turned up a seventh defect next door

### `CoherentOn`: satisfiable, all four fields firing

`SetModel/CoherentWitness.lean`, `coherentOn_witness`. The environment declares
one constant *and* carries one defining equation, so `const_type`, `defeq` and
`defeq_type` all fire; `const_congr` fires at every pair of level lists. A
witness over `VEnv.empty` alone would have proved much less — three of the four
fields are vacuous there, and that weaker witness is what "build one at `.empty`"
would have produced.

It is conditional on a `LevelAssign` (the fields mention `interp M L`), but holds
for an **arbitrary** one. So `CoherentOn` adds no obstruction of its own: it
becomes inhabited the moment `LevelAssign` does.

### `LevelAssign.Stable` is unsatisfiable — and soundness is currently vacuous

Applying the same criterion to `LevelAssign`'s neighbours found a seventh
defect, in the same family and with the same cause: **a relation that fails to
constrain something its consumers assume is constrained.**

`Ctx.InstN` is declared with `Γ₀ e₀ A₀` as *parameters*, and its `zero`
constructor is `Ctx.InstN 0 (A₀ :: Γ₀) Γ₀` — `e₀` does not appear. So
`Ctx.InstN Γ₀ e₀ A₀ 0 (A₀ :: Γ₀) Γ₀` holds for *every* `e₀`, with no requirement
that `e₀` have type `A₀`, or any type at all. `Stable.lvl_instN` then demands

```
L.lvl Γ₀ ((VExpr.bvar 0).inst e₀ 0) ≈ L.lvl (A₀ :: Γ₀) (.bvar 0)
```

for every `e₀` and `A₀`. The left side does not mention `A₀`; the right side is
pinned by `lvl_sound` to `A₀`'s own level. Taking `A₀ := .sort .zero` and
`A₀ := .sort (.succ .zero)` with the same `e₀` forces `.zero ≈ .succ .zero`.

Machine-checked as `no_stable` in `SetModel/LevelAssignUnsat.lean`.

**Consequence, stated plainly: every theorem taking `L.Stable` as a hypothesis is
currently vacuous** — `soundAbove`, `sound`, `sound_nil`, `beta_sound`,
`eta_sound`, `interp_liftN`, `interp_inst`, and everything downstream. The
proofs are real and the case analyses are real, but until `Stable` is repaired
they are statements about an empty hypothesis.

**The repair**, not yet applied: add the hypothesis the consumers already have,

```
lvl_instN : … → env.HasType nv Γ₀ e₀ A₀ → ∀ B, L.lvl Γ (B.inst e₀ k) ≈ L.lvl Γ₁ B
```

and likewise `srt_instN`. A single `e₀` cannot have both `.sort .zero` and
`.sort (.succ .zero)` as its type, so the counterexample dies. The `liftN`
fields need no repair: `Ctx.LiftN` constrains everything it mentions.

### The `Stable` repair, applied — and it was mechanical, as predicted

`lvl_instN` and `srt_instN` now take `env.HasType nv Γ₀ e₀ A₀`. Fallout: four
files, every one of them supplying the fact it already had.

* `interp_inst` gains the hypothesis and threads it through its six recursive
  calls unchanged — the typing is about `Γ₀ ⊢ e₀ : A₀`, which does not vary as
  the recursion goes under binders, so `W.succ` reuses the same proof.
* `beta_sound` gains `env.HasType nv Γ e' A`, supplied in `soundAbove`'s `beta`
  case by the rule's own premise `Γ ⊢ e' : A`.
* `appDF_sound_type` gains `env.HasType nv Γ a A`, supplied by `appDF`'s premise
  `Γ ⊢ a ≡ a' : A`.

Nothing needed a fact the syntax side does not license, which was the outcome to
watch for: had some consumer genuinely lacked the typing, the model would have
been substituting terms the theory never permits substituting.

**Soundness is no longer vacuous.** `soundAbove`, `sound`, `sound_nil`,
`beta_sound`, `eta_sound`, `interp_liftN` and `interp_inst` now have a
hypothesis that is not provably empty.

### `CtxInvariant` paired with `hRd` is consistent, and the reason is the diagnostic

`CtxInvariant L R` is trivially satisfiable alone (`R := Eq`), so testing the
field in isolation proves nothing; it is always used with

```
hRd : env.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ)
```

and the pair is what matters. It is consistent, and *why* is the useful part:

> **The defect signature is a structure quantifying over a relation *parameter*
> that the relation's own constructors never constrain.**

* `IsDefEq.bvar` puts no condition on the context — `LevelAssign` broke.
* `Ctx.InstN` declares `e₀` as a parameter its `zero` constructor never mentions
  — `Stable` broke.
* `hRd`'s `A` and `A'` are **not** free: they arrive with a derivation
  `Γ ⊢ A ≡ A' : .sort u`, and that derivation is exactly what reconciles the two
  demands, through context conversion.

Machine-checked as `ctxInvariant_lvl_agrees` (`SetModel/CoherentWitness.lean`):
on every well-typed `B` — where `CtxInvariant.lvl` has content — the level
demanded in `A :: Γ` and in `A' :: Γ` coincide, by `lvl_sound` on both sides and
`IsDefEq.defeqDFC` to move the typing across.

This gives the audit a cheap test to run before building: **look at the
hypotheses of the relation the structure quantifies over, and ask which of its
parameters its constructors leave free.** Both defects were visible from the
inductive declaration alone.

### The pattern behind both, and where to look next

`LevelAssign` failed because `IsDefEq.bvar` has no side condition on the context;
`Stable` failed because `Ctx.InstN` has no side condition on the substituted
term. Both are **arbitrary-context / arbitrary-term defects**: a model-side
structure quantified over syntax more freely than the syntax side ever intends
to supply, and nothing forced the discrepancy because no witness existed.

The remaining structures in the tower, by the same criterion: `ModelData` is
plain data and trivially inhabited; `AxiomsValidated` is vacuous at `ds = []`;
`CtxInvariant` paired with `hRd` has now been tested and is consistent (above).
So have the three inductive-side structures — see below. **The audit of
`SetModel/` is complete: two defects, both repaired, everything else witnessed
or cleared at the declaration level.**

### The three inductive-side structures pass, and the reason sharpens the test

`IndSignature`, `IsStageSignature`, `IsSubsingletonSignature`: **none of them
quantifies over syntax at all.**

That is the sharper form of the diagnostic. `LevelAssign` and `Stable` broke
because they quantified over `List VExpr` and `VExpr` — objects the *syntax*
side supplies, at a generality it never intends to produce. These three quantify
only over their own set-theoretic data: every binder is bounded by `S.Q` or
`S.Fld q`, which the structure itself provides. There is no external relation
whose parameters could be left free, so the signature cannot fire.

So the triage procedure now has three steps, cheapest first:

1. **Does the structure quantify over syntax at all?** If not, the defect
   family cannot occur — its binders are bounded by data it owns.
2. **If it does: which parameters of the relations it quantifies over do those
   relations' constructors leave free?** Both defects were visible here, from
   the inductive declaration alone.
3. **Only then build a witness** — and make the fields do real work, or the
   witness is a formality.

`witSig` and `witSig_subsingleton` (`SetModel/CoherentWitness.lean`) witness the
first and third, with two distinct field values so `fld_det` is a genuine
injectivity requirement rather than a statement about a one-element set.
`IsStageSignature` needs its data to sit below a chosen stage, so a witness for
it is relative to a `k`; it is the least exposed of the three by step 1 and is
left at the declaration check.

## `Quot.ind` and `Quot.lift` are discharged

### `Quot.ind`: the spine's prediction held, with no level split

`quotIndFn_mem` (`SetModel/QuotInterp.lean`) is proved, sorry-free, on
`[propext, Classical.choice, Quot.sound]`. Five `pt_mem_interp_forallE_prop` in
a row, witness `•` at every one, **no case split on any level anywhere in the
membership proof.** The prediction recorded with the spine was that there would
be none, and it survived contact.

The reason is worth stating because it is a criterion, not an accident: every
codomain in `Quot.ind`'s type is `Sort .zero` **literally** — the motive `β`
lands in `Prop` by construction — so each `imax` above it collapses without ever
consulting `u`. Contrast `Quot.mk`, whose innermost codomain is `Quot α r : Sort u`
and whose whole type therefore becomes a proposition exactly at `u = 0`. **The
test is whether the innermost codomain is a syntactic `Sort .zero` or a
level-carrying expression**; that decides whether the witness needs a split,
before any proof is attempted.

The one split that does occur is confined to `interp_quotIndMkAp`, which
computes a *value*: at `u.eval = 0` the partial application `Quot.mk α r` is
proof-sorted and `interp_app_of_proof_sorted` returns `•` without consulting
`M.cnst` at all — so that branch needs neither the constant hypothesis nor
`Quot.mk`'s value chain. That is what keeps the split out of the membership.

### `Quot.lift`: proved, and it needed everything the other three did not

`quotLiftFn_mem` is proved, sorry-free, same three axioms. It is the first of
the four `Quot` operations that is genuinely different in kind, in four ways:

1. **Two universe parameters.** The witness splits on `v`, the *codomain* level:
   the type is a proposition exactly when `imax u v = 0`, i.e. when `v = 0`. The
   carrier level `u` never degenerates the witness — it only changes the value.
   So the standing `u = 0` check needs restating: **run it on every level
   parameter separately, and expect the answer to differ between them.**
2. **A hypothesis binder that is eliminated, not carried.** Without `c` the
   image of a class under `f` need not be a singleton and the witness would not
   land in `β` at all. This is the only place in the `Quot` block where a `Prop`
   argument is consumed, and it is exactly why `Quot.lift` is the first whose
   type mentions a second constant (`Eq`). `EqSpec` (`SetModel/PreludeSpec.lean`)
   is what turns the *existence* of `c` into an equation between values;
   `quotLift_respects` is the only consumer.
3. **`quotEqv`'s elimination rule was needed, and the `Π₁` form paid off.**
   `quotEqv` was defined by its universal property rather than as `lfp`, for
   definability, and the docstring recorded that nothing needed the two to
   agree. `Quot.lift` needs to stretch `c` — which speaks only about `r` — over
   the closure. With the `Π₁` form that is one line: instantiate the universal
   property at the kernel of `f`, which is `eqvStep`-closed exactly because `f`
   respects `r`. Going through `eqvClosure_least` would first have required
   proving the two definitions equal. **A definition chosen for one reason
   (definability) turned out to be the one with the cheap elimination rule.**
   `isEquivalenceOn_quotEqv` is likewise proved directly, without the
   comparison.
4. **The value is a union, not a choice.** `quotLiftVal f q i` is
   `⋃ˢ (image f q)` above a `Prop` carrier and `f ‘ •` at one. No appeal to `AC`
   and no representative selection: `c` makes the image a singleton and `⋃ˢ`
   reads it out. `exists_quotient_lift` (`SetModel/Universe.lean`), which
   produces a lift by an existential, is *not* usable here — it gives `∃ g`, and
   a `mkLam` needs a definable function of the parameters.

The ι-rule at the value level (`quotLiftVal_quotMkVal`) holds in both branches,
and the degenerate one is not vacuous: at a `Prop` carrier `α ⊆ {•}`, so the
representative `a` *is* `•` and the two sides agree on the nose.

### `quotDefEq` is **not** the next step after `Quot.ind` — `Quot.lift` was

The handover into this stage read "`Quot.ind`, then `quotDefEq`". That skips a
prerequisite: `quotDefEq` is
`fun α r β f c a => Quot.lift α r β f c (Quot.mk α r a) ≡ f a`, so both its
obligations are about a six-λ nest whose left-hand body is a full `Quot.lift`
application. Nothing about it can be stated before `Quot.lift`'s denotation
exists. `Quot.lift` was built first, and then `quotDefEq` — see below. What
`quotDefEq` needed, and which is now all built:

* **`Quot.lift`'s application spine** — a `¬IsProof` for each of the five proper
  prefixes of `Quot.lift α r β f c`, and `isProof_iff` wants a typing *and* a
  sort derivation for each. The types are the successive `inst`s, and they are
  worth recording because they are easy to get wrong by hand. Over the context
  `[.bvar 4, quotLiftC v, quotLiftFTy, .sort v, quotRelTy, .sort u]` (indices
  `0 = a, 1 = c, 2 = f, 3 = β, 4 = r, 5 = α`), with `E := .const Eq [v]`:

  | after | type |
  |---|---|
  | `Quot.lift α` | `∀ (.bvar 5) (.bvar 6), Sort 0` → `∀ Sort v, ∀ (∀ (.bvar 7), .bvar 1), ∀ (∀ (.bvar 8), ∀ (.bvar 9), ∀ (r a b), E …), ∀ (Quot (.bvar 9) (.bvar 3)), .bvar 3` |
  | `Quot.lift α r` | `∀ Sort v, ∀ (∀ (.bvar 6), .bvar 1), ∀ (∀ (.bvar 7), ∀ (.bvar 8), ∀ ((.bvar 8) a b), E …), ∀ (Quot (.bvar 8) (.bvar 7)), .bvar 3` |
  | `Quot.lift α r β` | `∀ (∀ (.bvar 5), .bvar 4), ∀ (∀ (.bvar 6), ∀ (.bvar 7), ∀ ((.bvar 7) a b), E (.bvar 7) …), ∀ (Quot (.bvar 7) (.bvar 6)), .bvar 6` |
  | `Quot.lift α r β f` | `∀ (∀ (.bvar 5), ∀ (.bvar 6), ∀ ((.bvar 6) a b), E (.bvar 6) ((.bvar 5) a) ((.bvar 5) b)), ∀ (Quot (.bvar 6) (.bvar 5)), .bvar 5` |
  | `Quot.lift α r β f c` | `∀ (Quot (.bvar 5) (.bvar 4)), .bvar 4` |

  Every one is non-proof exactly when `v ≠ 0`, since each sort bottoms out at
  `imax u v`.
* **`Quot.mk` at indices `(5, 4, 0)`** — the analogue of `quotMkAp1/2_type`,
  which are stated at `(3, 2, 0)` for `Quot.ind`'s context.
* **`interp_lam_congr`** — two `lam`s with the same binder type have the same
  denotation once their bodies do. *This needs the two bodies to agree on
  `IsProof`, which is not free*: `IsProof` is syntactic, so it has to come from
  `srt_congr` on a defeq derivation, or from typing derivations for both bodies.
  That is the reason the equation cannot be reduced to its bodies without the
  spine above.
* **The membership obligation is the cheap half.** `⟦lhs⟧ ∅ ∈ ⟦type⟧ ∅` can be
  proved for the *right*-hand nest (`fun α r β f c a => f a`) and transported
  across the equation; its bottom is `f ‘ a ∈ β`, which is already
  `quotLift_f_props`.

## `quotDefEq` is discharged, and the split criterion worked prospectively

`quotDefEq_ok` (`SetModel/QuotInterp.lean`) delivers **both** obligations in the
exact shape `coherentOn_addDefEqFold` consumes — the level list destructured
from `us.length = quotDefEq.uvars`, both `Above` wrappers discharged by
`Above.pure`. Sorry-free, `[propext, Classical.choice, Quot.sound]`. That
statement being accepted is itself the check that `quotDefEq_eq` and
`quotDefEq_mem` are the right two propositions: it is copied from the fold's
hypothesis rather than restated.

**The level-split criterion was run before writing a line, and it held.** The
type is `∀ α r β f c (a : α), β`; the innermost codomain is `β`, a
level-carrying expression of sort `v`, and every sort in the chain bottoms at
`imax u v`. Prediction: **`v` splits, `u` does not.** Outcome: no proof in the
`quotDefEq` layer branches on `u`. The `u`-split lives entirely inside
`interp_quotDefMkAp` and `quotLiftVal_quotMkVal`, both already proved in both
branches, so it never surfaces. This is the first time the criterion was used to
*schedule* work rather than to explain a surprise after the fact.

### The cross-check passed, and that is the report

The five successive `inst` types of `Quot.lift`'s partial applications were
computed by Lean, transcribed, and then checked by `appDF` — which produces the
`inst` itself and will not elaborate against a wrong transcription. All five
elaborated first try, as did the five sort derivations above them. The
cross-check is mandatory, not diligent; recording that it found nothing is the
point of running it.

### Four copies of one shape that are *not* shifts of one another

`Quot.lift`'s hypothesis `∀ a b, r a b → f a = f b` appears once in each of
`quotLiftTy2 … quotLiftTy5`, and it is tempting to write one lemma and reuse it
at four shifts. **That is wrong.** Each `inst` step replaces a *different*
binder, so the `β` and `f` references land on different binders depending on how
many have been consumed: at `quotLiftTy5` the motive is still the outer
`quotLiftFTy` (index 5), while at `quotLiftTy4` and below it is the freshly
bound one (index 3). The two lowest copies *do* coincide with the already-defined
`quotLiftRab` and `quotLiftEqAp` — but only because there both `β` and `f` are
freshly bound and land exactly where `Quot.lift`'s own spine puts them.

The general form: **under a chain of instantiations, a repeated subterm's de
Bruijn indices are not a uniform shift of the original; they depend on how many
of the binders it refers to have already been consumed.** Assume the shift and
you write four wrong lemmas that all look right.

### Peel by type agreement, split only at the bodies

`interp_lam_congr` needs the two bodies to agree on `IsProof`, and `IsProof` is
syntactic — it does not follow from the bodies being pointwise equal. But it
*does* follow from the two bodies having the **same type**, via `isProof_iff`
twice, and that holds at every level of a defeq between two nests over the same
binders. So all six λs peel **uniformly, with no case split**, and the level
split appears only once, at the bodies. At `v = 0` both bodies are applications
of a proof-sorted head — `Quot.lift α r β f c` on the left, `f` on the right — so
`interp_app_of_proof_sorted` gives `•` on both sides without consulting the
constant assignment; above it, the ι-rule fires. This is the shape to reuse for
every ι-rule the inductive layer will need.

### The `Quot` block's constant equations are triangular, not recursive

Worth recording before the inductive block asks the same question. The
denotations depend on `M.cnst` as follows:

| constant | its denotation mentions |
|---|---|
| `Quot` | — |
| `Quot.mk` | — |
| `Quot.lift` | `Eq`, `Quot` |
| `Quot.ind` | — (it is `•`) |

So the four defining equations `M.cnst n us = …Fn …` can be satisfied in
sequence, with no fixpoint, in exactly the order `quotNames` already lists.
`quotIndFn_mem` and `quotLiftFn_mem` take the *other* constants' equations as
hypotheses, which is consistent precisely because no denotation mentions its own
name. **Check this triangularity before assuming an inductive block's assignment
needs a fixpoint** — for `Quot` it does not, and the reason is visible from the
binder types alone.

## The `PreludeSpec` vacuity audit: `EqSpec` is satisfiable

`Quot.lift`'s and `quotDefEq`'s obligations are stated *against* `EqSpec`, which
is a `PreludeSpec` statement — a `Prop`-valued definition nothing had ever had to
meet. That is precisely the shape that can be quietly unsatisfiable, and a cone
discharged against an unsatisfiable hypothesis is conditional on nothing. The
tell in every vacuity finding this project has had is identical: **nobody had
exhibited a witness.**

**`preludeSpec_satisfiable` (`SetModel/PreludeSpec.lean`) exhibits one**, and it
is joint — a single `ModelData` meeting `EqSpec` at every level, `IffSpec`, and
`NonemptySpec` at every level, over an arbitrary `κ` and `ls`. Sorry-free,
`[propext, Classical.choice, Quot.sound]`. Stating the three separately would
have left open the failure mode that has bitten this development three times:
each conjunct fine alone, the conjunction unsatisfiable.

Three things about how the witness is built are worth keeping:

* **It does not use a `LevelAssign`.** That structure was itself found
  unsatisfiable once and repaired; building the prelude witnesses on top of it
  would reproduce the hole the audit exists to close. `IsSeq` is the raw form of
  `interpCtx_domain`'s conclusion — internal function, domain a numeral — and
  needs only `κ`, `ls` and `𝗭𝗙`.
* **It is environment-passing, not capturing.** The naive witness captures `α`
  in the inner λ's *domain*, and then the outer `mkLam`'s fibre map is no longer
  jointly definable. `SetModel/Definability.lean` says this about `interp`; it is
  equally true of anything built alongside it, including a throwaway witness.
* **Both branches of every `if` are exercised.** A witness whose conditional only
  ever took one branch would say very little. `eqFn_refl` and `iffFn_same` fire
  the `then` branch, `iffFn_diff` and `nonemptyFn_empty` fire the `else` branch
  **unconditionally** — `UProp` holds two distinct elements with no chain
  hypothesis at all — and `eqFn_distinct` fires `Eq`'s `else` branch under the
  same `IsInaccessibleChain` the rest of the model already assumes. `Eq`'s
  `else` branch *cannot* be reached without a chain, because at `U κ 0` every
  carrier is a subset of `{•}` and so has at most one element.

The audit came back clean. Recording that plainly is the point: an audit that
only ever reports failures decays into one nobody runs.

### Stated once, generally: peel by type agreement

`interp_lam_congr` and `interp_lam_congr_of_type` now live in
`SetModel/Cnst.lean` rather than in `QuotInterp`, because every ι-rule the
inductive layer needs will take the same step. The trap they package:

> `interp` sends `.lam A b` to `•` when `b` is a proof and to a `mkLam`
> otherwise, so an equation between two `lam`s needs the bodies to **agree on
> `IsProof`** before their pointwise equality is of any use — and that agreement
> does *not* follow from the bodies denoting the same thing at every valuation,
> because `IsProof` is syntactic. It follows from the two bodies having the
> **same type**, which for a defining equation is automatic: both sides are typed
> at `df.type`.

So a defeq obligation peels its whole nest uniformly, with no case analysis at
any binder, and whatever level split it needs appears exactly once, at the
bodies. `quotDefEq_eq` is now six calls to `interp_lam_congr_of_type`.

### Running the same audit one level down: the cone's real open hypothesis

`EqSpec` was the hypothesis I was asked to witness, and it is witnessed. But the
audit is only worth what its *next* question is worth, so: what else in the
`Quot` cone has never been exhibited?

Every result in `SetModel/` is parameterised by `L : LevelAssign envF nv`, and
**nothing anywhere exhibits one.** `CoherentWitness.lean` says so explicitly —
`coherentOn_witness` takes `L` as a hypothesis and its docstring records that "no
unconditional witness is possible while `LevelAssign` [is unwitnessed]".

This is **not** a new hidden vacuity: it is the project's tracked item #1, and
`SetModel/Interp.lean`'s own header records it. It matters anyway, because it
fixes what the `EqSpec` result does and does not buy. `EqSpec` is now discharged
outright; the `Quot` cone's one remaining unwitnessed hypothesis is
`LevelAssign`, and that is blocked on the two `sorry`s in
`Theory/Typing/Injectivity.lean` (lines 124 and 128 — the `trans` and
`proofIrrel` cases of `sort_inv`). No further set-model work changes that, and
no set-model result should be described as unconditional until it does.

Worth noting for scale: the *unguarded* form of `LevelAssign` was not merely
unwitnessed, it was `IsEmpty` for **every** `env` and `nv` (`no_levelAssign`,
`SetModel/LevelAssignUnsat.lean`). The guarded form has not been shown empty and
is not expected to be — but it has also not been shown inhabited for a single
`(env, nv)`, which is a weaker and possibly reachable target than the general
construction.

### A recorded claim that deserves testing before it is relied on

`SetModel/Interp.lean`'s header states that `LevelAssign` is "exactly
`IsDefEqU.sort_inv` in functional form (plus choice)". **I think that
understates it, and it is worth checking before anyone plans around it.**

`lvl` can indeed be built from `sort_inv` and choice: pick any WF sort of `A`;
`lvl_sound` then needs only that two WF sorts of the same type agree, which is
`sort_inv`. But `srt_sound` says `srt Γ e ≈ lvl Γ A` for **every** `A` typing
`e`, and `srt` can only be defined by choosing *one* such `A`. Discharging it
therefore needs `lvl Γ A ≈ lvl Γ A'` for any two types of the same term — and
nothing links their sorts without first knowing `A ≈ A'`, which is *unique
typing* (`Theory/Typing/UniqueTyping.lean`, itself carrying a `sorry`), strictly
stronger than `sort_inv`.

This is flagged, not asserted: I have not machine-checked either direction, and
today's record is that both directions get refuted. The concrete test is to
attempt `levelAssign_of_sort_inv` and see which hypothesis the `srt_sound` field
actually demands. That construction does not exist anywhere in the tree, and
building it — conditionally, so that `LevelAssign` falls out the moment
`sort_inv` lands — looks like the highest-value self-contained piece the set
model has left.

## Scoping the `.induct` step, and one blocker removed

Surveyed the whole bridge before starting it. The picture is sharper than the
open-items list suggests.

**Both ends are finished; the middle is empty.** The model side ends at *sets* —
`Ind S D`, `indCtor S q a f`, `indRec S D R e he`, with `indRec_mem_stage` and
`indRec_indCtor_stage` (`SetModel/IndStage.lean:125, :130`) giving membership and
the ι-rule outright, and `Ind_mem_U_stage` (`IndCard.lean:499`) putting the
family in the right universe. The syntax side ends at *`VExpr`s* — `D.recType j`,
`D.iotaRule j q C`, `D.allConsts` (`Theory/Inductive/Decl.lean`). **Nothing
connects them.** `interp` does not occur in any of the three inductive model
files; `VInductDecl'` occurs in `SetModel/` only in prose. `cnstOf`'s `.induct`
line uses `D.allNames : List Name` and nothing else.

So the two obligations the step owes — `o n us ∈ ⟦ci.type.instL us⟧ ∅` for each
of `D.allConsts`, and the `coherentOn_addDefEqFold` pair for each of
`D.iotaRules` — have no `interp`-level counterpart yet. `indRec_mem_stage` is
membership in an *abstract* codomain set `R`, not in an `interp`-produced one;
`indRec_indCtor_stage` is an equation between set-level values, not between
`⟦lhs⟧ ∅` and `⟦rhs⟧ ∅`. Contrast `quotLiftFn_mem` and `quotDefEq_ok`, which are
in the right shape. Nothing of that shape exists for inductives.

**`docs/model-interface.md` §2 already has the plan** — `interpSig`, its
field-by-field translation table, and `interpSig_stage` / `interpSig_wf`. It
names two blockers, both said to be owed by the syntax side. **One of them was
already proved and nobody had noticed.**

### `interp_congr` is a corollary of soundness, not an open obligation

`model-interface.md` §4 says "**Without `interp_congr` there is no first step at
all**, so `interp_congr` has to be stated and proved before `interpSig_wf` can
even be stated." It does not exist in the tree under that name — but
`SoundInduction.lean`'s `Sound` has *two* fields, and the `eq` field is
`EqSound M L Γ e₁ e₂`, which unfolds to exactly
`∀ ρ ∈ interpCtx M L Γ, ⟦e₁⟧ρ = ⟦e₂⟧ρ`. So `interp_congr` is `sound` with the
`type` half projected away, and it is now stated and proved as
`SetModel/SoundInduction.lean:interp_congr`, in three lines, holding for
arbitrary `B` rather than only at `.sort u`.

**But read the caveat before planning around it.** It is `Above`-wrapped,
because soundness is: what is available is "there is a threshold `m` such that
any chain of `m` inaccessibles makes the two denotations agree", *not* an
unconditional equality of `DefFun`s. That is enough to **prove** things about a
construction and not enough to **define** one by rewriting `⟦F.type⟧` to `⟦A⟧`,
which is how §2 phrases `interpSig`'s first step. So the blocker is not removed
so much as **relocated**: what `interpSig` needs is either an unconditional
`interp_congr` (a different theorem — soundness would have to be de-`Above`d,
which the module header of `SoundInduction.lean` explains cannot be done by
bounding the chain) or a formulation of `interpSig` that only ever needs the
`Above` form.

That is a design question for whoever takes the bridge, and it is better asked
now than discovered after `interpSig` is written. The second blocker,
`NoBlock.indep`, is untouched and is genuinely syntax-side.

## Settled: `interpSig` can be formulated wrapped-only. No unconditional `interp_congr` is needed.

The question was whether `interpSig` can be written so it only ever *uses* the
`Above`-wrapped `interp_congr`, or whether it genuinely needs an unconditional
one. **It can. The split is data versus properties, and it falls on the right
side of the line.**

### Why: the oracle's *values* are unconditional, its *properties* are not

`cnstOf`'s `.induct` line is `oracleExtend o D.allNames …`, and `o : Name →
List VLevel → V` is a plain function parameter — **data, supplied with no chain
in sight.** So an inductive's constructor and recursor *values* have to be
actual sets, defined unconditionally. That rules out the tempting shape
`Above M (∃ S : IndSignature V, …)`: you cannot extract data from an `Above`.

But `OracleOK`'s own two fields are **already** `Above`-wrapped
(`Cnst.lean:183–186`), as are `Coherent`'s four and the pair
`coherentOn_addDefEqFold` consumes. So every *property* of the signature may be
wrapped, and every consumer already expects it that way.

The split is therefore:

| piece | status | why |
|---|---|---|
| `interpSig D hD levels params : IndSignature V` | **unconditional data** | its fields are `⟦A⟧` for the block-free `A` that `VIndCtor.WF`'s `pos` clause provides; extracting `A` is `Classical.choice` on `∃ A, D.NoBlock A ∧ IsDefEqType … F.type A` (`Decl.lean:288`), a **chain-free** existential |
| `Fld_definable` and friends (bundled in the structure) | **unconditional** | definability of `⟦A⟧` is `(interp …).definable`; no congr |
| `interpSig_stage`, `interpSig_wf`, the `⟦ctorType⟧` connection | **`Above`-wrapped** | all `Prop`s, and every consumer takes `Above` |

### What §4 actually needs, and it is not what it says

`docs/model-interface.md` §4 says "**Without `interp_congr` there is no first
step at all**, so `interp_congr` has to be stated and proved before
`interpSig_wf` can even be stated." That **conflates defining with relating.**
`Fld q` is *defined* from `A`; knowing `⟦F.type⟧ = ⟦A⟧` is never needed to write
the definition down. It is needed only to carry a membership proved at `A` over
to `F.type`, which is a `Prop`.

That step is now machine-checked in the wrapped form: `above_mem_congr`
(`SetModel/SoundInduction.lean`) transports a membership across a definitional
change of type entirely inside `Above` — the congr's threshold and the
membership's threshold merge, and nothing is ever unwrapped.

### The algebra that made it possible, and that was missing

`Above` had only `pure` and `imp` — enough to *carry* one wrapped fact, not
enough to *combine* two, which is what any construction with several
chain-dependent properties needs. Added, all sorry-free:

* `Above.and` — two thresholds merge by `max`, because `IsInaccessibleChain` is
  downward closed (`IsInaccessibleChain.le`);
* `Above.imp₂`;
* `Above.forall_mem` — finitely many wrapped facts come under one threshold,
  which an inductive block needs, one obligation per constructor.

### Price of the alternative, if anyone still wants it

An unconditional `interp_congr` would require de-`Above`-ing soundness, and
`SoundInduction.lean`'s header already explains why that cannot be done by
bounding the chain: a derivation's premises can need arbitrarily higher
inaccessibles than its conclusion, so no bound on the conclusion is inherited,
and the bound cannot be moved onto `L` either since `L.lvl Γ (.sort k) = k+1`
for every `k`. Getting it would mean a model with a proper class of
inaccessibles, or a reflection argument — **a change to the model's
foundational hypothesis, not a lemma.** Against that, the wrapped route costs
three combinators and a transport lemma, all now built.

**Recommendation: build `interpSig` unconditionally, keep every property
wrapped, and do not weaken `WF.pos` to a syntactic `NoBlock`.** The remaining
genuine blocker is `NoBlock.indep`, which is syntax-side and untouched.

## `interpSig`, built on the settled shape: `SetModel/IndInterp.lean`

New file, sorry-free, `[propext, Classical.choice, Quot.sound]`, in the build
(`Lean4Lean.Theory.*` globs recursively, confirmed by the olean).

**The factoring is the design decision.** `interpSig` splits into two halves
that fail for entirely different reasons, so they are kept apart:

* **the assembly** — turn per-constructor data into an `IndSignature`,
  discharging its four *bundled definability obligations*. Built.
* **the syntactic computation** — read that data off a `VInductDecl'`. De Bruijn
  bookkeeping against `Decl.lean`, and the only place `NoBlock.indep` is needed.
  Not built.

Splitting them makes the assembly checkable now and reduces what is left to
"compute a `CtorData` from a `VIndCtor`".

### What is built

`mkIndSignature (Idx params : V) (cs : List (CtorData V)) : IndSignature V` —
tags are `0 … cs.length-1`, every component dispatches on the tag, and **all
four definability proofs are discharged**. That was the real difficulty: an
`IndSignature` bundles `Fld_definable`, `Pos_definable`, `posIdx_definable` and
`resIdx_definable`, so nothing can be handed over until every component is
definable jointly in all its arguments.

The primitives beneath it, each general and reusable:

| primitive | what it is |
|---|---|
| `teleFun` | the dependent sum of a telescope of **definable domains**, `DefFun`-valued; `Idx`, `Fld`, `Pos` are all instances. With `teleFun_isSeq` and `teleFun_read`, so its elements are usable as `interp` valuations |
| `tagCase₁/₂/₃` | definable dispatch on a constructor tag, with `tagCase₁_at` reading it back |
| `ite_eq_definable₁/₂/₃`, `ite_rel_definable₂` | definable two-way splits, on an equality and on a definable relation |
| `tagUnionF` | the `n`-ary tagged union (`disjUnion` is only binary), definable in the valuation |
| `tagPayload`, `tagSel₂` | decoding a tagged recursive position, and dispatching on its tag |
| `teleDomains`, `argsVal` | the `VExpr` → `DefFun` bridge, and index-tuple construction |

**`teleFun` is deliberately not stated over `List VExpr`.** A recursive field's
stored type mentions the block, so `Fld`'s telescope is *not* the syntactic one.
Taking `List (DefFun V)` lets the caller supply `⟦A⟧` at a non-recursive field
and a singleton at a recursive one, and keeps the block-freeness question out of
the assembly entirely.

### Two things worth keeping

**`DefFun`-valued recursion is forced, not stylistic.** `mkFamUnion` takes the
fibre map's definability *as an argument*, so each step of `teleFun` needs the
previous step's definability at definition time. A bare `V → V` recursion cannot
be written at all. This is the same reason `interp` is `DefFun`-valued, and it
will recur in every list-indexed set construction.

**No Kuratowski projection was needed, and adding one would have been the wrong
move.** `posIdx` receives a position `⟨tag, payload⟩ₖ` and needs the payload;
Foundation has `kpair` and `kpair_inj` but no projection, and writing one needs
a bounded search. It is unnecessary: `{⟨u, v⟩ₖ}` is already an internal
*function* sending `u` to `v` — Foundation proves `IsFunction ({⟨x,y⟩ₖ} : V)` —
so the payload is `({b} : V) ‘ tag`, and definability is `value`'s.
**Reusing an existing definable operation beat adding a primitive**, which is
the same check that found `interp_congr` inside `Sound.eq`.

### `definability` diverging, and the fix that is not a bigger limit

`tagSel₂_definable` failed with `maximum recursion depth`, and **raising
`maxRecDepth` did not help** — this was `SetModel/Definability.lean`'s
documented *first* failure mode, genuine divergence rather than depth:
`tagPayload` unfolds to `value` of a singleton and the search chases the
unfolding. The fix is to **abstract the offending function** so the search
cannot unfold it — `eq_kpair_definable` is stated with `t` a variable and
applied at `tagPayload i`. Cheaper than any limit, and the general form is:
*when `definability` diverges, generalise the sub-term it is chasing into a
hypothesis.*

### What remains for `.induct`

1. **`CtorData` from `VIndCtor`** — the syntactic half. Needs `Classical.choice`
   on `WF.pos`'s block-free existential (chain-free, so unconditional), the
   context conventions of `Decl.lean`, and `NoBlock.indep`.
2. **`interpSig_stage` / `interpSig_wf`** — `Above`-wrapped, per §4.
3. **Connecting to `OracleOK`** — wrapped throughout; `Above.and`,
   `Above.imp₂`, `Above.forall_mem` and `above_mem_congr` are in place for it.

## `NoBlock.indep`, measured — and it is a third consumer of the same family

Taken first, as the only piece of the syntactic half whose difficulty was
unmeasured. It **splits into two halves of completely different difficulty**,
which is why measuring it was worth doing before the transcription work:

1. **Model half** — *if `A` never reads those positions, `⟦A⟧` ignores them.*
   **Built**: `interp_avoids` (`SetModel/IndInterp.lean`), unconditional,
   sorry-free, with `AvoidsAt` (a position-level "never reads" predicate, stated
   on positions rather than de Bruijn indices because that is what `interp`
   reads) and four `mk*_congr_arg` lemmas for `mkFamUnion`/`mkLam`/
   `mkForallProp`/`mkForallType`. All independently reusable.
2. **Syntactic half** — *a block-free, well-typed field type never reads a
   recursive-field position.* Open. `VExpr.NoConsts` is about constants only
   (`.bvar _ => True`), so block-freeness says nothing about bound variables on
   its own; this is where all the content is.

### The measurement

It is **true**, and every branch of the argument bottoms out in the same place.
If a block-free well-typed `A : Sort ℓ` reads a recursive-field variable
`r : I p π`, then `r` occurs either as an argument (forcing a block-free
function of type `∀ _ : I p π, B`, which no parameter, earlier field, earlier
constant or `lam` can supply), or as a binder type (forcing `I p π` to be a
sort), or in head position (forcing `I p π` to be a Π).

The last two, and the base case of the first, are **disjointness of a constant
application from the other head forms**:

| what it needs | status |
|---|---|
| `IsDefEqU.const_forallE_inv` — a constant application is not a Π | **stated, `sorry`** (`Theory/Typing/Injectivity.lean`) |
| "a constant application is not a sort" | **not stated anywhere** |

So `NoBlock.indep` is not an isolated obligation. It is a **third independent
consumer of `Injectivity.lean`'s disjointness family** — alongside
`LevelAssign` (via `sort_inv`) and the injectivity stream's own targets — plus
one statement nobody has written down. That reframes it: the question is not
"how hard is `NoBlock.indep`" but "is the disjointness family worth another
consumer".

**Recommendation: take `model-interface.md` §2's own escape hatch.** Replace
`Fld : V → V` by a monotone `Fld : V → V → V` over the family's current
approximation. It needs *no* disjointness at all, and its cost is bounded and
known — a redo of the recursor's rank argument, since the non-recursive data
would then itself contain family elements. Against an open family that has
resisted all day and now has three consumers, a bounded model-side change is the
cheaper side of the trade. The decision is not mine; both sides are now priced.

**Method note.** This is the second time today that measuring the unknown first
paid: the answer was not "hard" or "easy" but "*already blocked on something we
are already blocked on*", which is only visible once you push the reduction to
its base case. A difficulty estimate that stops at "this looks hard" would have
hidden that the blocker is shared.

## The escape hatch, built — and it was cheaper than priced

Ruled in and landed in `SetModel/IndInterp.lean`, sorry-free,
`[propext, Classical.choice, Quot.sound]`. `IndSignature₂` carries
`Fld : V → V → V` over the family's current approximation plus one new field,
`Fld_mono`. A non-recursive field's domain may now mention family elements, so
**the disjointness family `NoBlock.indep` bottoms out in is never consulted.**

**Conservative in both directions, which is what kept it additive.**
`IndSignature.toTwo` embeds the old notion (`Fld` ignores the approximation);
`IndSignature₂.at` specialises back at a fixed approximation; and
`IndSignature.at_toTwo` is `rfl`. So `Inductive.lean`, `IndStage.lean` and
`IndCard.lean` — 1600 lines of proved material — were not touched.

`Fld_mono` is spent in exactly two places: `indStep₂_isMonotoneOn` and
`indStep_at_mono`. Everything else about the operator is unchanged, because the
signature enters `indStep` in exactly one clause.

### The priced cost was not incurred, and the reason is checkable

§2 priced this as "what needs redoing is the rank argument for the recursor,
since the non-recursive data `a` would then itself contain family elements".
**It does not need redoing.** The inequality driving the recursion is

> `rank_lt_indCtorVal : ⟨b, y⟩ₖ ∈ f → rank y < rank ⟨q, ⟨a, f⟩ₖ⟩ₖ`

and its proof descends `rank y < rank f < rank ⟨a,f⟩ₖ < rank ⟨q,⟨a,f⟩ₖ⟩ₖ` —
through the *recursive-position function* `f`, **never inspecting `a`**. What
`a` contains is irrelevant to well-foundedness.

The theorem that turns that observation into transfer:

> **`Ind₂_eq_Ind_at` — the generalised family is the ordinary family of the
> signature specialised at itself.**

`Ind₂` is not by definition an instance of `Ind` (its operator's signature moves
with the approximation), but at the fixed point they coincide. Both inclusions
are leastness arguments. Consequence: **every existing theorem about `Ind`
transfers by one rewrite** — constructors, no confusion, the induction
principle, the recursor, the ι-rule. `indRec₂_mem` is the worked instance, and
its proof is `rw [Ind₂_eq_Ind_at] at hp; exact indRec_mem …`.

The genuine adaptation cost is `IsStageSignature`, whose `fld_mem` must now be
asked of `Fld W q`. Bounded, mechanical, and not a rank argument.
`docs/model-interface.md` §2 is corrected.

**Method note.** The estimate that made this look expensive named the right
*structural* change and the wrong *consequence*: it reasoned that `a` would
contain family elements without checking whether anything downstream reads `a`.
Nothing does. **Before pricing a change by what it alters, check what actually
consumes the thing altered** — the rank lemma's three-line proof settled it.

## Stage, well-formedness, and the `OracleOK` connection

All sorry-free, `[propext, Classical.choice, Quot.sound]`.

**The `fld_mem` adaptation, which was the escape hatch's only real cost.**
`IsStageSignature₂` and `IndSignature₂.WF` ask their conditions of `Fld W q`
rather than `Fld q`, and it is enough to ask them of the approximations that can
actually arise — the subsets of the ambient `S.Idx ×ˢ vsetV k`. Both specialise
back at any such `W` (`IsStageSignature₂.at`, `IndSignature₂.WF.at`), so
together with `Ind₂_eq_Ind_at` the stage results transfer by one rewrite:
`Ind₂_mem_vsetV` and `Ind₂_mem_U_stage` are each three lines. The adaptation was
as bounded as predicted, and it is now done.

**`oracleOK_above` (`SetModel/Cnst.lean`).** `oracleOK_of` takes *unconditional*
obligations and wraps them with `Above.pure`, which is right for the `Quot`
primitives — every one is built outright. An inductive block's obligations
arrive **already wrapped**, and nothing has to be unwrapped to use them:
`OracleOK`'s two fields *are* `Above`s, so the lemma is the identity.

Stating an identity is worth doing exactly when the fact it records is one
people get wrong. §4 of `model-interface.md` priced an entire unconditional
`interp_congr` on the assumption that the wrapped form would not do; the whole
`.induct` step's shape turns on the consumer already accepting it. A named
lemma makes that checkable instead of remembered.

### The pattern this round is built on, named

`Ind₂_eq_Ind_at` is the reason none of this cost what it was priced at, and the
shape generalises:

> **Reach for the identification theorem before the porting effort.** Do not
> port the theory to the generalised object; prove the generalised object *is*
> the ordinary object at a particular instantiation, and every existing theorem
> transfers by one rewrite.

Its precondition is the other half: **make the generalisation conservative in
both directions** — an embedding one way (`IndSignature.toTwo`), a specialisation
back (`IndSignature₂.at`), and an identity connecting them
(`IndSignature.at_toTwo`, `rfl`). Then nothing downstream has to choose which
notion it was written against, and the change is additive rather than a
migration. Expect the inductive layer to force more generalisations; this is the
shape to reuse for each.

## `CtorData` from `VIndCtor` did not land, and why is the finding

I went to build it as transcription. It is not transcription: **the escape hatch,
as one paragraph, does not determine a design that satisfies the constructor's
typing obligation.** This only became visible on attempting the use, which is
the third time today that has been the thing that found the problem.

**Nothing landed is invalidated.** `IndSignature₂`, `Ind₂_eq_Ind_at`,
`indRec₂_mem`, `Ind₂_mem_U_stage`, `oracleOK_above` are theorems about *any*
`IndSignature₂` and remain machine-checked. What is open is whether a
`VIndCtor` can be *translated into* one.

### The obstruction, precisely

`a` and `f` are quantified **independently** everywhere the model consumes them
— quoted from `SetModel/Inductive.lean`:

```lean
indStep …   := {p ∈ … ; ∃ q ∈ S.Q, ∃ a ∈ S.Fld q, ∃ f ∈ (D ^ S.Pos q a : V), …}
IsIndCarrier.ctor_mem  : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, ∀ f ∈ (D ^ S.Pos q a : V), …
IsMinorPremise.mem     : ∀ q ∈ S.Q, ∀ a ∈ S.Fld q, ∀ f ∈ (D ^ S.Pos q a : V), ∀ h …
```

Nothing ties `f` to `a`. That forces a choice, and both horns fail:

* **Put the family elements in `a`** (what §2 says: "the non-recursive data `a`
  would then itself contain family elements"). Then `f` *duplicates* them, and
  `IsIndCarrier`'s `∀ f` admits pairs where `f` disagrees with `a`'s copies, so
  the carrier holds junk. Avoiding that forces `Pos q a = ∅` — at which point
  `h ∈ R ^ ∅` carries no recursive results and **the minor premise `e q a f h`
  receives none**. The recursor stops computing.
* **Keep `a` non-recursive, justified by *some* filler from `W`.** Then `Fld` is
  monotone and definable, but `indStep` supplies an *arbitrary* `f`, unrelated
  to the filler that justified `a`. The family is too big and the constructor's
  `const_type` obligation — which needs the field types checked against the
  `f` actually supplied — fails.

### Correcting my own earlier report

I wrote that the escape hatch's priced cost, the recursor's rank argument, "is
not incurred", having checked `rank_lt_indCtorVal` and found it never inspects
`a`. **That is true and it answered the wrong question.** Well-foundedness is
untouched; what breaks is the recursor's *interface* — `IsMinorPremise` and
`IsIndCarrier`, which quantify over `f` independently of `a`. I applied "check
backward from the consumer" to one consumer and not to the two that decide it.
The rule catches this only if you enumerate the consumers rather than the first
one that comes to hand.

### The two ways to close it

1. **Prove `NoBlock.indep`** — then `Fld q` never needs family elements, the
   original design stands, and none of this arises. Blocked on
   `Injectivity.lean`'s disjointness family, which the injectivity stream's
   stratified relation may be about to make cheap. *This is the moment to
   revisit that*, per the standing offer: what I now need is more than the rank
   argument.
2. **Generalise the model side further than §2 says** — replace the product
   `a ∈ Fld q`, `f ∈ D ^ Pos q a` by a signature-supplied *dependent set of
   argument tuples* `Args W q`, monotone in `W`, with `a` and `f` mutually
   consistent by construction. This works — the rank argument still descends
   through `f`, and the recursor keeps its interface — but it is a **real port**
   of `Inductive.lean`, not an additive change: `indStep`, `IsIndCarrier`,
   `IsMinorPremise`, `recStep` and `indRec` all quantify over the product and
   would quantify over `Args` instead. The identification-theorem pattern does
   *not* rescue it this time: the old theory is stated over the product shape,
   so old theorems are instances of the new ones rather than the reverse, and
   instances do not prove the general case.

**Recommendation: (1), if the disjointness family is close.** Option 2's cost is
the thing the escape hatch was chosen to avoid, and paying it to avoid an
obligation that may be days from opening is the trade the original ruling
already rejected — with the difference that the price is now known to be a port
rather than a rank argument.

## The port: priced by enumeration first, then started

Ruled in after the disjointness family was shown to sit in `sort_inv`'s
equivalence class. **Priced by enumerating the consumers before committing**,
which is what the last round's failure taught, and the enumeration paid twice.

### It found a cheap alternative — and ruled it out

Put a redundant copy of the recursive fillers inside `a`, accept that the
carrier then holds junk pairs where the copy disagrees with `f`, and note that
the interpretation never produces them. Formation, the recursor and the ι-rule
all survive that; it would have avoided the port entirely.

**It breaks large elimination for subsingletons — in fact, not in proof.**
`IsSubsingletonSignature.fld_det` asks `resIdx q a = resIdx q a' → a = a'`; with
a redundant copy two fillers give the same result index and different `a`, so
`Ind_subsingleton` becomes *false*. `Eq`, `Iff` and every proof-irrelevant family
with large elimination go through exactly there, and `EqSpec` is about one of
them. Rejected on that specific, checkable ground rather than on a feeling.

Worth noting *how* it was caught: by walking the enumerated consumer list, not by
attempting the build. The rule works when you enumerate.

### The price

41 declarations mention the product shape directly across `Inductive.lean`,
`IndStage.lean` and `IndCard.lean`; 121 declarations and ~1570 lines total.
**But the change is an added conjunct, not a reshape** — `∃ a ∈ Fld q, ∃ f ∈
D^Pos q a, …` becomes the same with `⟨a,f⟩ₖ ∈ Args W q` conjoined. Every
destructuring gains one component; every construction gains one obligation.
Estimate **400–900 lines touched, mechanical-dominated** — consistent with what
§2 always implied for a model-side generalisation, and far below the
3000–6000-line Church–Rosser alternative. The stop condition was not met, so I
proceeded.

The cardinality argument is the one place that could have been expensive and is
not: `Args W q` is a *subset* of the product, so `IndCard`'s bounds only get
smaller.

### Landed: the operator layer

`IndSignature₃` (extending `IndSignature₂` with `Args`, `Args_definable`,
`Args_mono`), `indStep₃` with its membership lemma and definability,
`indStep₃_isMonotoneOn`, `Ind₃`, `Ind₃_subset`, `indStep₃_Ind₃`,
`Ind₃_induction`, `ctor_mem_Ind₃`. Sorry-free,
`[propext, Classical.choice, Quot.sound]`.

`Ind₃_induction`'s proof is `Ind_induction`'s verbatim plus one destructured
component — which is the evidence, rather than the claim, that the estimate's
shape is right.

One thing the port makes visible: the induction step is stated at `P`, the
approximation `lfp_subset_of_prefixed` supplies — not at `Ind₃ S D`. The old
`Ind_induction` is the same in this respect; it is invisible there only because
its `Fld` does not move.

### The recursor and the ι-rule are ported

`IsIndCarrier₃`, `IsMinorPremise₃`, `indCtor₃`, `mem_indStep₃_iff_of_carrier`,
`recStep₃` (+ two membership lemmas, definability, monotonicity), `recGraph₃`
(+ subset, fixed point, membership), `recGraph₃_unique`, `recGraph₃_total`,
`isFunction_recGraph₃`, `indRec₃`, `indRec₃_kpair_mem`, `indRec₃_mem`,
`indRecTuple₃` (+ three lemmas), and **`indRec₃_indCtor₃` — the ι-rule**. All
sorry-free, `[propext, Classical.choice, Quot.sound]`.

**The estimate's shape held throughout.** Every one of these is the original
proof plus one destructured or supplied component. The only two corrections
needed were restoring steps I had dropped by hand while transcribing, not
anything the port demanded.

### The one declaration that needed more than an added component

Reported here rather than in a summary, as the drift signal.

`recGraph₃_total` runs `Ind₃_induction`, and the induction hands its step data
**at the approximation, not at the fixed point**. The old proof's target set is
a `sep` of `S.Idx ×ˢ D`, which gives `a ∈ S.Fld P q` where `mem_recGraph₃_iff`
wants `a ∈ S.Fld (Ind₃ S D) q` — and `P ⊄ Ind₃ S D`, so nothing carries it.

The fix is one word: `sep` over `Ind₃ S D` instead of over `S.Idx ×ˢ D`. Then
`P ⊆ Ind₃ S D` and `Fld_mono`/`Args_mono` move the step data across. Small — but
it is exactly the invariant flagged when `Ind₃_induction` landed: *an invariant
that is invisible because nothing moves breaks silently once something starts
moving.* It surfaced two declarations later, in the first proof that needed it.

Two other structures also had to take the approximation as a parameter for the
same reason: `IsIndCarrier₃` and `IsMinorPremise₃` quantify over `W`, because a
form fixed at `Ind₃ S D` would not apply inside the induction.

### The rank check: it composes, and `IndCard` does not need porting

**`rank_mono {x y : V} (h : x ⊆ y) : rank x ≤ rank y` exists** —
`SetModel/Rank.lean:467`. With `mem_vsetV_iff_mem_Vset` and
`mem_Vset_iff_rank_lt` it composes directly into
`Ind₃_mem_vsetV_of : X ∈ vsetV k → Ind₃ S D ⊆ X → Ind₃ S D ∈ vsetV k`, three
lines. **So `IndCard.lean`'s 506-line cardinality argument does not need
porting**: `Ind₃` inherits its bound from any containing set already known to be
in the stage. `Ind₃_subset_of` — `Ind₃_induction` with the `Args` component
dropped — is the containment tool. Both sorry-free.

### The last step hit a documented hazard, and the documented remedy closed it

The composition — instantiating `Ind₃_subset_of` at
`P := Ind (S.toIndSignature₂.at W₀) D` — **did not elaborate**. `whnf` timed
out, and raising the limit 200k → 1M did not help, so by this file's own
diagnostic it was looping rather than deep. The cause is the hazard
`SetModel/Cnst.lean` already documents for `mkLam_mem_mkForallType`:
`Ind S' D` unfolds to `lfp _ (indStep S' D) (indStep_definable S' D)`, and with
`S'` a *concrete* anonymous constructor that definability **proof term** is large
enough to hang unification.

The remedy applied unchanged: **`Ind₃_subset_Ind_of` states it schematically**,
with `S'` an abstract `IndSignature` plus the six field equations relating it to
`S`. With `S'` a variable the proof term is never unfolded, and it elaborates
without a heartbeat bump. `Ind₃_mem_vsetV` and `Ind₃_mem_U_stage` follow, the
equations discharged by `rfl` at the concrete signature.

Worth recording as a third instance of the same pattern: a note written about
one subsystem (`definability`'s divergence) diagnosed a failure in another
(`whnf`'s unification), and a remedy written for one lemma
(`mkLam_mem_mkForallType`) closed a different one two files away. Neither was
aimed where it landed. **Such notes are worth writing not because you can
predict where they will be needed, but precisely because you cannot** — and the
moment they stop reading as idle remarks is the moment it is too late to write
them.

## Re-measuring the translation: it is **not** transcription, and the reason is new

I measured `VIndCtor → CtorData` as blocker-free transcription once, before the
escape hatch changed its shape, and it was not. The port has changed the shape
again, so I re-measured before building — enumerating what consumes the
translation's output rather than checking the first consumer to hand.

**It comes back "not transcription" a second time, at a site the port does not
cover.**

### The finding: `Pos` has no `Args`-shaped escape

`Pos q a` is the disjoint union over the constructor's recursive fields of
`⟦r.binders⟧`. `Decl.lean` specifies `r.binders` as "*`ξ`, in declaration order,
over `params ++ fields<i`. Contains no block constant*" — block-free, but living
over a context that **includes earlier recursive fields**. So evaluating it
needs their values.

`Pos : V → V → V` takes only `(q, a)`. It cannot take `f`, because `Pos q a` is
what *types* `f`. So either `a` carries the recursive fillers, or `r.binders`
does not depend on them — and the second is `NoBlock.indep`, restated at
`r.binders` instead of at the `pos`-clause's `A`. Same statement, same
disjointness family, different site.

**The port fixed `Fld`'s dependence on `f` and could not fix `Pos`'s**, because
`Args` works by constraining the pair `⟨a, f⟩ₖ` *after* `f` has a type, and
`Pos` is upstream of that.

### Why `a` cannot simply carry the fillers

That is the obvious escape and the enumeration kills it, with a named family.

`IsSubsingletonSignature.fld_det` asks `resIdx q a = resIdx q a' → a = a'`.
`Ind_subsingleton`'s proof (`Inductive.lean:648`) uses it to pin `a` from the
index and *then* pins `f` by the rank induction hypothesis — which is exactly
how it handles families that do have recursive fields. Put the fillers inside
`a` and `fld_det` must determine them from the result index, which it cannot;
the rank IH can no longer be reached.

The family this breaks is **`Acc`** — a large-eliminating subsingleton with a
recursive field, whose eliminator is not optional. Note this is a *sharper*
refutation than the one that killed the redundant-copy design earlier: that one
was "some subsingleton might break", this one names the family and the line of
the proof that stops working.

### Options, priced

1. **`NoBlock.indep` at `r.binders`.** Same disjointness family, now known to be
   in `sort_inv`'s equivalence class, i.e. behind the 3000–6000-line stratified
   Church–Rosser build.
2. **Generalise `Pos` further.** Does not help: the dependence is on `f`'s
   *values*, not on the approximation, and anything that makes `Pos` a superset
   computable without them puts junk positions into `f`, reintroducing the
   junk-in-the-carrier problem one level down.
3. **Record it in the specification rather than derive it** — require
   `r.binders` to be independent of recursive-field variables as part of
   `VIndField.WF`. `Decl.lean` already uses exactly this device, twice, and says
   so: `VIndField.lvl` is "*recorded, not derived*" because `sort_inv` is open,
   and the `HasArgs` clause likewise. This is the same situation and the same
   remedy, and it is a `Decl.lean` change (not mine).

**Recommendation: 3.** It is precedented in the file that would carry it, it is
a clause about the syntax rather than a model-side generalisation, and unlike
options 1 and 2 it does not wait on the contested obligation. The cost is one
more recorded-not-derived clause and whatever it takes to show the kernel's
positivity check implies it.

### `.induct`: what it now has, and what it still lacks

**Has** — all sorry-free, `[propext, Classical.choice, Quot.sound]`:

* the signature (`IndSignature₃`), its operator, monotonicity, and the family
  (`Ind₃`) as a least fixed point;
* the induction principle, constructor membership, carrier and minor premise;
* the recursor in full: graph, single-valuedness, totality, functionality,
  `indRec₃`, and **the ι-rule** `indRec₃_indCtor₃`;
* stage membership `Ind₃_mem_vsetV` / `Ind₃_mem_U_stage`, inheriting
  `IndCard`'s bound rather than porting it;
* the definability toolkit and the assembly (`mkIndSignature`) from earlier
  rounds.

**Lacks** — one thing, and the re-measurement above says what it costs:

* **the translation `VIndCtor → CtorData`/`Args`.** The syntactic half. The port
  removed the obstruction at `Fld` (nothing now forces `a` and `f` apart) but
  not the one at `Pos`, which has no `Args`-shaped escape. Blocked on a
  `NoBlock.indep`-shaped clause for `r.binders`, for which the recommended
  route is a recorded-not-derived clause in `Decl.lean` rather than the
  disjointness family.

## `interpSig_stage` and `interpSig_wf`, at the assembly level

The two proofs `docs/model-interface.md` §2 asks for, in the half the port
closed and the blocked translation does not gate. All sorry-free,
`[propext, Classical.choice, Quot.sound]`.

* **`mkIndSignature₃`** — the ported assembly: per-constructor `CtorData₃` to an
  `IndSignature₃`, discharging **all six definability obligations and both
  monotonicity obligations**. The two the port added (`Fld_mono`, `Args_mono`)
  are pushed out to the caller, where they belong: a `CtorData₃` carries
  `flds_mono` and `args_mono` as fields.
* **`mkIndSignature₃_wf`** — `interpSig_wf`.
* **`mkIndSignature₃_stage`** — `interpSig_stage`.

New machinery, all general: `tagCaseSnd` with its definability, **monotonicity**
and read-back, because the port moved `Fld` from `V → V` to `V → V → V` and the
tag became the *second* argument — `tagCase₁` dispatches on the first and cannot
do it. Plus `ite_eq_snd_definable₂`, `tagCase₂_at`, and `mem_ofNat_iff` (the
tags really are the numerals below `n`, which every read-back needs).

Everything in this round elaborated first try. No drift.

### Method: "enumerate the consumers" means *read their proofs*

Stated in this form because the short version reads as a list-making exercise
and is then done uselessly.

> **A consumer's statement tells you what it concludes. Only its proof tells you
> what it uses.**

Both re-measurements of the translation turned on exactly this. The design that
puts recursive fillers into `a` satisfies every consumer *statement* in the
enumeration — `IsSubsingletonSignature`'s included, since `fld_det` is just an
implication. It is `Ind_subsingleton`'s **proof** (`Inductive.lean:648`) that
shows `fld_det` is used to pin `a` from the index *before* the rank induction
hypothesis pins `f`, so burying the fillers in `a` strands the argument at a
step no statement mentions.

The failure mode this guards against, named from three attempts on one piece:

> **Correct about the site I was looking at, silent about the one I was not.**

Two of three measurements on the `VIndCtor` translation failed that way. The
remedy is not "look harder" — it is mechanical: enumerate the consumers, then
open each one's proof rather than its signature.

### Method, not an anecdote: why prophylactic notes are load-bearing

Recorded here as method because it has now fired three times, twice outside the
subsystem it was written about.

> Write the note at the moment the property is *observed*, not when it is
> needed — because you cannot predict where it will be needed, and the moment
> you *can* say where, you have already paid for the knowledge.

If such notes only ever fired inside the subsystem they described, writing them
early would just be tidiness. What makes the practice load-bearing is that they
fire elsewhere: the moving-invariant note fired two declarations later in its
own file; the diverging-search note, written about `definability`, diagnosed a
**`whnf` unification** failure; and a remedy written for `mkLam_mem_mkForallType`
closed `Ind₃_subset_Ind_of` **two files away**. None was aimed where it landed.
The corollary for practice: the notes that feel least worth writing — the idle
remarks about a property that currently costs nothing — are the ones to write.

So `.induct` is **open**, and the model remains conditional on `LevelAssign` —
unwitnessed, four consumers. A closed port does not change either label.

### Port total against estimate

Estimated **400–900 lines, mechanical-dominated**. Actual: `IndInterp.lean` grew
from 874 to ~1400 lines, of which roughly **520 lines are the port** (signature,
operator, carrier, minor premise, the full recursor graph, totality,
single-valuedness, the recursor, the ι-rule, and the stage step) — **inside the
estimate, in its lower half**, and the 506-line cardinality file was avoided
entirely rather than ported.

Drift signals over the whole port: **one** declaration needed more than an added
component (`recGraph₃_total`, cause known, one-word fix), and two corrections
were my own dropped transcription steps rather than port cost.

The cheap route, which avoids porting `IndCard.lean` at all: prove
`Ind₃ S D ⊆ Ind (S.at (S.Idx ×ˢ D)) D` by `Ind₃_induction` — the step's
`a ∈ S.Fld (Ind (S.at W₀) D) q` moves to `S.Fld W₀ q` by `Fld_mono` and
`Ind_subset`, which is exactly what `ctor_mem_Ind` at `S.at W₀` wants — and then
conclude from `Ind_mem_vsetV` that `Ind₃` is a subset of a member of `vsetV k`.

**The one fact that route needs and I have not confirmed exists**: subsets of
members of `vsetV k` are members, i.e. rank monotonicity under `⊆`.
`SetModel/Rank.lean` has `Vset_mono`, `subset_Vset_rank`,
`subset_Vset_of_mem_Vset` and `mem_Vset_iff_rank_lt`; whether they compose into
it, or whether `IndCard`'s bounded-rank argument (`IndStage.lean:247`) has to be
rerun, is the next thing to check — before writing, not after.

### Caveat left standing: the all-levels quantification

`quotDefEq_ok` takes `hEq`, `hcnst`, `hcnstMk` and `hcnstL` quantified over
**all** `VLevel`s, including non-`WF` ones. That is the natural shape for a
uniformly-defined `M.cnst` — which is what `oracleExtend` produces — but if the
assembly wants them only at `WF` levels the hypotheses need weakening. The change
is mechanical; it is flagged rather than done, because doing it before assembly
knows what it wants is work that may be undone.

## The `OracleOK` connection, closed — and the staging mismatch it exposed

`coherentOn_addInduct` (`SetModel/IndInterp.lean`, section `InductStep`) is the
`.induct` line of the `CoherentOn` induction: from a coherent `env`, the block's
constants and the block's ι-rules, it produces `CoherentOn` for the environment
`addInduct'` builds. Sorry-free, `[propext, Classical.choice, Quot.sound]`.
Supporting: `addConstList_allConsts`, and in `Cnst.lean`
`addConstList_append` / `oracleExtend_append` (both `[propext, Quot.sound]`).

Everything it needs was already in place — `Above.and`, `Above.imp₂`,
`Above.forall_mem`, `above_mem_congr`, `oracleOK_above` — and the proof is two
lines. The finding is not the proof; it is what had to be seen before writing it.

### The finding: the two sides stage the block differently

`VEnv.addInduct'` adds the block in **three** `addConstList` steps —
`addIndTypes`, then `addIndCtors`, then `addIndRecs` — and only then folds the
ι-rules. `cnstOf`'s `.induct` line performs **one** `oracleExtend o D.allNames`.

Chained in the obvious way, that mismatch is expensive. Each intermediate step
would carry a `CoherentOn` at a *partial* assignment: the type formers' obligation
stated in a world where the constructors are still unassigned, the constructors'
where the recursors are. Moving each obligation from its partial assignment to
the final one is exactly `interp_cnst_congr`'s job, and it would have to be
invoked three times, with three freshness side-conditions about which names are
not yet in the environment.

None of that is necessary, because

```
D.allConsts = D.typeConsts ++ D.ctorConsts ++ D.recConsts
```

is definitional, and `addConstList` and `oracleExtend` both **distribute over
`++`**. So the three steps collapse into one `addConstList D.allConsts` before
the coherence argument starts, and `coherentOn_addConstList` — which already
handles a whole list at a single final assignment — applies directly. The two
distribution lemmas are eight lines together.

> **Method: when two sides of an interface stage the same operation
> differently, check whether either side's staging is a fold over an append
> before paying to bridge them.** A bridge between stages costs congruence
> lemmas and freshness conditions at every intermediate point; collapsing the
> staging costs one associativity lemma per operation, and the collapse is
> available whenever both operations are list folds — which, in this tree, they
> usually are.

The obligations `coherentOn_addInduct` pushes out to its caller are the
per-constant `OracleOK` (already `Above`-wrapped in both fields, so no
unconditional statement appears anywhere) and the per-ι-rule pair. Those are the
translation's business, not the connection's.

### What `.induct` has now, and what it lacks

Has: the family, its constructors, its recursor, the ι-rule and the stage bound
in the ported ₃ form; `mkIndSignature₃` with all six definability and both
monotonicity obligations discharged; `interpSig_wf` and `interpSig_stage`; and
now the coherence step that consumes them.

Lacks: the translation `VIndCtor → CtorData₃`/`Args`, blocked on the `Decl.lean`
clause that makes `Pos q a` computable from `a`. When that clause lands it gets
checked against `Acc` **before** anything is built on it — a clause `Acc` fails
leaves the translation blocked at the same site, not unblocked.

So `.induct` remains **open**, and the model remains conditional on
`LevelAssign` — unwitnessed, four consumers. Closing the connection changes
neither label.

## The `binders_indep` clause, checked at the consumption point

The `Decl.lean` clause the translation was blocked on landed (`3c79601`) as
`VIndRecArg.BindersIndep` + `VIndField.WF.binders_indep`. It was checked in
isolation there. This is the **second, independent check** — done here rather
than taken on report, because if the clause is stated in a way `Acc` fails, the
translation is blocked at the same site rather than unblocked.

### `Acc`, re-checked from this side

Six machine checks, all green (`lake env lean` on a scratch file; the checks are
closed computations, `BindersIndep` mentions no `VEnv`):

1. `Acc.intro`'s earlier field is `{type := .bvar 1, recArg := none}` — **not**
   recursive.
2. `accIntroRec.BindersIndep (accIntro.fields.take 1) 1` holds.
3. Its hypothesis set is **empty** — there is no `(i', F')` with
   `pre[i']? = some F'` and `F'.recArg.isSome`. So it holds vacuously.
4. **And `ξ` genuinely does mention the earlier field**:
   `¬ (accIntroRec.binders[1]!).Skips' 1 1`. This is the check the isolation
   pass does not force, and it is the one that matters — it shows the vacuity
   is for the *stated* reason (the earlier field is non-recursive), not because
   `Acc`'s `ξ` happens to be independent of everything. A clause quantified over
   all earlier fields would fail here, and `Acc` would be gone.

### The finding: two index conventions, and truncated subtraction between them

Checking the clause "at the consumption point" turned up something the isolation
check could not.

`BindersIndep` states `B.Skips 1 (k + t)`: **relative** de Bruijn indices,
innermost 0, incremented under binders. `interp_avoids` (this file) states
`AvoidsAt S n e` with `.bvar i ↦ ¬ S (n - 1 - i)`: **absolute** positions
counted from the outside, because that is what an environment `ρ` is read at.

The conversion `j = n - 1 - i` is a bijection only on well-scoped terms. With
`Nat`'s truncated subtraction, any out-of-range `bvar` collapses to absolute
position `0` and would falsely appear to read the **outermost** slot — the
parameters. So the bridge needs a `ClosedN` hypothesis, which is free at the use
site (the binders are well-typed in `r.binders.reverse ++ Γ`) but is not
optional.

> **Method: a clause checked in isolation is checked against its own
> convention.** The failure this catches is not "the clause is wrong" but "the
> clause and the consumer disagree about what an index means" — invisible from
> either side alone, and silently *false* rather than a type error, because both
> sides are `ℕ`.

Three lemmas now hold the bridge in `SetModel/IndInterp.lean`, all sorry-free,
`[propext, Classical.choice, Quot.sound]`, all first try:

* **`avoidsAt_of_forall`** — `BindersIndep` gives one `Skips` per earlier
  recursive field, i.e. a family of *singleton* avoid-sets, while
  `interp_avoids` wants one predicate covering all of them. This unions them.
  The clause's per-field shape therefore costs nothing here.
* **`avoidsAt_of_skips`** — the index conversion, with the `ClosedN` side
  condition and the extra-binder depth `d` that binder `k` of `ξ` sits at.
* **`interp_indep_of_skips`** — the depth-0 corollary.

The clause's own bookkeeping was checked against this file's, and agrees: with
`i' + 1 + t = i`, field `i'` sits at de Bruijn index `t` in `Γ`, hence at
absolute position `|Γ| - 1 - t = D.np + i'` — the recursive field's slot.

### What remains unchecked, and it is not mine

The tree still has **no `VInductDecl'.WF` witness with a recursive field**, so
"the clause admits `Acc`" is established about `BindersIndep` and not about the
well-formedness predicate the translation consumes. Routed to the `Decl.lean`
stream. Until that witness exists, my checks above and theirs all test the same
isolated object — more checks of one kind, not two kinds.

Also noted for later: under the nested companion design a companion's
constructors are derived and reclassified, and for `Tree`/`List` **both** fields
of the companion constructor become recursive. That is the first configuration
where `BindersIndep` is non-vacuous, and it is the configuration the model's
`Pos q a` argument is actually stated over. Not current work; it is where the
clause will first earn its keep.

## The `WF`-witness gap is closed, at three configurations

The item above — "the tree still has **no `VInductDecl'.WF` witness with a
recursive field**, so *the clause admits `Acc`* is established about
`BindersIndep` and not about the well-formedness predicate the translation
consumes" — is closed. Three complete `VInductDecl'.WF` witnesses now exist in
`Theory/Inductive/DeclExamples.lean`, all sorry-free and none of them touching
`VIndRecArg.exists_indep`'s open obligation:

| witness | axioms | what it adds |
|---|---|---|
| `accDecl_WF` | `propext`, `Quot.sound` — not even choice | parameters *and* indices, a two-binder `ξ`, a nontrivial `π`, `LECond`'s second disjunct |
| `mutDecl_WF` | the three standard | two types in the block, cross-recursion (`recArg.idx` into the *other* type), two recursive fields in one constructor |
| `wDecl_WF` | the three standard | a later recursive field whose `ξ` is **non-empty**, so the `Skips` obligation is evaluated |

Why the reason this was worth doing is not "more coverage". A clause has as many
vacuity levels as it has nested conditions, and a witness's honest measure is the
**deepest level it reaches**, not whether it passes:

| witness | earlier field recursive? | `ξ` non-empty? | `Skips` evaluated? |
|---|---|---|---|
| `fooDecl_WF` | — (no recursive field at all) | — | no |
| `accDecl_WF` | no | yes | no |
| `mutDecl_WF` | **yes** | no | no |
| `wDecl_WF` | **yes** | **yes** | **yes** |

Only the last row tests the clause's actual content. `wDecl` is
`inductive W' (β : Prop) : Prop | mk : W' β → (β → W' β) → W' β`; its second
recursive field has `ξ = [β]`, and in that field's context `[W' β, β]` the
parameter is `.bvar 1` while the earlier recursive field is `.bvar 0`, so
`(.bvar 1).Skips 1 0` is a computation that could have gone either way. `wRecBad`
— the same declaration with `ξ = [.bvar 0]` — is refuted next to it, which is
what shows the last column is not automatic. Both `wType.type` and
`wMk.type wDecl 0` are `rfl`-checked against Lean's own `@W'` and `@W'.mk`, so
the encoding is not a convenient fiction.

**This is deliberately ahead of the port.** The note above records that under the
companion design both fields of `Tree`/`List`'s companion constructor become
recursive, and calls that "the first configuration where `BindersIndep` is
non-vacuous". `wDecl` is that configuration, built against the current spec while
the clause is still five lines from being changed. If the clause were wrong at
that shape, it is much cheaper to learn it here than from the nested port.

What is *still* only checked in isolation: nothing about `BindersIndep` itself —
but `VIndRecArg.exists_indep` (the "the kernel's positivity check implies this
clause" obligation) remains open, blocked on `IsDefEqU.forallE_inv` in
`Typing/Injectivity.lean`. That debt is shared with three other cones, not new.

## Hazard: `type_tac` is only correct while the target sort is a metavariable

Recorded here because it costs a debugging round and, like the `isDefEq`
coercion-index hazard above, it **reports an unrelated failure**. This is the
failure mode that has been expensive all session: a wrong answer that looks like
a different problem.

`type_tac` (`Theory/Typing/Meta.lean`) has

```lean
| refine HasType.forallE (u := ?_) (v := ?_) ?_ ?_ <;> [skip; skip; type_tac; type_tac]
```

a **four**-slot `<;> [...]`. That arity is right only when the goal's sort is a
metavariable, which is the case at every other use in the tree, because they all
sit under `IsType`'s `∃ u`. When the target sort is **concrete** — as in
`VIndField.WF.hasType`, which demands `.sort F.lvl` — unification solves `?u` and
`?v` from `.sort (.imax ?u ?v)` at `refine` time, only two goals remain, the
four-slot combinator fails, and `first` falls through to its last alternative.

The error you actually see is therefore

```
Type mismatch
  VEnv.HasType.lam ?m ?m
has type
  VEnv.HasType _ _ _ (lam _ _) (forallE _ _)
but is expected to have type
  … (sort (imax …))
```

— a complaint about `lam` on a goal containing no `lam`. Nothing in it points at
`forallE`, at arity, or at the concrete sort.

**Remedy**: apply the constructor directly, `.forallE (by type_tac) (by type_tac)`,
and let `type_tac` handle only the sub-goals (whose sorts are again concrete but
whose head symbols take the `bvar`/`app`/`const` branches, which have the right
arity either way). Nesting it for a two-binder telescope is
`.forallE (by type_tac) (.forallE (by type_tac) (by type_tac))`.

Two further gotchas met at the same site, both of which also present as unrelated
errors:

* **A structure-instance goal carries an unreduced projection.** Inside
  `refine { hasType := ?_, … }` the goal is stated at `{…}.type`, and
  `type_tac`'s `refine` will not see a `forallE` through it. Hoist the judgement
  into a `have` with the type spelled out.
* **`.sort` resolves against the goal's head, not against `HasType`.** Under
  `IsDefEqType` — i.e. `∃ u, IsDefEq …` — the anonymous-constructor hole has head
  `VEnv.IsDefEq`, so `.sort` elaborates as `VEnv.IsDefEq.sort`, which does not
  exist. Write `VEnv.HasType.sort` in full. Under a bare `IsType` the same
  `⟨_, .sort _⟩` is fine, which is why this only bites on `VIndType.WF.canon`.

`Meta.lean` is not this stream's file and was not touched; fixing the combinator
there (`<;> [skip; skip; type_tac; type_tac]` → a form tolerant of solved level
goals) would retire all of the first item.

## Nested inductives: the `VEnv` expressiveness gap, with all exits costed

The gap: `VEnv` is `{constants : Name → Option VConstant, defeqs : VDefEq → Prop}` and
`VConstant` is `(uvars, type)`, so nothing in a `VEnv` records that a constant *is* an
inductive or what its constructors are. The companion clause of
`docs/design-inductive.md` §9.3 needs the **completeness** half — *these are exactly `J`'s
constructors and there are no others* — and an under-complete constructor list is precisely
an unsound recursor (eliminate `List (Tree α)` with only the `nil` minor).

Prices below. Two of the three expectations that ranked these turned out **wrong on
measurement**, both in the direction of making an exit cheaper, so the checks are recorded
with the prices.

### Correction first: exit 1 does **not** need sign-off

An earlier report of mine said extending `VEnv` "changes the type `kernel_sound` is stated
over", implying a frozen-file change. **That is wrong.** `VEnv` occurs **0 times** in
`Verify/Soundness.lean`, `Verify/Axioms.lean` and `Verify/Guard.lean`; `kernel_sound` is
stated over `Kernel.Environment`, `Declaration` and `Entailment.Inconsistent`. `VEnv` is
internal proof machinery, which `CLAUDE.md` explicitly designates as free to design. This was
the single largest input to the old ranking and it was mis-measured.

### Exit 1 — extend `VEnv` with inductive bookkeeping

| | |
|---|---|
| frozen-file change | **none**; no sign-off |
| construction surface | **2 sites** — `addConst` and `addDefEq`, both in `Theory/VEnv.lean` (plus `VEnv.empty`) |
| `VEnv.ext` risk | **nil** — `@[ext]` is declared but has **0 uses** |
| mechanical repair | `VEnv.LE` must gain a clause or weakening silently loses the new data; ~47 anonymous `LE` constructions stop typechecking |
| genuinely new proof | one truthfulness invariant: only `addInduct'` writes the field, and it writes exactly the block being added, threaded through `Ordered`/`WF'` |
| size | **M** |

**Does anything already-proved become restatable-but-false, or merely need re-proving?**
Merely re-proving — and mostly not even that. Every existing statement about a `VEnv` is
about `constants` or `defeqs` only, and both are preserved by every operation, so no existing
lemma changes truth value. Adding a field makes existing lemmas *too weak for new consumers*
and makes ~47 constructions *fail to elaborate*; neither is falsity. The one pattern that
could have produced a false-after-restatement — a lemma proved by `VEnv.ext` or by exhaustive
case analysis on the record — **does not occur**: `ext` has no uses in the tree.

Unverified and worth checking before committing: whether the SetModel must *interpret* the
new field. If it is bookkeeping consumed only by `VIndType.WF`, the interpretation is
untouched (the model already gets its inductive data from `VEnv.WF'`'s `.induct` step).

### Exit 2 — thread `VEnv.WF'`'s history into `VIndType.WF`

**Falsified at row zero: hard import cycle.** `Theory/Typing/Env.lean` (which defines
`VEnv.WF'` and `VDecl.WF`) imports `Theory/VDecl.lean`, which imports
`Theory/Inductive/Decl.lean` (which defines `VIndType.WF`). `Decl.lean` is strictly
*upstream*; it cannot mention `VEnv.WF'`.

Doing it anyway means merging `Typing/Env.lean` (86 lines), `VDecl.lean` (41) and
`Inductive/Decl.lean` (822) — **949 lines** — into one file, *and* converting the entire `WF`
cluster (`VIndField.WF`, `VIndCtor.WF`, `VIndType.WF`, `VInductDecl'.WF`, `VDecl.WF`,
`VEnv.WF'`) from structures into one mutual inductive block, losing structure-field syntax at
every use site.

Blast radius on inductions: `VEnv.WF'.ruleShape`, `VEnv.WF.ordered`, `TrEnv'.wf` and the
SetModel's `coherentOn_*` chain all run `induction H with | empty | decl`. They stay
well-founded — the recursion is on `ds`, and `VIndType.WF` would refer to a *strictly
earlier* environment — but each becomes a mutual induction with a new motive, i.e. must be
**restructured**, not re-proved.

Size **XL**, and it is **dominated**: exit 1 achieves the same effect with none of this.

### Exit 3 — `VInductDecl'` carries the earlier declaration as data

**Expected falsifier, run, and it passed.** I expected mutual `structure`s to be rejected.
They are not: a mutual block of `structure`s with `deriving Inhabited` elaborates, `default`
is derived for every member, and `l.getD j default` — which the tree uses pervasively — still
works. Checked directly rather than assumed; the expectation was wrong.

Cost is the construction surface, not the read surface: `VIndType` occurs 141×, `.ctors`
128×, `.indices` 332×, but those are reads and an added `Option` field leaves them alone.

**Cheaper repair that avoids the mutual block entirely.** The companion does not need a whole
`VInductDecl'`. Let it carry `J`'s **constructor list** — `List VIndCtor`, already a legal
`VIndType` field type, introducing no new recursion — plus the parameter instantiation, and
*compute* the certificate block with a `def : VIndType → VInductDecl'`. A function is not a
data cycle. Size **L**.

### Exit 4 — the completeness certificate is already in the tree

This is the finding of the round, and it may make the gap disappear.

`VEnv.defeqs` is a **predicate**, so it is the one *enumerable* field of a `VEnv` — and
`Theory/Typing/PatternRules.lean` already exploits it. `VEnv.RuleShape`'s `iota` constructor
carries, **as data**, the declaring block `D` together with `D.WF env₀`, the full staging
chain `env₀ → env₁ → env₂ → env₃ ≤ env`, and

```lean
env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩
env.constants C.name = some ⟨D.uvars, C.type D j⟩
```

and `VEnv.WF.ruleShape : env.WF → env.defeqs df → env.RuleShape df` is **fully proved**
(`WF'.ruleShape`, an induction over the declaration list with def/unsafeDef/quot/induct
cases — not a `sorry`).

So from *any* ι-rule of `J.rec` you recover the block that declared `J`, and its constructor
list is complete **by construction** — no enumeration, no `VEnv` change, no mutual recursion,
no recursive `VInductDecl'`. Two consequences:

* The completeness half may not need to be a **clause** at all. It looks derivable
  *downstream*, where `WF.ruleShape` is in scope — and the model already consumes `VEnv.WF'`,
  so it can use the same handle.
* It supplies the precedent for exit 3's certificate: `RuleShape.iota` ties a block to an
  environment by exactly "the recursor constant is present at the block's `recType`". And the
  primitives to invert `recType` already exist — `VExpr.mkPi_inj`, `mkPi_inj_of_arity`,
  `mkApp_inj_of_arity` in `Theory/Inductive/Telescope.lean`, where the arity versions
  *derive* the length hypothesis rather than assuming it. (Note 1 of
  `Theory/Inductive/Lemmas.lean` — "check `Telescope.lean` before estimating" — paying for
  the fourth time.)

**What is verified and what is not.** Verified: `RuleShape.iota`'s payload, that
`WF.ruleShape` exists and is proved, the import direction, and that the injectivity
primitives exist. **Not** verified: that the `D₀` recovered from a rule is *unique* for a
given `J` — the existential could in principle attribute two ι-rules of `J.rec` to different
blocks, and pinning it needs the uniqueness family (`DeltaUnique`/injectivity). Also, a `J`
with **zero** constructors has no ι-rules and yields nothing; that is benign (the
ctor-constant clause then forces the claimed list empty too) but it means the route is not
uniform. Import constraint: `RuleShape` is downstream of `Decl.lean`, so exit 4 cannot be a
clause *in* `VIndType.WF` — it must be a downstream theorem, which is the shape it wants
anyway. Size **M** if uniqueness resolves.

### Exit 4, settled: uniqueness is free; the zero-constructor case is not

**Which uniqueness is needed — the weak one, and it costs nothing.** The companion does not
need the recovered block to be unique; it needs any two recovered blocks to agree about `J`'s
constructor list. That is strictly weaker, and it does **not** need the
injectivity/`DeltaUnique` family the companion story was at risk of depending on. The chain:

1. A rule headed by `J.rec` comes from a block containing a type named `J` — `iotaLhs`'s head
   is `.const (mkRecName (D.types.getD j default).name) …`, and `mkRecName` is injective.
2. **At most one block of a history contains a type named `J`** — now proved as
   `VEnv.addInduct'_types_disjoint` (`Theory/Inductive/Nested.lean`), sorry-free, standard
   axioms. Its proof is two steps: the earlier block's type constant is present and monotone,
   and the later block's `addInduct'` demands that name be *absent*. It rests entirely on
   `addInduct'_type_fresh`, i.e. on `addConst` failing on a duplicate.
3. Hence the attribution is unique, and *a fortiori* the constructor lists agree.

Its hypothesis set is inhabited — `example : ((VEnv.empty.addInduct' eqDecl).bind (·.addInduct'
iffDecl)).isSome := rfl` in `DeclExamples.lean`, since a lemma about two sequential blocks is
worthless if no two blocks are sequential.

What is **not** done: step 2 is proved for two blocks, not wrapped in the induction over
`VEnv.WF'` (straightforward, using `addInduct'_le` and monotonicity of the `VDecl.WF` steps),
and step 1's "the lhs head determines `T.name`" is not formalised (`mkApp_inj_of_arity` plus
`mkRecName` injectivity — cheap, and both primitives exist). The *risk* is retired; the
plumbing is not written.

**The zero-constructor case is real, reachable, and breaks uniformity.** Filing it as benign
was wrong. `Empty` and `False` indeed cannot be nested through — they take no parameters, so
`Empty T` is ill-typed — but a **parameterised** constructor-free inductive can be, and both
kernels accept it:

```
inductive Void1 (α : Type) : Type          -- no constructors, one parameter
inductive T1 : Type | mk : Void1 T1 → T1   -- accepted; numNested = 1
```

`Lean4Lean.ElimNestedInductive` reduces `T1` to `[T1, _nested.Void1_1]` with
`_nested.Void1_1.ctors = []` (run directly, not inferred). So the companion for `Void1` is a
**zero-constructor companion**, and `VInductDecl'.iotaRules_eq_nil`
(`Theory/Inductive/Nested.lean`, proved) says such a block contributes no ι-rules — exit 4's
entire handle yields nothing there.

This is not cosmetic. A companion with no minor premises is an eliminator asserting that `J A`
is empty; admitting it without a certificate is exactly the "holds except at the degenerate
case" shape. The natural certificate is that `J.rec`'s stored type carries no minor premises,
which needs the same `recType` telescope inversion (`mkPi_inj_of_arity`, present) that exit 3's
certificate needs. **So at the empty case exits 3 and 4 converge on the same lemma**, and
whichever is chosen that lemma has to be written.

Net: exit 4 survives, remains the cheapest, and is no longer free — **M plus the `recType`
inversion**, which is shared with exit 3 rather than additional to it.

### The option set, ordered

1. **Settle exit 4's uniqueness question first.** It is small and decisive, and if it works
   exits 1 and 3 are unnecessary.
2. **Exit 1** if it does not — much cheaper than previously reported, and needs no sign-off.
3. **Exit 3** (in its `List VIndCtor` repair, not the mutual-structure form) as fallback.
4. **Exit 2 never** — dominated by exit 1.

### Carried item, whichever exit is taken

The companion clause must also **preserve `BindersIndep` under substitution**. A companion's
constructors are `J`'s with the instantiation substituted, and for `Tree`/`List` *both*
fields of the companion constructor become recursive — the configuration where
`VIndField.WF.binders_indep` is non-vacuous. `wDecl_WF`
(`Theory/Inductive/DeclExamples.lean`) is the standing witness that the clause is satisfiable
at exactly that shape, built ahead of the port for this reason.

## The remaining open items, ranked






1. **`IsDefEqU.sort_inv`** — gives `LevelAssign`, hence the interpretation.
   Single `sorry`, highest value in the project.
2. **Connecting the `.induct` case.** Reduced to **one** remaining piece. The
   model half is complete in its ported form (`SetModel/IndInterp.lean`):
   `IndSignature₃`, `Ind₃` with its constructors, recursor, ι-rule and stage
   bound; `mkIndSignature₃` discharging all six definability and both
   monotonicity obligations; `interpSig_wf`, `interpSig_stage`; and
   `coherentOn_addInduct`, the `CoherentOn` step for `addInduct'`. What is left
   is the **translation** `VIndCtor → CtorData₃`/`Args`, blocked on a `Decl.lean`
   clause making `Pos q a` computable from `a` — see "Re-measuring the
   translation". Watch the elimination universe: it is not uniform across
   inductives — a small eliminator such as `Nonempty` fails large elimination and
   its recursor takes one universe parameter where `Eq`'s takes two.
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
   | `.quot` | `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and `quotDefEq` | **done** — all four `const_type` obligations (`quotFn_mem`, `quotMkFn_mem`, `quotIndFn_mem`, `quotLiftFn_mem`) and both `quotDefEq` obligations (`quotDefEq_ok`). Open against `EqSpec`, which the `.induct` step owes |
   | `.induct` | `oracleExtend o D.allNames` | step **proved** (`coherentOn_addInduct`); its `OracleOK`/ι-rule obligations wait on the translation |

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

---

## Correction, 2026-08-31: two ledger entries above are **vacuous as stated**

`Theory/SetModel/CnstRecursion.lean`.

The table in item 4 lists the `.induct` line as "step **proved**
(`coherentOn_addInduct`)", and the section "The `OracleOK` connection, closed"
says `coherentOn_addConstList` "already handles a whole list at a single final
assignment — applies directly". **Both entries are wrong, and the error is not a
gap in the proofs: the proofs are fine and their hypotheses are jointly
unsatisfiable.**

`coherentOn_addConstList` (`Cnst.lean`) takes, alongside
`env.addConstList cs = some env'`, an occurrence hypothesis

    hocc : ∀ p ∈ cs, p.2.type.ConstsIn env.contains

stated at the **pre-block** environment `env`. But `addConstList` fails on a
duplicate, so `addConstList cs = some env'` forces every name of `cs` to be
*absent* from `env` (`addConstList_fresh`, already in the file). Hence any block
one of whose declared types mentions another of the block's own names satisfies
the `addConstList` hypothesis and refutes `hocc`. Machine-checked, sorry-free:

* `addConstList_hocc_unsat` — the general statement, for any `p q ∈ cs` with
  `q.1` occurring in `p.2.type`;
* `hocc_unsat_eqIndDecl` / `hocc_unsat_eqIndDecl'` — instantiated at
  `eqIndDecl`, the **head of `leanPrelude`**, where `Eq.refl`'s type mentions
  `Eq`. So the lemma is vacuous at the very first inductive the model must
  interpret, and by extension at every inductive with a constructor, since a
  constructor's type names its own family. `coherentOn_addInduct`, which routes
  through `coherentOn_addConstList` on `D.allConsts`, inherits the vacuity.

The staging collapse the section celebrates — `addIndTypes ⨟ addIndCtors ⨟
addIndRecs` into one `addConstList D.allConsts` — is still correct and still
worth having (`addInduct'_iff`). What was wrong was inferring from it that the
*occurrence* condition also collapses. It does not: `VInductDecl'.WF` itself
stages its `ctors` field at `addIndTypes` rather than at `env`, which was the
available signal that the block's own names have to be in scope partway through.

### The repair

    def StagedOcc : VEnv → List (Name × VConstant) → Prop
      | _, [] => True
      | env, p :: cs => p.2.type.ConstsIn env.contains ∧
          ∀ env₁, env.addConst p.1 p.2 = some env₁ → StagedOcc env₁ cs

`coherentOn_addConstList'` is `coherentOn_addConstList` with `hocc : StagedOcc env cs`
in place of the unstaged form. **The proof body is unchanged**: the head step
consumes `hocc.1`, and the recursive call consumes `hocc.2` at the intermediate
environment — exactly the information the unstaged form threw away. Sorry-free.

`stagedOcc_separates` is the non-vacuity control: a two-constant block on which
`StagedOcc` holds and the old hypothesis fails. So this is a real repair and the
new lemma is not vacuous in turn.

### What the repair buys, and what it does not

`coherentOn_cnstOf` (same file) is the outer recursion of item 4, over
`VEnv.WF' ds env`, sorry-free:

| `VDecl` | disposition in `coherentOn_cnstOf` |
|---|---|
| `.def`, `.opaque` | **discharged** from `coherentOn_defEq` / `coherentOn_defConst` |
| `.example` | **discharged** (no environment change) |
| `.unsafeDef` | **refuted** from `VDecl.noUnsafe`, which `VEnv.LeanWF` supplies (`noUnsafe_of_leanWF`); item 3's `mutualDef` therefore does not block H2 |
| `.quot` | occurrence side **discharged** (`stagedOcc_quotConsts`, from `VEnv.QuotReady` alone — precisely what `VDecl.WF.quot` carries); value side is `QuotOracleOK`, i.e. the four `const_type` obligations plus `quotDefEq`, all already proved in `QuotInterp.lean` |
| `.induct` | reduced to `InductOracleOK` — **the residual** |

`InductOracleOK L κ ls o c D` has three fields: `staged` (`StagedOcc env D.allConsts`
whenever `addInduct' D` succeeds — this is what the repaired lemma now *asks* for and
what `VInductDecl'.WF` should supply), `consts` (per-constant `OracleOK`), `rules`
(per-ι-rule `DefEqOK`). Fields 2 and 3 are the ones the ledger already says wait on
the `VIndCtor → CtorData₃`/`Args` translation; field 1 is new, and is the part the
vacuity was hiding.

Boundary control on the residual, both sorry-free, both in the same file:

* `not_oracleOK_falseProp` / `not_inductOracleOK_falseProp` — `InductOracleOK` is
  **refutable** at a block declaring a constant of type `∀ p : Prop, p`, since
  `OracleOK`'s `type` field asks for an element of `⟦falseProp⟧ = ∅`. So no uniform
  proof of the residual exists, and the reduction is not circular: `VDecl.WF` asks
  that a declared type *be* a type, never that it be inhabited.
* `inductOracleOK_empty` — `InductOracleOK` **holds** for a block with no type
  formers, so the residual is not plainly false either.

### H2 after this: a reduction, not a closure

`upper_bound_of (hA : InaccModelInput) (hB : ModelFitsInput) :`
`Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent`, sorry-free. Its two inputs
are open, and they are **not** the same thing as the residual:

* `InaccModelInput` — model existence. Foundation supplies the two halves
  separately (`small_satisfiable_of_consistent` + `QuotNormalize`/`standardStructure`,
  and `exists_inaccessibleChain`), and **neither is applied here**. The second is a
  real gap, not bookkeeping: `exists_inaccessibleChain` gives one `κ` *per* `n`,
  while `consistent_of` needs a single `κ` with `∀ m, IsInaccessibleChain m κ`,
  because the threshold `sound_nil` produces is not known in advance.
* `ModelFitsInput` — per-environment model data: a `PropSplit env 0` with `Stable`
  and a `CtxInvariant`, plus `OracleFits`. The `PropSplit` part carries
  `docs/model-interface.md`'s standing label (nothing in the tree exhibits one);
  the `OracleFits` part is the `.axiom`/`.quot`/`.induct` oracle, of which only the
  `.induct` clause is the residual.

**No joint witness for the whole hypothesis set has been exhibited.** The claim
here is exactly: every `VDecl` case of the recursion is discharged or refuted
outright, and what remains is the three named inputs above.
