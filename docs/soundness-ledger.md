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

## The non-injectivity obligations — the handoff specification

This is the list of everything a `LevelAssign` / `ModelData` construction owes,
i.e. what has to be supplied before soundness is unconditional. None of it is an
injectivity fact.

| Obligation | Where declared | What it says |
|---|---|---|
| `LevelAssign.lvl_sound`, `srt_sound` | `Interp.lean` | the assignment agrees with the typing rules — this *is* `sort_inv`, in functional form |
| `LevelAssign.Stable` (4 fields) | `InterpSubst.lean` | the assignment commutes with weakening and substitution |
| `CtxInvariant` | `InterpSound.lean` | the assignment cannot distinguish definitionally equal contexts |
| `ModelData.Coherent` (3 fields) | `InterpSound.lean` | constants inhabit their types; `env.defeqs` holds in the model |
| `AxiomsValidated` | `InterpSound.lean` | **new** — each axiom in the declaration list has an inhabited type in the model |

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

## The remaining open items, ranked


1. **`IsDefEqU.sort_inv`** — gives `LevelAssign`, hence the interpretation.
   Single `sorry`, highest value in the project.
2. **`VEnv.addInduct` / `VInductDecl.WF`** — `sorry` *definitions* in
   `Theory/Inductive.lean`. These now block `cnst` too, not just the typing
   stream: the `.induct` case of the induction has to say what values the
   constants an inductive declaration introduces receive, and until `addInduct`
   is a definition the post-declaration environment is opaque and there is
   nothing to assign to. The set-theoretic side is finished and waiting —
   `SetModel/IndStage.lean` and `SetModel/IndCard.lean` supply the family, its
   constructors, its recursor and its ι-rule, all as members of the stage.
3. **Assembling the thirteen soundness cases into one `Sound` theorem.** This
   turned out to be a prerequisite for `cnst`, not a successor to it. The `.def`
   step has to show the body's denotation inhabits the declared type, and that
   is soundness applied to `VDefVal.WF`'s `HasType env ci.uvars [] ci.value
   ci.type`. So soundness and coherence are proved *together*, by the outer
   induction on the declaration list: at each stage, the thirteen-case induction
   runs against the coherence already established for that environment, and then
   the step lemmas extend it. This is not circular, but it does mean the two
   cannot be finished independently.
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

   The step is proved (`coherentOn_addConst`, `coherentOn_addDefEq`); what
   remains is the outer recursion, blocked on items 2 and 3. Two further lemmas
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
   independent of items 2 and 3.
