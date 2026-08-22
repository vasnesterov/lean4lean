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

Not done: `constDF` and `extra`, both of which need `ModelData.cnst` and its
coherence with `env.defeqs`. Also outstanding: parts 3 for `lamDF`/`forallEDF`
(the `∈` direction; part 4 is proved), which the analysis says needs nothing new.

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
| `ModelData.cnst` coherence | `constDF`, `extra` | **open** — see below |
| `IsDefEqU.sort_inv` | packaged as `LevelAssign` | **open**, one `sorry` |
| `IsDefEqU.forallE_inv` | — | **not needed** |
| `IsDefEqU.sort_forallE_inv` | — | **not needed** |

## The two remaining open items, ranked

1. **`IsDefEqU.sort_inv`** — gives `LevelAssign`, hence the interpretation.
   Single `sorry`, highest value in the project.
2. **`ModelData.cnst` and its coherence** — an induction over the declaration
   list (which `VEnv.WF'` already orders), assigning each constant a value and
   showing the assignment validates `env.defeqs`. This is where the
   well-foundedness that Carneiro's `|c| = |e| + 1` clause needs actually lives;
   displacing it here is what makes the term recursion in `SetModel/Interp.lean`
   structural. Independent of item 1 and of the injectivity stream.
