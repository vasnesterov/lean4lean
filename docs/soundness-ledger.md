# Soundness ledger: what the model's soundness proof consumes

For each of the thirteen constructors of `VEnv.IsDefEq`
(`Lean4Lean/Theory/Typing/Basic.lean`), what the soundness induction needs — and
in particular which *injectivity* facts, since that is what the injectivity
stream should prioritise.

Statements are machine-checked in `Lean4Lean/Theory/SetModel/InterpSound.lean`;
the case analysis below is **analysis, not a completed proof**, and is marked as
such. Weakening and substitution, which several cases consume, *are* proved
(`SetModel/InterpSubst.lean`, sorry-free).

## Headline

**No injectivity fact beyond `IsDefEqU.sort_inv` appears in any case.**

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

**Part 2 is a corollary of parts 1 and 3**, not a fourth branch of the induction:
if `α` is a proposition then `⟦α⟧ρ ⊆ {•}` and `⟦e⟧ρ ∈ ⟦α⟧ρ`, so `⟦e⟧ρ = •`.
That is `proofSound_of` in `InterpSound.lean`. The induction carries three parts.

## A consistency fact used throughout

For `Γ ⊢ f : forallE A B`, the split for `app` (on `srt Γ f`) and the split for
`forallE` (on `lvl (A::Γ) B`) **agree**:

```
srt Γ f  ≈  lvl Γ (forallE A B)  ≈  imax (lvl Γ A) (lvl (A::Γ) B)
```

and `imax u v` evaluates to `0` exactly when `v` does. So `f` is a proof iff `B`
is a proposition. This follows from `srt_sound`, `lvl_sound` and level
arithmetic — no injectivity. It is used in `appDF`, `lamDF` and `beta`.

## Case by case

| Rule | Part 3 (`⟦e⟧ ∈ ⟦A⟧`) | Part 4 (`≡` ⟹ `=`) | Injectivity |
|---|---|---|---|
| `bvar` | valuation is typed (`mem_interpCtx_cons`) + **weakening** for the `.lift` in `Lookup` | — | none |
| `symm` | — | IH | none |
| `trans` | — | IH | none |
| `sortDF` | `U_mem_succ`; **this is where the universe bound is spent** | `l ≈ l'` gives equal evaluations | none |
| `constDF` | `cnst` coherence | `ls ≈ ls'` + `cnst` coherence | none |
| `appDF` | IH gives `⟦f⟧ρ ∈ ⟦forallE A B⟧ρ`; apply at `⟦a⟧ρ`; **substitution** for `B.inst a` | IHs + `srt_congr` for the split | none |
| `lamDF` | graph is a function into `⋃⟦B⟧`; split agreement | IHs; both bodies live in `A::Γ` | none |
| `forallEDF` | `U_mem_succ` at `imax u v` | IHs | none |
| `defeqDF` | IH part 4 on the type gives `⟦A⟧ρ = ⟦B⟧ρ` | IH | none |
| `beta` | — | **substitution** + part 3 for `e'` (Carneiro's entanglement) + the graph is a function | none |
| `eta` | — | **weakening** for `e.lift` + an internal function equals its own graph | none |
| `proofIrrel` | — | part 1 gives `⟦p⟧ρ ⊆ {•}`, part 3 puts both values in it | none |
| `extra` | `cnst` coherence with `env.defeqs` | same | none |

### Notes on the two cases I would check first

**`beta`.** `⟦(λA.e) e'⟧ρ = (graph) ‘ ⟦e'⟧ρ = ⟦e⟧(snoc ρ ⟦e'⟧ρ) = ⟦e.inst e'⟧ρ`.
The middle step needs `⟦e'⟧ρ ∈ ⟦A⟧ρ` — which is part 3 for `e'`, i.e. exactly
the entanglement Carneiro flags. In `SetModel/InterpSubst.lean` this is the
`top` field of `AgreeInst`, stated as a hypothesis rather than proved, so the
substitution lemma is available to the induction without circularity.

**`eta`.** `⟦λA. (lift e) (bvar 0)⟧ρ` is `{⟨v, ⟦e⟧ρ ‘ v⟩ | v ∈ ⟦A⟧ρ}` after
weakening, and this equals `⟦e⟧ρ` because an internal function equals its own
graph. That is surjective pairing for `Y ^ X`, provable from
`function_eq_of_subset` and `value_eq_of_kpair_mem`; the `Prop` branch is
separate and immediate (both sides are `•`).

## Full ingredient list

| Ingredient | Consumed by | Status |
|---|---|---|
| `interp_liftN` (weakening) | `bvar`, `eta` | **proved** |
| `interp_inst` (substitution) | `appDF` part 3, `beta` | **proved** |
| `AgreeInst` entanglement | `beta` | **hypothesis by design** |
| `LevelAssign.lvl_congr` / `srt_congr` | every congruence case | **proved** |
| `LevelAssign.Stable` | `bvar`, `beta`, `eta` | hypothesis |
| `U_mem_succ` + explicit bound | `sortDF`, `forallEDF` | **proved** |
| `piProp_mem_UProp` | part 1, `forallE` case | **proved** |
| validity (`Γ ⊢ e : A → IsType Γ A`) | `appDF`, to level the `∀` | available, `Theory/Typing/` |
| internal function = its graph | `eta` | routine, not yet written |
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
