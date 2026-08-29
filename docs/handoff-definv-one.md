# Handoff: `DefInv ∅ 1 1` — **REFUTED**

**Target of this stream:** decide `DefInv ∅ 1 1`, the single open input that
`docs/handoff-appcase.md` §5 named as the thing to pick up first, because it decides
`AppCase.lean`'s dichotomy `AppCaseRefute.thm_utype_one_false_of_defInv`.

**Verdict: it is false.** Clause (2) fails — the reference's `unique.tex:33`, in its literal
form, with no strengthening.

**Everything marked *machine-checked* is a sorry-free declaration in
`Lean4Lean/Theory/Typing/DefInvRefute.lean`, axioms `[propext, Quot.sound]` only** (verified
with `#print axioms` on every declaration). Claims marked *analysis* or *source reading* are
not machine-checked; the distinction is load-bearing in §4 and §6.

---

## 0. The headline

`⊢₁` is not invariant under changing the *type of a context variable* along a `⊢₁`-conversion.
Clause (2) of definitional inversion asks for exactly that transport: from
`Γ ⊢ₙ ∀x:α.β ≡ ∀x:α'.β'` it concludes `Γ,x:α ⊢ₙ β ≡ β'`, while a derivation of the premise may
compose two ∀-congruences whose codomain premises live in `Γ,x:α` and `Γ,x:α'` respectively.
The two contexts declare `x` at syntactically different types, and `⊢₀` — where all the typing
premises of a `⊢₁` conversion sit — has no conversion rule to bridge them.

    []             ⊢₁  ∀x:U_{max(p,p)}. x  ≡  ∀x:U_p. (λ y:U_p. y) x      derivable
    x:U_{max(p,p)} ⊢₁  x  ≡  (λ y:U_p. y) x                               NOT derivable
    x:U_p          ⊢₁  x  ≡  (λ y:U_p. y) x                               derivable (one β)
    x:U_{max(p,p)} ⊢₂  x  ≡  (λ y:U_p. y) x                               derivable

Consequences, in decreasing scope:

* `DefInv ∅ 1 1` is false (`defInv_one_false`), so `∀ n, DefInv ∅ 1 n` is false
  (`defInv_all_false`) — **the route's own target**.
* `thm:1dinv` (`unique.tex:262`, "⊢ₙ₊₁ has definitional inversion") is **false as stated**, at
  its first instance: `DefInv 0` is a theorem (`DefInv.zero`) and `DefInv 1` is refuted
  (`defInv_step_zero_false`). So the break in `unique.tex` is not only at `thm:utype`
  (`SubstC`, `docs/reference-gap-thm-utype.md` §§1–3) but also in §§3–4.
* `thm:utype`'s **statement** is *not* refuted. It is conditional on definitional inversion,
  and at `n = 1` over `∅` that hypothesis is now known false, so the theorem is *vacuously
  true* there (`thm_utype_one_vacuous`). `AppCaseRefute.uniqN_false` therefore refutes the
  **unconditional** reading and nothing more.
* **Nothing about Lean's type theory.** `cod_conv_bvar_succ` machine-checks that the very
  conversion clause (2) asks for holds at `n = 2`. Exactly like `AppCaseRefute.lhs_conv_a_succ`.
* **The route is not dead.** `IsDefEqU.sort_inv_of_defInv` and
  `IsDefEqU.sort_forallE_inv_of_defInv` consume only clauses (1) and (3) — see §5, which is the
  actionable part of this handoff.

---

## 1. The witness

`∅` for the environment (no constants, no `defeqs`), one universe parameter `p := .param 0`,
`U = 1`.

    dom  := .sort (max p p)          dom' := .sort p          max p p ≈ p,  max p p ≠ p
    cod  := .app (.lam dom' (.bvar 0)) (.bvar 0)             -- (λ y:U_p. y) x
    piL  := .forallE dom (.bvar 0)                           -- ∀x:U_{max(p,p)}. x
    piR  := .forallE dom' cod                                -- ∀x:U_p. (λ y:U_p. y) x

`hpi : [] ⊢₁ piL ≡ piR` is `trans (forallEDF hdom rfl) (forallEDF rfl bvar_conv_cod_right)`:

* `hdom` is one `sortDF`, `max p p ≈ p` — the only rule in play with no typing premise that
  changes a *type*;
* the first codomain premise is reflexivity **at a term that is `⊢₀`-typed in that context**
  (`step1_codomain_typed0 : [dom] ⊢₀ .bvar 0 : dom`), so the repo's one documented deviation
  from the reference — unconditional `rfl` — is **not** load-bearing here (§4);
* the second codomain premise is one `beta` step in `[dom']`, whose two typing premises are
  `bvar` rules at `⊢₀`.

`DefInv.forallE hpi |>.2` is `[dom] ⊢₁ .bvar 0 ≡ cod`, and `bvar_not_conv_cod` refutes it.

## 2. Why the negative half is short

Same shape as `SubstCRefute.stuck`, with the context carried in the motive instead of
eliminated by closedness. The one fact that discharges every rule:

> **In `[dom]`, `cod` is not `⊢₀`-typeable at any type** (`cod_not_hasType0`), because typing it
> needs `.bvar 0` at the λ's *annotated* domain `dom'`, and the variable's unique `⊢₀` type is
> `dom` (`bvar_not_hasType0_left`, from `HasTypeN.uniq_zero` and `max p p ≠ p`).

`rfl` relates it to itself; `symm`/`trans` are recursive **in the same context**;
`sortDF`/`constDF`/`lamDF`/`forallEDF` have the wrong head shape; `appDF`, `beta`'s left side,
`eta`'s right side and `proofIrrel` all carry a `⊢₀` typing premise that fails; `beta`'s right
side closes by `Stratified.instN` at `m = 0`; `extra` is empty over `∅`.

The two context-*changing* congruences (`lamDF`, `forallEDF`) are discharged by shape, so their
induction hypotheses — which would need the context hypothesis in an extended context — are
never used. That is what makes a context-parametric `stuck` no harder than the closed one.

## 3. Machine-checked inventory

All in `Lean4Lean/Theory/Typing/DefInvRefute.lean`.

| name | statement |
|---|---|
| `hdom` | `Γ ⊢₁ dom ≡ dom'`, any `Γ` — one `sortDF` |
| `bvar_hasType0_right` | `[dom'] ⊢₀ x : dom'` |
| `bvar_not_hasType0_left` | `¬ [dom] ⊢₀ x : dom'` |
| `cod_not_hasType0` | `cod` is `⊢₀`-untypeable in any `Γ` where `x` is not `⊢₀`-typed at `dom'` |
| `stuck` | `⊢₁` relates `cod` to nothing but itself, in any such `Γ` |
| `bvar_not_conv_cod` | **`¬ [dom] ⊢₁ x ≡ cod`** |
| `bvar_conv_cod_right` | `[dom'] ⊢₁ x ≡ cod` — the same pair, other context, one `beta` |
| `hpi` | **`[] ⊢₁ piL ≡ piR`** |
| `step1_codomain_typed0` | the `rfl` premise is backed by a `⊢₀` typing (§4) |
| `env_ordered`, `dom_type`, `dom'_type`, `piL_type`, `piR_type` | the environment, the two contexts and both Π-types are well-formed — the refutation does not turn on junk |
| **`defInv_one_false`** | **`¬ DefInv ∅ 1 1`** |
| `defInv_one_witness` | the same as an explicit `∃`: two Π's, `⊢₁`-convertible, codomains not |
| **`defInv_all_false`** | **`¬ ∀ n, DefInv ∅ 1 n`** — the route's own target |
| `defInv_forallE_right_false` | the mirrored reading (codomains compared under `α'`) is false too, by the same instance `symm`'d |
| `defInv_step_zero_false` | `¬ (DefInv 0 → DefInv 1)` — `thm:1dinv` at its first instance |
| `cod_conv_bvar_succ` | `[dom] ⊢₂ x ≡ cod` — the failure is the index |
| `thm_utype_one_vacuous` | `DefInv ∅ 1 1 → UniqN ∅ 1 1` — the dichotomy's second horn |
| `sort_not_proof0`, `forallE_not_proof0`, `lam_not_proof0` | `proofIrrel` cannot relate a sort, a Π or a λ — the `proofIrrel` case of clauses (1) and (3), any env, any context |
| `SortInvN`, `SortForallEDisjN` | clauses (1) and (3), named separately |
| `sortInvN_of_defInv`, `sortForallEDisjN_of_defInv`, `sortInvN_zero`, `sortForallEDisjN_zero` | they are implied by `DefInv`, and hold at `n = 0` |
| `sort_inv_of_sortInvN`, `sort_forallE_inv_of_sortForallEDisjN` | the two live reductions, restated against the clause each actually consumes (§5) |

## 4. Fidelity: is this the reference's clause (2), or a transcription artifact?

*Source reading against `~/lean-type-theory`, not machine-checked.* Checked because the repo
carries one documented deviation (`Stratified.lean`'s unconditional `rfl`) and because a
refutation of a published theorem must not turn on it.

| rule used | reference | transcription |
|---|---|---|
| ∀-congruence | `axioms.tex:37` — `Γ⊢α≡α'` and `Γ,x:α⊢β≡β'`, **no typing premises**, codomain premise in the **left** domain's context | `Stratified.forallEDF`, identical |
| universe congruence | `axioms.tex:34` — no typing premises | `Stratified.sortDF`, plus level-`WF` side conditions (satisfied) |
| β | `axioms.tex:38` — `Γ,x:α⊢e:β` and `Γ⊢e':α` | `Stratified.beta`, same two |
| reflexivity | `axioms.tex:31` — **typed**: `Γ⊢e:α` | `Stratified.rfl`, unconditional (the deviation) |
| `trans` | `axioms.tex:33` | `Stratified.trans`, same |
| clause (2) | `unique.tex:33` — "then `Γ⊢ₙ α≡α'` **and `Γ,x:α ⊢ₙ β≡β'`**" | `DefInv.forallE`, identical, same context |

**The deviation is not load-bearing.** Both `rfl` uses in `hpi` are at terms that are `⊢₀`-typed
in their contexts — `[dom] ⊢₀ x : dom` (`step1_codomain_typed0`) and `[] ⊢₀ dom' : U_{Sp}`
(`dom'_type`) — so both are available under the reference's *typed* reflexivity as well.
(Separately: the reference's own basics (2) asserts `⊢₀ ⊆ ⊢₁`, and `⊢₀` is unconditional
syntactic equality by `unique.tex:12`, so the reference's `⊢₁` contains unconditional
reflexivity anyway. The witness does not need that argument.)

**Level equality.** `max(p,p) ≡ p` is derivable in the reference's algorithmic level judgment
(`axioms.tex:44–46`), not only under the semantic reading — this check is `docs/reference-gap-thm-utype.md` §6's, unchanged.

**`⊢₀` typing is syntactically unique in the reference too.** Its `⊢₀` has no usable conversion
(`unique.tex:12,14`), its variable rule types `x` at its declared type only, and weakening
cannot retype. So `x:U_{max(p,p)} ⊬₀ x : U_p`, which is the engine.

**Where the reference's proof of `thm:1dinv` clause (2) goes wrong** (*analysis*): it applies
`thm:ckappa` to get `∀x:α.β ↝*_κ ∀x:α₁.β₁ ≡_p ∀x:α'₁.β'₁ *↜_κ ∀x:α'.β'` and then says "if
these are `≡_p` equivalent using the compatibility rule then we are done". The `≡_p`
compatibility premise for ∀ lands `β₁ ≡_p β'₁` in `Γ,x:α₁`, the right-hand reduction lands in
`Γ,x:α'`, and the conclusion is wanted in `Γ,x:α`; and `≡_κ` additionally requires both
endpoints to be `⊢ₙ`-typed *in the conclusion's context*, which is exactly what fails here. The
proof transports between three contexts without justification. **The conclusion is not merely
unjustified — it is false.**

## 5. What survives, and what to do about it — **the actionable part**

`Theory/Typing/UniqueTypingN.lean`'s two live reductions,
`IsDefEqU.sort_inv_of_defInv` and `IsDefEqU.sort_forallE_inv_of_defInv`, use `dinv n` at
**exactly one projection each** — `.sort` and `.sort_forallE`, i.e. clauses (1) and (3).
Neither touches clause (2), the only clause refuted. So:

* their hypothesis `∀ n, DefInv env U n` is now known unsatisfiable over `∅`, which makes them
  vacuous as stated;
* restated against the clause each actually consumes they go through **verbatim** —
  `sort_inv_of_sortInvN` and `sort_forallE_inv_of_sortForallEDisjN`, machine-checked in the
  new file, proofs character-for-character the same;
* `∀ n, SortInvN env U n` and `∀ n, SortForallEDisjN env U n` are **not refuted by anything
  known**, at any index above 0.

**Recommended edit, for whoever owns `UniqueTypingN.lean`** (I did not make it — that file is
another stream's): split `DefInv` into its three clauses, or add the two single-clause
predicates, and weaken the two reductions' hypotheses to them. Everything else in that file
(`Stratified.uniq`, `IsDefEqN.sort_imax_congr`, `DefInv.sort_proofIrrel`) genuinely needs more
than one clause and should keep `DefInv`. The new file's `SortInvN`/`SortForallEDisjN` are
deliberately declared inside `namespace DefInvRefute`, not `namespace VEnv`, to avoid the
double-declaration problem `docs/handoff-appcase.md` §6.3 records for `PropUniq` and
`PropTypeAgree`; a `UniqueTypingN.lean` version should take the `VEnv` names.

## 6. What is open

* **`SortInvN ∅ 1 1` and `SortForallEDisjN ∅ 1 1`** — clauses (1) and (3) at `n = 1`. Neither
  proved nor refuted. This witness does not reach them: it never relates a sort to a non-sort.
  These are now the only clauses anything downstream wants (§5), so they are the successor to
  this stream's question.
  *Analysis, not machine-checked*, on how they look, correcting `docs/handoff-appcase.md` §5:
  its reading of clauses (1) and (3) as "reachable by one induction, modulo a confluence
  argument at index 1" survives — clause (2) was the one that fell, and it fell for a reason
  orthogonal to confluence (context transport, not joinability). The confluence obligation for
  (1) and (3) is unchanged and is still the smallest instance of `unique.tex` §§3–4 that
  exists. One thing the present work does add, **machine-checked**: `proofIrrel` can never
  relate a sort, a Π or a λ to anything, in any environment and any context, because a proof's
  `⊢₀` type must itself be `⊢₀`-typed at `.sort .zero`, while those three have `⊢₀` types of
  the shapes `.sort (.succ _)`, `.sort (.imax _ _)` and `.forallE _ _` — `sort_not_proof0`,
  `forallE_not_proof0`, `lam_not_proof0`. That is the `proofIrrel` case of both clauses, for
  free, and it is one of the two cases §9a of `docs/reference-gap-thm-utype.md` listed as open.
  **What remains for (1) and (3) is exactly the `trans` case**, i.e. the confluence argument —
  a sort *is* `≡₁`-related to β-redexes, so no shape invariant works without a reduction
  relation.
* **Whether any repair of clause (2) is usable.** Two are refuted here (left context,
  `defInv_one_false`; right context, `defInv_forallE_right_false`). Two are untouched:
  "in *some* context", and "at index `n+1`" — `cod_conv_bvar_succ` shows the witness satisfies
  the second. Both are *weaker conclusions*, and `docs/reference-gap-thm-utype.md` §2's
  arithmetic says index slack is unusable by `thm:utype`'s consumer. Not re-derived here.
* **The five `app`-case statements** of `docs/handoff-appcase.md` — untouched. Note however
  that `AppTypeUniq.appDisj`, `.appPropDisj` and `.appUniqLvl` take `DefInv` as a hypothesis;
  over `∅` at `n = 1` those three are now vacuous. They should be restated against
  `SortForallEDisjN`/`SortInvN`, which is what their proofs actually use.

## 7. What was tried, and the exact failing step

1. **Refute clause (3)** (`⊢₁ U_ℓ ≢ ∀x:α.β`). Failed at: there is no zigzag. The only rules
   that move a sort at `⊢₁` are `sortDF` (sort to sort) and β-expansion; `proofIrrel` cannot
   touch a sort (§6); so a sort/Π identification would need a genuine confluence failure, and
   β-expansion/contraction is deterministic per redex position. *Analysis; abandoned, not
   proved impossible.*
2. **Refute clause (1)** — same, same reason.
3. **Refute clause (2) via `SubstC`-style substitution.** The route `M ≡₁ M'` by `appDF` then
   β on both sides gives two Π's whose components need `X[d] ≡₁ X[d']` from `d ≡₁ d'`. Failed
   at: `appDF`'s premises force `d` and `d'` to be `⊢₀`-typed at the **same** type, which is
   exactly what makes the `SubstCRefute` obstruction unavailable — the substituted terms are
   never "typeable only one level up". *Analysis.*
4. **Refute clause (2) via η-relabelling.** `lamDF` can change a λ's annotation for free, so
   `e ≡₁ λx:α. e x ≡₁ λx:α'. e x`. Failed at: η back requires `⊢₀ e : ∀x:α'.β'` and `⊢₀` types
   are unique, so `α' = α`; and β on the relabelled λ requires the body to be `⊢₀`-typed at the
   new annotation, which fails for the same reason. *Analysis.*
5. **Refute clause (2) via context transport.** **Succeeded**, §1. The first attempt at this
   used `rfl` on a body that is *not* `⊢₀`-typeable in the left context, which would have made
   the witness depend on the repo's unconditional-`rfl` deviation; it was rebuilt so that both
   `rfl`s are `⊢₀`-backed (§4). **That rebuild is the difference between a result about this
   repo and a result about the reference — do not lose it.**
6. **Prove `DefInv ∅ 1 1`.** Not attempted beyond the scoping in §6: clause (2) is false, so
   the structure is refuted regardless of (1) and (3).

## 8. Two things not to redo

* **Do not re-derive the witness.** It is eight short declarations plus one 40-line induction.
* **Do not read `defInv_one_false` as "unique typing fails for Lean", or as "`thm:utype` is
  false".** `cod_conv_bvar_succ` and `thm_utype_one_vacuous` are in the file for exactly these
  two misreadings. The honest three-line summary: *the repo's indexed proxy is false; the
  reference's `thm:1dinv` is false as stated; `thm:utype`, `thm:unique` and Lean's type theory
  are untouched.*

## 9. Corrections to what this stream was handed

* `docs/handoff-appcase.md` §2 and §5 present `DefInv ∅ 1 1` as the deciding question and give
  the dichotomy. Both are correct; the answer is the second horn. §5's guess that "clauses (1)
  and (3) look reachable" is **not** contradicted — it was clause (2), which §5 called "the hard
  one", that fell, and it fell to context transport rather than to confluence.
* `docs/reference-gap-thm-utype.md` §4 said "**`DefInv` in the reference's literal form** …
  Definitional inversion is untouched." That was correct about the `SubstC` witness and wrong
  as a general claim. §4 has been amended (by this stream) with both amendments marked; §1, §7,
  §9, §9a and §10 have been corrected where they depended on it.
* `docs/reference-gap-thm-utype.md` §9a's table already listed clause (2)'s open case as "the
  IH lands `B ≡ B'` in context `A'::Γ`, the goal is `A::Γ` — context conversion at a preserved
  index". That entry was right, and it is now a counterexample rather than an open case. The
  table has been updated.
* Nothing in `AppCase.lean`, `ShapeSpine.lean`, `SubstCRefute.lean` or `UniqueTypingN.lean` is
  wrong; `thm_utype_one_false_of_defInv` is simply now known to be vacuous.

## 10. Should this go to the reference's author?

*This is the human's decision, not an agent's, and nothing has been sent.* The material fact:
`thm:1dinv` clause (2) is false as stated, at `n+1 = 1`, over a signature with no constants, no
inductives and no quotients, and the counterexample is four lines. It is independent of the
`SubstC` gap already recorded, and it is in a different theorem. `docs/reference-gap-thm-utype.md`
§4 and §11 collect the other findings in the same neighbourhood.
