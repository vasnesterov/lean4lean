# Handoff: the stratified route to `IsDefEqU.sort_inv`

Rewritten after four candidate repairs failed their own row-zero checks. **The previous
version of this file described a route that is now known to be closed**; if you are reading a
cached copy, stop and re-read this one.

**Target:** `Lean4Lean.VEnv.IsDefEqU.sort_inv` and its family in
`Theory/Typing/Injectivity.lean`. **Still open, and the target statement has not moved.**

### Where the route stands, plainly

| statement | status |
|---|---|
| `PropTypeAgree` | **open.** Five of twelve conversion cases close. Three characterised obstructions: `forallEDF` (context conversion, index drop), `proofIrrel` (self-reference), `eta` (needs `SortForallEDisjoint`). `constDF`, `appDF`, `beta`, `extra` uncharacterised. |
| `SortForallEDisjoint` | **one open case, and likely true.** Six of seven typing cases close from `DefInv` alone; only `AppCase` remains, and a refutation is *provably impossible* at the model's own witness (§9). **Satisfiable** (`SortForallEDisjoint.zero`). **The hereditary shape agreement proposed for `AppCase` is now closed both ways** — as disjointness it is *equivalent* to the statement itself, as agreement it is *false* (§9, machine-checked). `AppCase` is the statement's own fixpoint. **The `common_sort` lead is now closed too (§11)** — the route has no untried idea left in this neighbourhood. |
| `PropUniq`, `SortUniq` | **in the normalisation family, and no model route.** Both fail the criterion's `trans` test; `SortUniq` is refuted as a semantic consequence by the cumulativity check, and the model is parameterised on it. |
| `unique.tex` §§3–4 at the index (the reduction relation §8 asks for) | **closed (§12).** Its two substitution lemmas — and a third site nobody had counted — all need `SubstT`, substitution into a *typing* at a preserved index. That is a different statement from the already-refuted `SubstC`, and it is **also false**, machine-checked (`SubstTRefute.lean`). |
| the reference | **three documented defects**: two in §2 (one machine-checked, one a reading result with a repair) and `thm:ckappa`'s base case, machine-checked (§12). |

The obstruction was diffuse and is now two named statements. What the route produced beyond
that is in §7 — read it, because it is more than what it closed.

---

## 0. Read this first

Two things a fresh reader will otherwise re-derive:

1. **The reference's proof of `thm:utype` is invalid**, machine-checked, over the empty
   environment. Not "hard", not "unproved" — the inference it uses at `unique.tex:51` is
   false. `docs/reference-gap-thm-utype.md` is the write-up; read its **§4 (scope)** before
   quoting anything else, because the *statement* of `thm:utype` is **not** refuted and
   `DefInv` in its literal form is **not** refuted.
2. **Every repair to the alternation index is closed by one arithmetic argument** (§3 below).
   The argument does not mention the repair's shape, so it closes the family: depth-0 rules,
   general-depth `Ctx.InstN` rules, explicit substitutions, and context morphisms alike.
3. **The logical-relation route is scoped and priced out** — §13 and `docs/logrel-scope.md`.
   Before quoting §8's last bullet, read §13: two of that bullet's three claims were wrong,
   and the route's own row-zero is **machine-checked** in `Theory/Typing/LogRelRowZero.lean`.
   The finding with the widest reach is (b) there, and it is not about logical relations at
   all: **the environment class every target in `Injectivity.lean` is stated over is not
   normalising**, so it blocks any normalisation-flavoured route and needs a `Verify/`-side
   re-cut first.
4. **§13(b)'s conclusion does not hold at its own witness — §14, machine-checked.** The
   cycle `LogRelRowZero.lean` exhibits is between two *proofs of one proposition*, which
   `proofIrrel` identifies anyway, so it breaks **reduction** without enlarging
   **conversion**: `Theory/Typing/CycleConv.lean` shows `loopEnv`'s conversion relation *is*
   that of a rule-free, `noUnsafe` environment. `sort_inv` also **survives** refutation
   there. And the re-cut §13(b) asks for would not help: `sort_inv`'s `proofIrrel` case is
   live **over the empty environment**, from the context alone. Do not re-run either check
   without reading §14.

The general rule the previous handoff drew — *necessity has to be checked against the
specification, not the tree* — held up and then paid again in the opposite direction: this
time the specification was the thing that was wrong, and the check that settled which way it
ran was verifying that this tree's one deviation only *enlarges* the judgment, so an
underivability result holds a fortiori for the reference.

---

## 1. What is proved, sorry-free

All `#print axioms` clean: `propext` and `Quot.sound` only. No `sorryAx`, no `native_decide`,
no `bv_decide`, no axiom added.

| Name | File | What |
|---|---|---|
| `Stratified.{mono, weakN, instN}`, `IsDefEqN.{zero_iff, inst0}`, `IsDefEq.stratifyN` | `Typing/Stratified.lean` | the index, the four n-provability basics, weakening and substitution |
| `DefInv`, `DefInv.zero` | `Typing/UniqueTypingN.lean` | definitional inversion (`unique.tex:29–35`) and `thm:0dinv` |
| `SubstC`, `SubstC.zero`, `SubstC.of_hasTypeN_zero` | `Typing/UniqueTypingN.lean` | the inference at `unique.tex:51`, isolated; true at `n = 0` and on the conversion-free fragment |
| `HasTypeN.{bvar,sort,const,app,lam,forallE}_inv` | `Typing/UniqueTypingN.lean` | subject-shape inversion at the index — **the most reusable thing here** |
| `Stratified.uniq`, `HasTypeN.uniq_zero` | `Typing/UniqueTypingN.lean` | `thm:utype` from `DefInv` + `SubstC`; content only at `n = 0` |
| `IsDefEqU.sort_inv_of_defInv`, `sort_forallE_inv_of_defInv` | `Typing/UniqueTypingN.lean` | **the target reduced to `∀ n, DefInv`** — uses neither `uniq` nor `SubstC` |
| `DefInv.sort_proofIrrel` | `Typing/UniqueTypingN.lean` | at the index, `unique.tex:266` needs only `DefInv` clause (1), not `SortUniq` |
| `SubstCRefute.{lhs_not_hasType0, stuck, substC_false, defInv_forallE_inst_false}` | `Typing/SubstCRefute.lean` | the refutation |
| `IsPropN`, `PropTypeAgree` | `Typing/UniqueTypingN.lean` | the set model's syntactic import, at the index |
| `sortNotProof_of`, `forallENotProof_of` | `Typing/UniqueTypingN.lean` | **the payoff, checked not assumed**: `PropTypeAgree` + `DefInv` at `n` give "a sort is not a proof" and "a Π-type is not a proof" at `n` — both the induction hypothesis, so not circular |
| `SortForallEDisjoint`, `SortForallEDisjoint.AppCase`, `sortForallEDisjoint_of` | `Typing/UniqueTypingN.lean` | the primitive `PropTypeAgree` needs, and six of its seven cases |
| `PropNotProof`, `PropTypeAgree.{eta_case, proofIrrel_case}`, `propNotProof_of` | `Typing/UniqueTypingN.lean` | each case closes **from its residual and nothing else** — which is what makes the residual an exact obligation rather than an approximation |
| `Apply`, `Apply.{conv_head, hasType}`, `Apply₂.{left,right}` | `Typing/ShapeSpine.lean` | spines at the index; `hasType` is the collapse lemma — a spine result is a type of the applied term |
| `SortForallEDisjointH{,₂}.iff`, `SortForallEDisjoint.appCase` | `Typing/ShapeSpine.lean` | **the hereditary disjointness is equivalent to `SortForallEDisjoint`**, and `AppCase` follows from the statement itself — §9 |
| `typeShapeAgree_false`, `substShapeAgree_false` | `Typing/ShapeSpine.lean` | **the agreement (`iff`) form is FALSE at `n = 1`**, by `SubstCRefute`'s witness lifted to a term with two types |
| `SubstDisj`, `SubstDisj.zero`, `applyDisj`, `applyDisj_zero` | `Typing/ShapeSpine.lean` | the surviving form, named and shown satisfiable; with `DefInv` it gives spine determinism at a type |
| `SortForallEDisjoint.zero`, `SortForallEDisjoint.AppCase.zero` | `Typing/UnivDiscrim.lean` | **the primitive the whole route funds is satisfiable**, at the base index, next to `DefInv.zero`/`SubstC.zero` |
| `succ_eq_imax`, `univ_premises_satisfiable`, `strong_univ_premises_satisfiable` | `Typing/UnivDiscrim.lean` | **a universe does not discriminate a sort from a Π** — the `common_sort` lead, closed in both judgments (§11) |
| `HasTypeStrong.regular`, `HasTypeStrong.sortType` | `Typing/UnivDiscrim.lean` | **regularity is free in the type-indexed judgment** — no `Ordered`, no `OnCtx`, no `CtxStrong`, no hypothesis at all. Contrast `IsDefEqStrong.isType'`, which needs all three |
| `SortForallEDisjointSUniv.iff` | `Typing/UnivDiscrim.lean` | the universe-relativised statement **is** the statement — trap #11 in a new instance |
| `appCase_ih_vacuous` | `Typing/UnivDiscrim.lean` | the `app` case's induction hypothesis at `f` is *vacuously true*, provable from `DefInv` with the sub-derivation unused |
| `loop_conv_iff`, `loopEnv_conv_iff`, `sort_inv_transfer` | `Typing/CycleConv.lean` | **the δ-cycle of `LogRelRowZero.lean` adds no conversions** — `loopEnv`'s conversion relation *is* that of `loopEnv2`, which has no rule at all; so the six targets there are the targets at a cycle-free environment (§14) |
| `loopEnv2_wf_noUnsafe`, `loopEnv2_no_defeqs` | `Typing/CycleConv.lean` | …and `loopEnv2` is `VEnv.WF` by two `.axiom` steps, `noUnsafe`, rule-free |
| `empty_ctx_inconsistent` | `Typing/CycleConv.lean` | **the `proofIrrel` obstruction is not an environment fact**: `sort_inv`'s own hypotheses inhabit every proposition over `VEnv.empty`, from the context |
| `propLoopEnv`, `propLoop_headStep_not_wf`, `propLoop_no_direct_collapse` | `Typing/CycleConv.lean` | the row-zero cycle re-aimed at a block of *propositions*, where the collapse recipe provably does not apply |

**The inversion lemmas are the asset.** They made the refutation a fifteen-line induction
instead of a confluence argument, and they made the `:266` improvement a five-line proof.
Reach for them before writing any new induction over `Stratified`.

---

## 2. The two reference defects, with confidence levels

Do not blur these.

**(a) `unique.tex:51` — machine-checked, empty environment.** `thm:utype`'s application case
uses "from `Γ,x:α ⊢ₙ β ≡ β'` and `Γ ⊢ₙ e₂ : α`, conclude `Γ ⊢ₙ β[e₂/x] ≡ β'[e₂/x]`". False at
`n = 1`. The counterexample puts the type mismatch **under an application**, where no
premise-free rule reaches — a first attempt that put it in a *binder annotation* was **not** a
counterexample, because `lamDF` + `sortDF`, both premise-free, repaired it. Write-up:
`docs/reference-gap-thm-utype.md`.

**(b) `unique.tex:180` — reading result with a worked configuration, plus a repair.** The
bullet concludes the lift's *output* type is a `Prop`; it does not follow, since
`Quot.lift`'s `{α : Sort u}` and `{β : Sort v}` are independent (verified against
`~/lean4/src/Init/Prelude.lean:443` and this repo's `quotLiftConst`). The reference's own
`typesys.tex:50` configuration is a counterexample to `thm:gg_compat`. **Repairable**, by the
reference's own device: a `K⁺` rule for `Prop`-quotients, exactly parallel to the one
`unique.tex:103` gives subsingleton inductives, with every clause of its justification
transferring verbatim. `reference-gap-thm-utype.md` §11.

---

## 3. Four candidates, four row-zero failures

| candidate | check | outcome |
|---|---|---|
| instantiation as a rule | does `thm:ckappa` absorb the new case? | **no**, by arithmetic — see below |
| a different stratification | is there a measure? | **no** — height gives `≤` not `<`; the tension is generic to the family |
| de-stratify | how many uses of unique typing in §§3–4? | **three**; `:180` now eliminated, `:266` reduced, `:272` remains |
| `sort_not_proof` from the model | which statement can a model reach? | **blocked** — the model is *parameterised* on `SortUniq` |

**The arithmetic that closed the first family.** Write `k` for the index an instantiation rule
concludes at and `j` for its typing premise's index.

* **(R1) `thm:utype`'s application case forces `j = k`** — the `app` rule hands it
  `Γ ⊢ₙ e₂ : A` and an IH at index `n`, and its conclusion must be at `n`.
* **(R2) `thm:ckappa` forces `j ≤ k−1`** — `≡ᵏ` is defined (`unique.tex:240`) with the side
  condition `Γ ⊢ e₁,e₂ : α`, a `⊢ₖ₋₁` typing under the §3 convention (`unique.tex:64`).

Both halves machine-checked at `k = 1`. The argument never mentions the rule's depth or
premise shape, so it closes explicit substitutions and context morphisms too — **the context
machinery was never the binding constraint.**

**The model check.** `Theory/SetModel/` is parameterised throughout on
`(L : LevelAssign env nv)` and nothing constructs one; `LevelAssign.srt_sound` *is* `SortUniq`
restated. And `SortUniq` is **false in the cumulative extension**, which any nested-universe
model validates — so no model can supply it. Recorded in `Typing/SortUniq.lean`'s docstring,
where its consumers look.

---

## 4. Where the obstruction sits: two statements

**"A sort is not a proof", and its Π analogue.** `:180` is eliminated by the `K⁺` repair;
`:266` needs only `DefInv` clause (1) (machine-checked); `:272` and clause (3)'s `proofIrrel`
case need exactly this.

* *Syntactically*, unstratified, it needs `uniq`, and the self-reference has no decreasing
  measure — the obvious height measure gives `≤`, not `<`.
* *Semantically*, it needs the model, which is parameterised on `SortUniq`.
* *At the stratified index* it is the induction hypothesis — which is what the index is
  **for**, and the index is broken by (a) above with no repair.

---

## 5. The live lead: `PropTypeAgree`

**The criterion, first, because it predicts rather than explains.**  It reformulated itself on
its third application, in the direction of being more predictive; the sharpened form is the
one to use.

> **Does the statement's induction ever have to look at a conversion derivation at all?**
> If it does not, it is tractable.  If it does, it is tractable exactly when its conclusion is
> **propagated along** the conversion rather than **asserted of** its endpoints — the first
> tolerates an arbitrary middle term at `trans`, the second does not.

The second clause is the earlier form of the criterion and is now a special case of the first.

> **A companion test, because the criterion is necessary and not sufficient.**  At each
> recursive position of the proposed induction, **is the induction hypothesis non-vacuous?**
> Run it by instantiating the IH at that position and trying to prove it from the ambient
> hypotheses *without the sub-derivation*; if that succeeds, the position carries no
> information.
>
> `SortForallEDisjoint` is the case that forced this.  It **passes** the criterion outright —
> its induction is on typing, so `trans` never arises — and it is still open, at `app`, for a
> reason the criterion cannot see: the recursive position that could reach what the case needs
> is `f`, whose type is a Π, and the IH there is guarded by "the type is sort-shaped".
> `appCase_ih_vacuous` (`Typing/UnivDiscrim.lean`) proves that IH from `DefInv` alone, taking
> no derivation about `f` as an argument.  So the `app` case is not a hard *use* of an
> induction hypothesis — there is nothing there to use.

Five applications of the criterion, and it has predicted before explaining every time after
the first:

| statement | induction sees a conversion? | conclusion | `trans` | outcome |
|---|---|---|---|---|
| `sort_inv` / `DefInv` clause (1) | yes | endpoint-asserted | fails | needs normalisation |
| `PropTypeAgree` (residual `PropConvInv`) | yes | propagated | closes | tractable |
| `PropUniq` | yes | endpoint-asserted | fails | needs normalisation |
| `SortForallEDisjoint` | **no** — induction on *typing* | — | never arises | tractable, 6 of 7 cases |
| shape-disjointness under substitution | yes | propagated | closes | does **not** inherit `SubstC`'s refutation |
| shape-***agreement*** under substitution | yes | propagated | closes | **FALSE** — `substShapeAgree_false` |

**Row 5 was under-specified and row 6 is the correction.** "Shape-disjointness under
substitution" names two different statements — a negation and an `iff` — and the criterion
separates them the wrong way round from what one wants: the `iff` is the one that composes at
`trans`, and the `iff` is **false**, refuted by the `SubstC` counterexample with no extra
construction.  The negation is true-as-far-as-known and does *not* compose.  §9 has the
detail; the general lesson is trap #10.

Route future statements through this before attempting them.

**And an irony worth stating, because the natural reasoning goes the other way.** The obvious
move is to attack these statements *unstratified*, since closing there would make the index
unnecessary. It is the wrong move: unstratified, the sort inversion these proofs need is
`HasTypeStrong.sort_type`, which *provably takes `SortUniq` as a hypothesis*, because this
tree's `IsDefEq` is type-indexed and composing conversions at two types **is** unique typing.
At the index, `HasTypeN.sort_inv` is free. So the setting that looks like the escape is the
one carrying the port's own defect, and the index — whose published metatheory is refuted in
§2 — is where this family of cases is cheap.


The model stream has re-parameterised and now imports one statement:

> `Γ ⊢ e : A`, `Γ ⊢ e : A'`, `A` a proposition ⟹ `A'` a proposition.

`sort_not_proof` is this at `e = .sort u`, so the two routes converged on it independently.
**It is strictly weaker than unique typing** (binary, not an equality) and it **passes the
cumulativity check** that refuted `SortUniq`.

**Row-zero, run: `trans` does *not* block it.** This is the finding that makes it worth
pursuing. Every case of `PropTypeAgree` reduces, via the inversion lemmas, to the residual

    PropConvInv : Γ ⊢ₙ A ≡ A'  ⟹  (IsProp A ↔ IsProp A')

and in that form `trans` **closes by composition** — `(ih1 d h).trans (ih2 d h)` — because the
property is *propagated along* the conversion rather than asserted of its endpoints. That is
exactly what `sort_inv`'s equality form is not, and it is why the arbitrary middle term that
blocks `sort_inv` is harmless here. `symm` likewise, given the `↔` form (the directed form
fails on `symm`, so state it as an iff).

Six of twelve conversion cases close, machine-checked in a scratch file:

* `rfl`, `symm`, `trans` — by composition;
* `sortDF` — retype the sort along the level equivalence;
* `lamDF` — **vacuous** given `DefInv` clause (3) (a λ's type is a Π, never `Prop`);
* the seven typing constructors die on `b = false`.

Open: `constDF`, `forallEDF`, `appDF`, `beta`, `eta`, `proofIrrel`, `extra`. Two things known
about these already:

* `forallEDF` is **not** vacuous — a Π *can* be a proposition (`imax u v ≈ 0` iff `v ≈ 0`,
  `VLevel.imax_eq_zero`), and the induction hypothesis is exactly about the codomain, which is
  what decides it. It resists on **context conversion** (`A::Γ` versus `A'::Γ`), the same
  thing that blocks `DefInv` clause (2)'s `symm` case.
* `beta` will meet the substitution index if attempted at the index; unstratified it should
  not.

### `PropUniq` — the model's *other* import, and it is on the wrong side

The model needs a second statement: **`PropUniq`** — `Γ ⊢ A : .sort u`, `Γ ⊢ A : .sort v`,
`u ≈ 0` ⟹ `v ≈ 0` (i.e. "`IsProp` is well-defined on types", where `PropTypeAgree` is
"`IsProof` is well-defined on terms"). Both are strictly weaker than `SortUniq`; that gain is
real. But they do not behave alike.

**Row-zero, run: `PropUniq` has `sort_inv`'s `trans` problem.** After shape inversion sends
both typings to the shape-determined type, its residual is
`.sort u ≡ₙ .sort v ⟹ (u ≈ 0 ↔ v ≈ 0)`. Machine-checked: `rfl`, `symm` and `sortDF` close, and
`trans` does **not** — `.sort u ≡ₙ X ≡ₙ .sort v` needs `X` to be a sort and nothing says it is.

The contrast with §5 is exact, and it is the same distinction:

| | conclusion | `trans` |
|---|---|---|
| `PropConvInv` (`PropTypeAgree`'s residual) | *propagated along* the conversion | closes: `(ih1 d h).trans (ih2 d h)` |
| `PropUniq`'s residual | *asserted of the endpoints* | fails: middle term need not be a sort |

So `PropUniq` needs normalisation, which puts it in the `SortUniq` family — and the
cumulativity check gives it no model route either. **Finishing `PropTypeAgree` does not
discharge the model.**

What `PropTypeAgree` *does* buy is on the syntactic side, and **both halves are now checked
rather than assumed**:

* `sortNotProof_of` and `forallENotProof_of` (landed, sorry-free, `Typing/UniqueTypingN.lean`):
  `PropTypeAgree` at `n` together with `DefInv` at `n` — both the induction hypothesis, so
  nothing is circular — give "a sort is not a proof" and "a Π-type is not a proof" at `n`.
  *(Note the second is not "a Π is not a proposition", which is false: `∀ x : α, β` is a
  proposition whenever `β` is. It says a term whose type is a Π does not also inhabit a
  proposition.)*
* With those, **`DefInv (n+1)` clause (1) closes in every case except `trans`** — machine-
  checked. `proofIrrel` closes outright.

So this removes **one** of the two obstacles in §4 and leaves the other standing alone:
`trans`/normalisation, and nothing else.

### The remaining cases, with what is known

**`forallEDF` resists on context conversion, and the target-preserving idea does not apply.**
The statement here is *already* target-preserving — same term `B'`, same target `.sort .zero`
— so the blocker is not an injectivity dependency but the index drop: context conversion for
the conversion half at `n+1` needs it for the typing half at `n`, while the context conversion
`A ≡ A'` is available only at `n+1`. Same family as the substitution gap. *Analysis, not
machine-checked.*

**`proofIrrel` is vacuous given the statement itself.** If `IsProp h` and `h : p : Prop`, then
`h`'s two types `p` and `.sort .zero` disagree on propositionhood, contradicting
`PropTypeAgree` at `h`. So it is not an obstruction to the *statement*, only a self-reference
in the *induction* — and the measure gives `≤`, not `<`, as at `DefInv.sort_proofIrrel`.
Attack it separately, not inside the induction. *Analysis.*

### Is `PropTypeAgree` closable at the index? — **No. One new primitive is needed.**

Settled, machine-checked. The three characterised cases are **two** obstructions, not one and
not three:

* **`forallEDF`** wants **context conversion at a preserved index**, and it is **not
  refuted** — the attempt is recorded below because where it resists is informative.

  *Diagnostic, machine-checked.* Context conversion at a preserved index closes for **every**
  rule except `appDF`, `beta`, `eta`, `proofIrrel` — the same four the substitution wall
  breaks at, and for the same reason (conclusion at `n+1`, typing premises at `n`, context
  conversion available only at `n+1`). Notably the `bvar` case, which looks like the obvious
  problem, closes cleanly: the fix-up conversion *is* the context conversion, weakened, and
  `Stratified.weak` preserves the index.

  *The conversion half is refutable*, by the same construction as §2a: in context `A'::Γ` the
  term `.app (.lam A (.bvar 0)) (.bvar 0)` is not `⊢₀`-typeable — its typing wants
  `.bvar 0 : A` at `⊢₀` while `Lookup` gives `A'` — so the `stuck` argument transfers and the
  `beta` conversion `.app (.lam A (.bvar 0)) (.bvar 0) ≡₁ .bvar 0` does not transport.
  ≈70 lines; not built, because it does not settle the question.

  *The typing half — which is what `forallEDF` actually needs — resists*, and for a specific
  reason: a typing's use of `bvar 0` at the wrong type is **repairable at index `n`** by
  `conv` along the context conversion itself. The index-`n−1` sub-derivations that break
  appear only *inside* conversions. So every counterexample that refutes the conversion half
  fails to lift to the typing half.

  **Status: the natural proof route for `forallEDF` is dead; the statement it needs is open.**
* **`proofIrrel` and `eta` look alike and are not.** `proofIrrel`'s residual is exactly
  `PropNotProof`, and `propNotProof_of` derives that *from `PropTypeAgree` itself* — the same
  statement at another subject, measure `≤` not `<`, so it is self-reference.  `eta`'s
  residual is exactly `SortForallEDisjoint`, and there is **no** such derivation: it is a
  separate weakening of unique typing, about a term's types being a sort versus a Π rather
  than about propositionhood.

**The primitive, named:**

    SortForallEDisjoint env U n :
      Γ ⊢ₙ e : .sort u  →  Γ ⊢ₙ e : .forallE A B  →  False

`PropTypeAgree.eta_case` and `PropTypeAgree.proofIrrel_case` (landed, sorry-free) show each
case closes from its residual and nothing else, so this is the precise obligation, not a
description of a gap.

It **passes the cumulativity check** — cumulativity retypes at sorts and never gives a Π-typed
term a sort type — so unlike `SortUniq` it is not excluded from a semantic argument in
principle. Whether the *model* can supply it is a separate question, since `Theory/SetModel/`
remains parameterised on `LevelAssign`.

**Unstratified is worse here, not better, and the reason is a port artifact.** The `sortDF`
case needs a typing inversion for sorts, and unstratified that is
`HasTypeStrong.sort_type` — which *provably takes `SortUniq` as a hypothesis*, because this
tree's `IsDefEq` is type-indexed and composing conversions at two types is `uniq`
(`Typing/SortUniq.lean` documents this). At the index, `HasTypeN.sort_inv` is free. **Work
this statement at the index.**

---

## 6. Traps that cost real time

1. **Arity.** `forallE_inv` names two unrelated families; a plain grep overcounts ~3.5×.
2. **Namespace.** `Lean4Lean.VEnv.Params` and `Lean4Lean.Params` are different classes. A
   claim about instantiation must carry its namespace.
3. **Case-pattern implicits.** `Stratified.bvar` has one more implicit than `IsDefEq.bvar`.
   Copying a case pattern between judgments requires counting implicits, not matching names.
   `induction ... with | ctor h1 h2` binds only explicit fields and IHs.
4. **Two head notions.** `VExpr.headConst?` peels λ; `VExpr.spineHead` does not.
5. **Index arithmetic.** `Stratified.instN` must be written `m + n`, never `n + m`.
6. **`rfl` is captured.** Inside these files `rfl` can elaborate to `Stratified.rfl`; write
   `(Eq.refl true)` when an equation is meant.
7. **`nomatch` needs constructors.** It cannot see through a `def`; `simp [thedef] at h`.
8. **A negative check licenses "not excluded", never "open".**  The cumulativity check shows
   `SortForallEDisjoint` is not *excluded* from semantic argument; it does not show a route
   exists.  **It cost a round.**  Writing "not excluded from a semantic argument in principle"
   was read as "a route exists"; the coordinator relayed the stronger reading and routed a
   model enquiry on it, and the model stream's first act was to correct the premise.  State
   what a negative check does not rule out, never what it opens.
9. **Reasoning about vacuity is unreliable.** Two cases in the `PropTypeAgree` pass were
   called vacuous by inspection and one was wrong (`forallEDF`). Run it.
10. **A statement that passes the criterion may pass it for free.** "The propagated iff
    `trans`-closes, machine-checked" was recorded for shape-disjointness and was *true* — of
    the version stated about a **conversion**, where it is not a theorem but a triviality
    (`SortLike` composes with `trans'`). The version that does the work is stated about a
    **substitution**, and it is false (`substShapeAgree_false`). Before recording a criterion
    pass, check the statement is the one the consumer needs *and* that the pass cost something.
11. **A "strengthening" can be the same statement.** The hereditary shape-disjointness is
    logically equivalent to `SortForallEDisjoint` (`SortForallEDisjointH.iff`), because a spine
    peeled off a type of `e` is a type of the applied term. Before funding a strengthening,
    prove it is one — or check whether the target's own rules already derive the extra clause.
    **Second instance, and it runs the other way**: adding a *hypothesis* can also leave the
    statement unchanged, when the hypothesis is free. Relativising `SortForallEDisjoint` to
    "each of the two types is itself a type at some universe" is *equivalent* to it in the
    unstratified judgment (`SortForallEDisjointSUniv.iff`), because `HasTypeStrong` carries
    regularity in every constructor. **Check both directions of "is this a different
    statement" — adding premises is not automatically weakening.**
12. **Free hypotheses hide in constructor premises.** `HasTypeStrong`'s rules each ship the
    typing of the type they conclude at, so `HasTypeStrong.regular` needs no `Ordered`, no
    `OnCtx` and no `CtxStrong` — while the neighbouring `IsDefEqStrong.isType'` needs all
    three. Before pricing a lemma as "needs regularity", read the constructor list.

---

## 7. What this route produced

The target has not moved, and the route produced more than it closed. Along the way:

* **a machine-checked defect in the published metatheory this project is built on** (§2a), and
  a second defect with a repair (§2b);
* **four candidate repairs closed by their own row-zero checks** (§3) — one of them by an
  arithmetic argument that closes a whole family without mentioning its shape, so the
  expensive machinery it would have needed was never the binding constraint;
* **a correction to the project's own model of the problem**: unique typing is used in §§3–4
  at three sites, not pervasively — and of those, `:180` is eliminated by the `K⁺` repair and
  `:266`/`:272` are discharged by `sortNotProof_of`/`forallENotProof_of`;
* **a diffuse obstruction reduced to two named statements**, each with its residual stated as
  an exact obligation rather than a description;
* **a criterion that predicts rather than explains** (§5), which reformulated itself on its
  third application in the direction of being more predictive, and has now decided five
  statements.

Build the unknown first. Every one of these came from running the check that was flagged as
unpriced, before building the thing it gated.

---

## 8. What is left after `PropTypeAgree`: `trans` alone

If `PropTypeAgree` lands, the residual of the whole route is one case. Framing for whoever
prices it — an option set, not a recommendation:

* **The criterion says `trans` cannot be dodged by reformulation.** Clause (1)'s conclusion is
  inherently asserted of its endpoints ("both are sorts, and their levels agree"), so no
  propagated-along restatement of it exists. It needs a *reduction relation* — something that
  says what the middle term does.
* **`unique.tex` §§3–4 (κ-reduction + Church–Rosser) — ~~is now materially cheaper than it
  looked~~ IS CLOSED AT THE INDEX. See §12; this bullet is superseded.** What it got right:
  §§3–4's *unique-typing* dependency really is only three sites, `:180` is eliminated by the
  `K⁺` repair (§2b), and `:266`/`:272` are what `sortNotProof_of`/`forallENotProof_of`
  discharge. What it missed is that unique typing was never the binding constraint:
  §§3–4 substitutes at a fixed index at three sites of its own, all three need `SubstT`, and
  `SubstT` is false. "Transcription plus one rule repair" is wrong.
* **A sorts-only normalisation is not a shortcut.** "A term convertible with a sort reduces to
  a sort" is not closed under its own induction: its `appDF` case needs the function's
  argument to reduce to a λ, dragging in Π-shape.
* **A different metatheory** (algorithmic conversion plus a logical relation). ~~breaks the
  typing/conversion circle without a reduction relation at all~~ — **that description was
  wrong twice, and the route is now priced out. See `docs/logrel-scope.md` (§13 below).** It
  does *not* avoid a reduction relation (every such development is built on weak-head
  reduction); it avoids *confluence*. And it is not outside what this repo has:
  `Experimental/LogRel.lean` is a genuine typed Kripke logical relation.

---

## 9. `SortForallEDisjoint`: where it stands

**Six of seven typing cases close from `DefInv` alone** (`sortForallEDisjoint_of`, sorry-free).
`trans` never arises — this is an induction on typing.  Only `app` is open.

**A refutation is provably impossible at the model's own witness.**  The six closed cases force
any counterexample to have an **application** subject.  The model's witness — `False` versus
`∀ x : False, B` — is a **constant**, and the `const` case is machine-checked.  So the model's
non-separation is real *and* cannot be lifted to syntax there.  The two facts are consistent
rather than in tension: the model genuinely does not separate them, the syntax genuinely does.

**`AppCase` is the whole remaining content of the statement — and read this before starting
it.**  Its first instinct will be that it inherits `SubstCRefute`'s refutation.  **It does
not, and not obviously so.**  What `SubstC` says, and what is refuted, is that *a conversion
survives substitution*.  What `AppCase` needs is only that *two shapes stay apart under it* —
a sort never becomes a Π.  Those are different claims and the second is much weaker: a
substituted term can fail to preserve a conversion while still never turning a sort into a Π.
The counterexample in `SubstCRefute` does not refute the disjointness form — both sides of it
are shape-inert — and the disjointness form **passes the criterion**: stated as a propagated
iff (`X ≡ₙ Y ⟹ (IsSortLike X ↔ IsSortLike Y) ∧ (IsPiLike X ↔ IsPiLike Y)`), `trans` closes by
composition, machine-checked.

*One detail that matters:* the formulation decides it.  Stated as `¬(sort(B[a]) ∧ Π(B'[a]))` —
the natural reading of "disjointness" — `trans` **fails**, because the middle term may be
neither.  Stated as the propagated iff, it closes.  Same content; only one passes.

*Read the paragraph above with one correction, because it was the trap.*  The propagated iff
that `trans`-closes is stated **about a conversion** — `X ≡ₙ Y ⟹ (SortLike X ↔ SortLike Y)` —
and in that form it is not merely tractable, it is **free**: `SortLike X := ∃u, Γ ⊢ₙ X ≡ .sort u`
composes with `X ≡ₙ Y` by `trans'`, no induction at all.  It is therefore no leverage.  The
statement that does the work is the one **about a substitution**, and that one is false.  See
below.

### The hereditary shape agreement, priced — both horns machine-checked

`Theory/Typing/ShapeSpine.lean` (new, sorry-free, `[propext, Quot.sound]`).  The primitive
proposed for `AppCase` was:

> the types of a term agree on shape, **and** their codomains agree on shape after
> instantiation at any argument typed at both domains.

It has two readings, and **both are closed**.

**(1) As disjointness — the usable reading — it is *equivalent to `SortForallEDisjoint`
itself*.**  `SortForallEDisjointH.iff`, machine-checked, and the joint-spine version the
sentence literally asks for (argument typed at *both* domains) collapses the same way
(`SortForallEDisjointH₂.iff`).  The collapse is one lemma:

    Apply.hasType :  Γ ⊢ₙ e : T  →  Apply Γ T args R  →  Γ ⊢ₙ e a₁ ⋯ aₖ : R

A spine peeled off a type of `e` is a type of the *applied term*, so quantifying over spines
quantifies over terms — which the unstrengthened statement already does.  The hereditary
clause is **derivable, not additional**.

And `AppCase` follows from `SortForallEDisjoint` in one line
(`SortForallEDisjoint.appCase`): `Stratified.app` already gives `.app f a` the type `B₀.inst a`,
and `conv` retypes it at the sort.  So **`AppCase` is the statement's own fixpoint**, and
nothing equivalent to the statement can close it.  *This is the finding to carry: the app case
is not a gap that a cleverer statement of the same strength will fill.*

**(2) As agreement — an `iff` of shape predicates, the reading that *would* be stronger — it
is FALSE.**  `typeShapeAgree_false`, at `n = 1` over the empty environment.  The witness is
`SubstCRefute`'s, lifted from a substituted conversion to *a term with two types*, which is the
hypothesis `SubstCRefute` explicitly declined to supply:

    A := .sort (succ p)     D := (fun _ : A => x) x     P := ∀ (_ : A), D      (P closed)

    [P] ⊢₁ .bvar 0 : P                     and    [P] ⊢₁ .bvar 0 : ∀ (_ : A), .bvar 0
                                                  (retyped by `forallEDF` of the beta step)

so the single term `.app (.bvar 0) a` has the two types `lhs` (stuck: `⊢₁`-related to nothing
but itself) and `a = .sort (max p p)` (a sort).  One is sort-shaped, the other is not.
`P` is a well-formed type (`P_type`), so the refutation does not turn on a junk context.

What it does **not** refute: `SortForallEDisjoint` (neither type is a Π), and `PropTypeAgree`
(`lhs` is typed at `.sort (succ p)`, not at `Prop`).  What dies is exactly the *agreement*
reading.  The same witness refutes the substitution form directly (`substShapeAgree_false`),
which is the §5 table's new row 6.

**The shape of the bind, stated once.**  The usable form is asserted of endpoints and does not
compose; the composable form is an `iff` and is false.  A transitive relation implying
disjointness would have to classify the stuck term: the witness forces it to relate `lhs` to a
sort, so transitivity forbids it from relating `lhs` to any Π — i.e. it has already decided the
target question at `lhs`.  That is §8's conclusion reached from a third direction: what is
missing is a **reduction relation**, something that says what the middle term does.

### What is left, named rather than described

    SubstDisj env U n :
      Γ ⊢ₙ a : A  →  A::Γ ⊢ₙ B ≡ B'  →
      Apply Γ (B.inst a) args R₁ → Apply Γ (B'.inst a) args R₂ →
      Γ ⊢ₙ R₁ ≡ .sort u  →  Γ ⊢ₙ R₂ ≡ .forallE C D  →  False

Not equivalent to `SortForallEDisjoint` (it is about two types with no common term, so
`Apply.hasType` does not collapse it), **satisfiable** (`SubstDisj.zero`, the base index, next
to `DefInv.zero`/`SubstC.zero`), and it buys one thing, machine-checked:

    applyDisj :  DefInv → SubstDisj → two spines off *one* type cannot end at a sort and a Π

— from `DefInv`'s clause (2) with **no induction on the spine**, which is what a `bvar` case
needs.  *But do not route `SubstDisj` as sufficient without pricing the `lam` case first.*
Analysis, not machine-checked: a spine induction on typing trades the open `app` case for two
others.  `app` closes (the IH applies at `f` with the spine extended by `a`); `bvar` reduces to
`applyDisj`; **`lam` does not close** — its two types are `.forallE A B` and `.forallE A B₂`
for two types `B, B₂` of the body, and bridging them under instantiation needs an existence
step (a spine on the middle) that only the refuted `∀∃` form provides.  Consistent with (1):
the difficulty moves, it does not shrink.

*On `docs/design-shape-lattice.md` and `Lean4Lean/Experimental/`, read as instructed.*  That
development is the same idea carried much further — a shape lattice with a logical relation —
and its recorded refutations are the same obstruction at a different altitude: `IsType.common`
false, and every relativisation of it (`Compat`-only, `LE_Interp`-relative, `TyDefEq`-relative)
refuted, each because *two compatible Π-shapes need not share a codomain sort when their
domains disagree*.  The one survivor there, `common_sort`, reads the sort off **the term's
universe** rather than off the shapes — the same shape of escape as "get the fact from the
accompanying term, not from the relation".  Nothing there is reusable as-is (it is unproved,
does not compile, and its `[ParamsExtra]` chain was vacuous twice), but that survivor is the
one idea in it that this route has not tried.  **It has now been tried; §11 closes it.**

---

## 10. Four independent convergences on one family

Recorded because whatever breaks this open will almost certainly be a single argument that
several consumers share:

1. the syntactic cone's `proofIrrel` case (`sort_not_proof`);
2. the set model's `LevelAssign.srt_sound` (`SortUniq` restated);
3. `PropTypeAgree`'s own `proofIrrel` case — self-reference at another subject;
4. the cut-down model, which bottoms out at `sort_not_proof` — i.e. at (3), from the opposite
   direction.

Impredicative formation forces the collapse the model cannot avoid; proof irrelevance forces
the identification.  Between them they close the semantic side for `SortUniq` and `PropUniq`
both.

---

## 11. The `common_sort` lead — closed, and the route now has no untried idea here

`docs/design-shape-lattice.md`'s one survivor was `LE_Interp.common_sort`, which escapes the
refutations that killed `IsType.common` and every relativisation of it by **reading the sort
off the term's universe** rather than off the shapes.  §9 flagged it as the one idea in that
development this route had not tried.  It has now been tried.  **It is dead, and the negative
is machine-checked in both judgments this repo has.**  `Typing/UnivDiscrim.lean`, sorry-free,
`[propext, Quot.sound]`.

### What `common_sort` actually does differently — get this before reusing the pattern

```
theorem LE_Interp.common_sort {ρ A U} {a a' : WShape n}
    (H : ∀ {b}, LE_Interp ρ b A → InterpTyped ρ b A (.sort U))
    (h : LE_Interp ρ a.T A) (h' : LE_Interp ρ a'.T A) (ha : a.IsType) (ha' : a'.IsType) :
    ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r)
```

Three parts, and all three matter:

1. **the datum is not computed from the two objects being compared.**  Nothing relates `a` to
   `a'`; `H` is applied to each separately.  It is supplied by a *third thing both are attached
   to* — the syntactic type `A`;
2. **it comes from a judgment one level up.**  The shared boolean is `decide (U ≠ .zero)`, a
   function of `A`'s own type `.sort U`, which the caller (`Adequacy:89`) holds as
   `IsDefEqStrong Γ A A' (.sort u)` — a type-indexed derivation that *ships with* its universe;
3. **the hypothesis is a uniformity** (`∀ b, …`) at a fixed `U`, so instantiating twice gives
   the same answer and there is no `∃`-common to construct.

`common_sort` is therefore a **coherence lemma between two layers**: it transports a fact that
is determinate on the *term* layer down to the *indeterminate shape* layer, at two shapes at
once.  That is the whole trick, and it is what the refutations miss — `cx_refutes` builds two
shapes with no term behind them, and `le_interp_common_fails` builds a common term under a
valuation with no well-formedness constraint.

### Why it does not transfer — two independent reasons

**(a) In a one-layer setting the lemma degenerates to its own hypothesis.**
`SortForallEDisjoint` has no shape layer.  The objects being compared (`B₀.inst a` and
`B₁.inst a`, the two types of `.app f a`) and the accompanying object (`.app f a`) are all
terms of the one syntax.  Written out there, `H` says "`A` is a type at universe `U`" — which
is `common_sort`'s own hypothesis, with nothing left over.  *In a single-layer setting
"consult the accompanying term" is "invoke the statement being proved"* — the same collapse
`Apply.hasType` produced for the hereditary form, reached from a different direction.
*Analysis.*

**(b) The datum is empty: a universe does not determine a type's shape.**  Grant the
level-`k+1` datum for free anyway.  Then, machine-checked:

> **`succ_eq_imax`** — for *every* `u`, `.succ u ≈ .imax (.succ u) (.succ u)`.  So the sort
> `.sort u` and the Π-type `∀ (_ : .sort u), .sort u` are types at **one and the same
> universe** `.succ u`.  `.sort u : .sort (.succ u)` and `.forallE A B : .sort (.imax p q)`;
> the ranges of `.succ` and `.imax` overlap, and `VLevel.imax_self` puts them on top of each
> other.

The disanalogy is exact.  In the shape model the datum read off the universe is the
`Prop`/`Type` boolean, which *is* the fact needed, and fixing `U` cuts the classifying shapes
down to one.  Here the fact needed is sort-shaped versus Π-shaped, and no universe carries it.

**And the negative is judgment-independent**, which is what makes it decisive rather than an
artifact of the index:

* `univ_premises_satisfiable` — at the stratified index, every premise of the universe-relative
  statement except "the two types have a common inhabitant" is simultaneously satisfiable, in
  any context, at any index `n+1`, over any environment.  The relativisation removes **no
  instance at all**;
* `HasTypeStrong.regular` — **regularity is free in the unstratified type-indexed judgment.**
  Every constructor already ships the typing of the type it concludes at, so the proof needs no
  `Ordered`, no `OnCtx`, no `CtxStrong` and no hypothesis of any kind.  (Contrast
  `IsDefEqStrong.isType'`, which needs all three.  Trap #12.)
* `SortForallEDisjointSUniv.iff` — consequently, in that judgment the universe-relative
  statement **is** the statement, one line each way.  Trap #11 in a new instance.
* `strong_univ_premises_satisfiable` — and the *shared*-universe version, the only variant that
  is genuinely weaker, has a premise that is consistent with a sort on one side and a Π on the
  other.  Free datum, and it still separates nothing.

### The variants checked and closed by the same fact

* *the universe of the application.*  In `AppCase`, `.app f a : .sort u` says the application
  *is* a type at universe `u`; on the other side it is a function and has no universe.  So `u`
  is one half of the disjunction being refuted, not an independent handle.
* *the codomain universes of `f`'s two Π-types.*  Suppose `Γ ⊢ B₀.inst a : .sort v₀` and
  `Γ ⊢ B₁.inst a : .sort v₁` were free — they are not; obtaining them substitutes into a typing
  derivation and meets `SubstC`'s index drop.  Then `v₀ ≈ .succ u` and `v₁ ≈ .imax p q`.  A
  contradiction needs `v₀ ≉ v₁`, which nothing supplies, and **even `v₀ ≈ v₁` is consistent**,
  by `succ_eq_imax`.  Dead twice over.

### Two things landed along the way

* **`SortForallEDisjoint` is satisfiable** (`SortForallEDisjoint.zero`, and
  `.AppCase.zero`), at the base index, for the same reason `DefInv.zero` and `SubstC.zero`
  hold: `≡₀` is equality, so `⊢₀` typing is syntactically unique (`HasTypeN.uniq_zero`).  The
  route funds this statement as a primitive and nothing had instantiated it.
* **The `app` case has no inductive content** (`appCase_ih_vacuous`) — see the companion test
  in §5.  This is a sharper diagnosis than "the fixpoint": the case does not fail because the
  IH is hard to use, it fails because the IH at `f` is vacuously true.

### What this leaves

Nothing here refutes `SortForallEDisjoint`; it is satisfiable and still open.  What is closed
is the hope of proving it by reading a discriminating datum off a universe — and with it the
last untried idea in this neighbourhood.  §8's conclusion now stands from a fourth direction:
what is missing is a **reduction relation**, something that says what a middle term does.

---

## 12. Does §§3–4 survive the substitution obstruction? — **No.**

§8 concluded that what is missing is a reduction relation, i.e. `unique.tex` §§3–4 restated
over `IsDefEqN`.  Before funding that, the row-zero was: §§3–4 takes the same substitution
step at `item:p_subst` (`:126`) and `item:gg_subst` (`:162`) — does it die there too?

**It does.  `Typing/SubstTRefute.lean` (new, sorry-free, `[propext, Quot.sound]`).**

### The sites need a *different* statement from the one already refuted — and it is false too

This is the thing to get right before quoting anything else.  `thm:utype`'s application case
needs `SubstC`: substitution into a **conversion** at a preserved index.  Neither §§3–4 site
does.  Both need

    SubstT env U n :
      Γ₀ ⊢ₙ e₀ : A₀ → Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → Γ₁ ⊢ₙ e : B → Γ ⊢ₙ e[e₀]ₖ : B[e₀]ₖ

— substitution into a **typing** at a preserved index — because what each has to reconstruct
is a `⊢ₙ` *typing premise*:

| site | the premise it must reconstruct | where it lives |
|---|---|---|
| `item:p_subst` (`:126`) | `≡ₚ`'s `proofIrrel` rule's three typings (and `refl`'s one) | `unique.tex:113`, `:118` |
| `item:gg_subst` (`:162`) | `K⁺`'s side condition `Γ ⊢ intro inv[p,h] : α` | `unique.tex:150` |
| **`thm:ckappa`'s β case** (`:251`) — *a third site, previously unrecorded* | `≡ᵏ`'s own side condition `Γ ⊢ e₁,e₂ : α` (`:240`) at the contractum `e[e'/x]` | `unique.tex:240` |

`SubstT` is genuinely weaker than `SubstC`, and the difference is real: a typing at `n` may
use `conv` at `n`, so the `⊢ₙ` typing of the substituted term is directly usable, which is
exactly what `SubstC` cannot do.  **`SubstCRefute`'s witness does not refute it** — there the
broken conversion is between two *uninhabited* types.

**`SubstT` is nevertheless false**, `substT_false`, at `n = 1` over the empty environment.
The move is one line of context: put `SubstCRefute`'s redex `C := (fun _ : A => #0) #0` in
the **context**.  Then `#0`'s `Lookup` type is `C.lift` and `hBB'` weakened retypes it as
`#1`, so `[C, A] ⊢₁ #0 : #1`; substituting `a` for the `A`-variable leaves `[lhs] ⊢₁ #0 : a`,
which `SubstCRefute.stuck` forbids.  `C` is a genuine type (`C_type`, at `⊢₀`), so the
context is well-formed.  *This is the hypothesis `SubstCRefute` declined to supply — a term
carrying both types — and a context variable supplies it for free, `Lookup` giving one and
`conv` the other.*

### The `j`/`k` answer, in §3's notation

At both sites **`j = k = n`**, and for a reason that is *stronger* than the one that closed
the repair family.  There, `j = k` came from `thm:utype`'s application case.  Here it comes
from §3's own convention (`unique.tex:64`): **the entire §§3–4 development has exactly one
typing judgment, `⊢ₙ`.**  There is no lower index to reach for — the substituted term's
typing arrives as `Γ ⊢ₙ e₂ : α` (`:162` supplies it explicitly; `:126` omits it, which is a
separate small gap since the proofIrrel case cannot be proved without it), and every premise
to be reconstructed is at `⊢ₙ`.  `Stratified.instN` lands at `j + k = 2n`.

Raising the index is not an option downstream either: `thm:1dinv` (`:266`, `:272`) consumes
the `≡ₚ` it gets by applying **unique typing at `n`**, and the outer induction (`:283`) has
unique typing only at `n`.  A `≡ₚ` at `2n` demands it at `2n`.

### The depth matters, and it is the depth the sites use

`substT_false` is at **depth 1** (`Ctx.InstN … 1 …`, i.e. under one binder).  At depth 0 the
statement is *not* refuted here and may well be true — the two arrangements that would refute
it either need a binder above the substituted variable (which forces depth ≥ 1) or a *closed*
context entry, and a closed conversion survives substitution.  That is not a loophole: both
`p_subst` and `gg_subst` recurse under λ (`unique.tex:114`, `:140`), so their inductions need
the general-depth statement, which is the one that is false.

*Checked, and worth knowing because it is the natural next guess:* subject reduction for β at
a preserved index is **not** refuted by this witness family.  The `ShapeSpine`-style
arrangement (`P := ∀(_:A), C` closed, in the context) re-derives the contractum's type
through a conversion the substitution cannot touch.  So the sites differ in how hard the
refutation bites, and one should not assume a single counterexample settles all three.

### Confidence, kept apart

* **Machine-checked:** `SubstT` is false at `n = 1`, depth 1 (`substT_false`).
* **Analysis:** each of the three sites' proof route runs through `SubstT` at depth ≥ 1 and
  has no alternative — the only two ways to obtain a `⊢ₙ` typing of a substituted term are
  substitution (refuted) and `conv` along a `⊢ₙ` conversion (`SubstC`, refuted).
* **Not established, and not claimed:** that `item:p_subst` and `item:gg_subst` are
  themselves *false*.  Refuting the route is not refuting the statement.  A refutation of
  `p_subst` looks constructible — two context variables whose common propositionhood holds
  only through the broken conversion, so `proofIrrel` cannot re-fire after substitution — but
  it needs `≡ₚ` defined at the index (9 constructors) plus a second `stuck`, a few hundred
  lines, and **it was not built**.  Until it is, the honest statement is *the reference's
  proof of §§3–4 does not go through at the index, by a machine-checked false lemma*, not
  *§§3–4 is false*.

### A third defect in the reference, found on the way

`thm:ckappa`'s **base case is false as stated** — `sorts_defEq1` and
`sorts_no_common_hasType0`, machine-checked.  `unique.tex:285` says that at `n = 0` both
`≡ᵏ` and `≡` "mean `e = e'`".  Under the §3 convention `≡` is `⊢ₙ₊₁ = ⊢₁`, and `⊢₁` is
strictly larger than syntactic equality (`sortDF` has no typing premise), while `⊢₀` typing
*is* syntactically unique — so `.sort (max p p)` and `.sort p` are `⊢₁`-convertible with **no
common `⊢₀` type**, and `≡ᵏ`'s side condition (`:240`) fails on them.  The outer induction
(`:283`) therefore has no base case, and `:252` uses `thm:ckappa` at `n` to get it at `n+1`,
so this is load-bearing.  Plausibly repairable by dropping "for some `α`" to two independent
typings — but that is exactly the side condition §3's (R2) arithmetic rests on, so the repair
must be re-priced rather than assumed.

### What this leaves

**The §§3–4 route is closed at the index.**  It is not "expensive transcription"; its two
substitution lemmas have no proof there, and a third site nobody had counted needs the same
thing.  §8's option list is down to its last entry: a different metatheory (algorithmic
conversion plus a logical relation), which breaks the typing/conversion circle without a
reduction relation, is outside anything `~/lean-type-theory` provides, and is large.  That is
a project-owner decision, not a stream decision.

### `ChurchRosser.lean`, re-measured (the old figures were stale)

2207 lines, **88 declarations** (not 85/86), **5 `sorry`s** (not 11) — all five in
`NormalEq.descend` (lines 1759, 1769, 1774, 1789, 1791).  The file **compiles**, with one
`declaration uses sorry` warning, and is in the default build via `Lean4Lean/Theory.lean` and
`HeadReduction.lean`.  **18 of 88** declarations import the uniqueness family directly
(`.uniq`/`.uniqU`/`IsDefEqU.sort_inv`/`IsDefEqU.forallE_inv`), 67 use-sites — not 23 of 85.
`IsDefEq.church_rosser`'s axiom cone is `[propext, sorryAx, Classical.choice, Quot.sound]`,
tainted from two independent sources: its own 5 sorries and the imported `IsDefEq.uniq`.
**Nothing instantiates `VEnv.Params`**, so all 88 declarations are vacuous as they stand, and
`Params` does *not* carry unique typing — that enters by import, per declaration.
Stale figures to correct if touched: `Injectivity.lean:183`, `RawDefEq.lean:26`,
`Stratified.lean:416`, `Experimental/ShapeLogRel.lean:1187`.

---

## 13. The logical-relation route — scoped and priced out (`docs/logrel-scope.md`)

§8's last remaining option was scoped. **Verdict: do not build.** The full document is
`docs/logrel-scope.md`; what a reader of *this* file needs is these five items.

**(a) Two corrections to how the option was described here.** A logical relation does **not**
avoid a reduction relation — it is built on weak-head reduction, and what it avoids is
Church–Rosser. So §8's conclusion ("what is missing is a reduction relation") is *satisfied*
by the route rather than bypassed. And it is not outside what the repo has:
`Experimental/LogRel.lean` (379 lines) is a textbook typed Kripke logical relation —
`Classifier` (a PER bundle), Kripke weakening, reducible substitutions, `fundamental` — and
`Experimental/ShapeLogRel.lean` is the coarsened version at **8435 lines**.

**(b) The decisive row-zero, machine-checked, and it is new.**
`Theory/Typing/LogRelRowZero.lean` (sorry-free, `[propext, Quot.sound]`): **`VEnv.WF` admits
an environment, one declaration step from empty, whose weak-head reduction has a two-cycle
between closed terms that are both well typed** (`exists_wf_env_headStep_cycle`,
`headStep_not_wf`). `VDecl.unsafeDef` typechecks its members in the environment already
carrying the block's constants, so two members naming each other install `f ≡ g` and
`g ≡ f`. Every open statement in `Injectivity.lean` is quantified over exactly that class.
**No normalisation argument of any kind can establish them as stated.** *Not claimed: that
the statements are false there.* Aiming a refutation of `sort_inv` at such an environment is
a cheap untried thread.

> **Superseded in part — read §14 before using this paragraph.** The thread was pulled.
> `sort_inv` is **not** refutable there (§14.1), and more importantly the bolded sentence is
> **wrong at this witness**: `loopEnv`'s two members are proofs of one proposition, so
> `proofIrrel` already identifies them and the two rules add *nothing* to the conversion
> relation. `Theory/Typing/CycleConv.lean` machine-checks that `loopEnv.IsDefEq` **is**
> `loopEnv2.IsDefEq`, where `loopEnv2` has no rule at all and is `VEnv.WF` by two `.axiom`
> steps. `headStep_not_wf` stands; what it is evidence *for* does not. A witness that
> survives the collapse — `propLoopEnv` — is in the same file.

The repair — restrict to `VEnv.LeanWF` — is already done on the *model* side
(`Verify/Bridge.lean:236`) and **not** on the algorithm side: `VContext` carries an arbitrary
`DefinitionSafety`, and `TrProj.uniq` / `TrProj.defeqDFC` / `TrProj.weak'_inv` /
`reduceRecursor.WF` all run there. That mismatch is a prerequisite for *any* normalisation
route and is owned by the `Verify/` stream.

**(c) The two feared assumptions do not bite — and this reverses §10.** Machine-checked
(`imax_measure`, `imax_domain_unbounded`): where a Π-type is **not** a proposition the
hierarchy is predicative and both component levels are bounded by its own; where it **is**,
the domain's level is unbounded — and that is exactly the case where proof irrelevance makes
recursion unnecessary. **Impredicativity is confined to precisely the case proof irrelevance
trivialises.** §10's two facts point the other way here. Trap #8 applies: this licenses "not
excluded", not "open", and it does not move the verdict. It also forces a design fact: the
relation must be a family indexed by a *level valuation*, since `VLevel.imax u v` is `0` at
some valuations and `max u v` at others.

**(d) Nothing in this tree becomes wrong under the route** — it adds no rule to any judgment.
`Strong.lean`, `DeclRules.lean` and the `Pattern*`/`DeltaUnique` cone (~6500 lines) carry
over; the stratified cone (`Stratified`, `UniqueTypingN`, both refutation files,
`ShapeSpine`, `UnivDiscrim` — ~2550 lines) goes **dead but stays true**. Contrast candidate 1
of `options-circularity-breakers.md`, which made `SubstCRefute` false.

**(e) There is no cheaper sub-target, and `PropUniq` + `PropTypeAgree` is not one.** The
whole injectivity family comes from a single lemma — `LRIsType.irrel` ("the relation at a
type is unique"), which is *already proved sorry-free* in `Experimental/LogRel.lean:157`,
from determinism of weak-head reduction. So the route delivers everything at once and no
part of it separately. And two apparent escapes from the model's two imports are closed: a
**derivation-directed** interpretation relocates `PropUniq` to a coherence obligation which
**is `PropUniq`** (`HasTypeStrong.lam` picks a codomain sort; two derivations may pick
different ones — trap #11 again), and a **type-directed** one removes `PropSplit` but *is* a
logical relation.

---

## 14. The environment class — the cycle is a reduction fact, not a conversion fact

**This section corrects §13(b) and `docs/logrel-scope.md` §1 at their own witness.** New
machine-checked file: `Theory/Typing/CycleConv.lean` (sorry-free, `[propext, Quot.sound]`).

### 14.1 The refutation attempt — `sort_inv` was **not** refuted

§13(b) named "aiming a refutation of `sort_inv` at a `.unsafeDef` environment" as the cheap
untried thread. It was tried. **`sort_inv` survives**, and so does the rest of the family;
the reason is structural rather than a failure of ingenuity, and it is worth writing down so
nobody re-runs it.

To make `.sort u ≡ .sort v` with `u ≉ v` the derivation must, somewhere, take a step whose
two endpoints are a sort and a non-sort. Only three rules can:

* **`extra`** — excluded outright in *every* `VEnv.WF` environment by
  `WF.instL_lhs_ne_sort` (`DeclRules.lean:253`): every rule's lhs is a `.const`, an `.app`
  or a `.lam`. `.unsafeDef` changes nothing here — its rules are δ-rules like any other, and
  `WF'.defeq_isDeclRule` covers the `unsafeDef` case explicitly.
* **`beta` / `eta` / congruence** — these do relate a sort to a non-sort (a sort is
  β-equal to a redex), but composing two of them back down to a sort re-imposes the
  original obligation: `appDF`+`lamDF` on `(λA. .sort u) e ≡ (λA. .sort v) e'` reduces to
  `.sort u ≡ .sort v`. A **discriminating** function — one sending two convertible arguments
  to different sorts — would break this, and needs an ι-rule firing on two *different*
  constructors that are nevertheless convertible. That needs large elimination from a
  non-subsingleton `Prop`, which `VInductDecl'.WF.isLE` / `LECond`
  (`Theory/Inductive/Decl.lean:447,467`) forbids. A δ-rule cannot discriminate: its rhs is
  one term, so `F a` and `F b` differ only where the bound variable occurs, and congruence
  already equates them when `a ≡ b`.
* **`proofIrrel`** — needs a sort to be a **proof**: `Γ ⊢ p : .sort .zero` and
  `Γ ⊢ .sort u : p`. Every route to that needs `.sort (u+1) ≡ p` at a common type, i.e. a
  sort–non-sort conversion at a proposition — the thing being constructed. `unsafeDef`
  does not open it either: a member's *value* is checked in `env.addConsts cis`, which
  carries the block's constants but **not its defeqs** (`VDecl.WF.unsafeDef`), so no member
  can be typed using the block's own equations, and a member declared at `.sort .zero`
  needs its value to be a proposition.

So the mechanism is a fixpoint: refuting `sort_inv` requires `sort_inv` to already fail. It
cannot be entered from `VEnv.empty`. *Confidence: this paragraph is analysis, not a Lean
proof — the two facts it leans on (`instL_lhs_ne_sort`, `LECond`) are machine-checked, the
case enumeration is not.* **Reported the other way, as §13(b) asked: `sort_inv` survives
refutation at a cycling environment.**

### 14.2 …and the cycling witness turns out not to be a cycling witness — machine-checked

The stronger result came out of the attempt. `LogRelRowZero.lean`'s `loopEnv` declares
`f, g : ∀ p : Prop, p` with `f := g`, `g := f`. Both members are **proofs of one
proposition**, and `IsDefEq.proofIrrel` identifies any two proofs of a proposition *with no
rule in the environment at all*. Hence, in `CycleConv.lean`:

| name | content |
|---|---|
| `loop_defeq_without_rules` | `f ≡ g` already holds in `loopEnv2` — `loopEnv` minus both rules |
| `loop_conv_iff`, `loopEnv_conv_iff` | `loopEnv.IsDefEq` **is** `loopEnv2.IsDefEq`; likewise `IsDefEqU` |
| `loopEnv2_no_defeqs` | `loopEnv2` has **no** definitional-equality rule, so no `HeadStep.delta` |
| `loopEnv2_wf_noUnsafe` | and it is `VEnv.WF` by two `.axiom` steps, `∀ d ∈ ds, d.noUnsafe` |
| `sort_inv_transfer` | so `sort_inv` at `loopEnv` **is** `sort_inv` at that cycle-free, `noUnsafe` environment — and the same one-line transfer works for each of the six |

**What this does and does not overturn.** `headStep_not_wf` stays true: the reduction really
does cycle. What does not follow — and what §13(b) and `logrel-scope.md` §1 assert — is that
*the statements* are out of reach there. At that witness they are exactly the statements at
an axiom-only environment. The witness is evidence about reduction and no evidence about the
targets. `logrel-scope.md`'s verdict on the logical-relation route does not depend on this
(its §§3–4 stand on their own); the sentence that needs withdrawing is "so a logical relation
cannot deliver them **as stated**".

**A witness that does survive the collapse** is in the same file: `propLoopEnv`, the same
one-step-from-empty block with the members declared at `.sort .zero` — `A : Prop := B`,
`B : Prop := A`. Now the members are *propositions*, not proofs, and the collapse recipe
would need `Γ ⊢ .sort .zero : .sort .zero`, a sort that is a proof
(`propLoop_no_direct_collapse`, from `SortUniq`). `propLoop_headStep_not_wf` is the cycle.
*Not proved: that its `A ≡ B` is a genuinely new conversion — only that this collapse
argument does not reach it (trap #8).* **Anyone restating the row-zero check should restate
it at `propLoopEnv`.**

### 14.3 The weakest hypothesis that excludes the cycle — and it is already in the tree

Not `VEnv.LeanWF`: that also bans `.axiom` steps, which the kernel must accept. The right
predicate is the one `Theory/Typing/Env.lean` already defines and `Verify/` already proves:

```lean
∃ ds, VEnv.WF' ds env ∧ ∀ d ∈ ds, d.noUnsafe        -- VDecl.noUnsafe
```

`.unsafeDef` is the **only** `VDecl` former that can install a rule whose rhs mentions the
block's own constants, so it is the only source of a δ-cycle; `.def` checks its value before
the constant exists, `.induct`/`.quot` install structural rules, `.axiom` installs none. And
`TrEnv'.wf_noUnsafe` (`Verify/Environment/Basic.lean:419`) delivers exactly this.

### 14.4 Does the obstruction disappear under it? — **No**, and this is the finding

`loopEnv2` is `noUnsafe`, has no rules at all, and the six statements there are *the same
statements*. More basically: `sort_inv`'s two open cases are `trans` and `proofIrrel`, and
neither is an environment fact.

* `trans`'s middle term is arbitrary in any environment.
* `proofIrrel` bites where propositions are inhabited, and `sort_inv`'s hypotheses supply
  that **over the empty environment, from the context alone** — `empty_ctx_inconsistent`
  (`CycleConv.lean`): `OnCtx [falseProp] (VEnv.empty.IsType 0)` holds and `.bvar 0`
  inhabits `∀ p : Prop, p`. No environment restriction can remove it.

What `noUnsafe` buys is δ-termination — a **precondition for one proof technique**
(normalisation), not a weakening of the goal. That is a real gain and the right cut to make
if a normalisation route is ever attempted. It is not a restatement that makes anything
provable by itself, and it should not be sold as one.

### 14.5 Do the consumers survive? — **the `Theory/` side yes, the `Verify/` side no**

Cone scan (transitive, arity-checked, not a grep). Only two files import `Injectivity.lean`:
`UniqueTyping.lean` and `ConstInvWitness.lean`; **`Theory/SetModel/` is not in the cone at
all** — its references are prose. 32 direct sites in 14 declarations.

* **`const_app_inv`, `const_forallE_inv`, `const_sort_inv` have zero call sites in the whole
  tree.** Their named consumers are themselves `sorry` (`TrProj.{uniq,defeqDFC,weak'_inv}`
  `Verify/Typing/Lemmas.lean:693,708,1374`; `quotReduceRec.WF` `Verify/TypeChecker/WHNF.lean:63`
  — note `reduceRecursor.WF` at `:66` is *proved*, the blocked one is `quotReduceRec.WF`),
  documentary (`SetModel/IndInterp.lean:536`, whose "not stated anywhere" row for
  `const_sort_inv` is now stale), or **nonexistent**: `pat_major_not_pi` is not a declaration
  anywhere, only a planned field named in `Theory/Inductive/Lemmas.lean:150`.
* **`sort_inv` + `forallE_inv_stratified` are the load-bearing pair**, and they reach
  `Verify/` through a single gateway: `IsDefEq.uniq` (`UniqueTyping.lean:13`), whence the
  ~28-member `UniqueTyping` family and ~230 uses across `Verify/`.
* `forallE_inv` and `sort_forallE_inv`'s remaining consumers (`ChurchRosser.lean`,
  `HeadReduction.lean`) sit inside `class Params`, which **has no instance in the tree**, so
  they are already vacuous for an independent reason.

**The blocker.** Every `Theory/` consumer takes `henv : VEnv.WF env` (or `Params.henv`) and
would absorb a stronger hypothesis for free. Every `Verify/` consumer does not:

| site | how it gets the environment |
|---|---|
| `inferApp.loop.WF` (`Verify/TypeChecker/InferType.lean:250`, uses at `:271,276,286`) | `c.Ewf`, from `VContext` |
| `inferType.WF_uniq` (`Verify/TypeChecker/Basic.lean:885`, use at `:889`) | `c.Ewf`, from `VContext` |
| `TrExpr.beta` (`Verify/Typing/Lemmas.lean:2571`, use at `:2586`) | explicit `henv`, supplied by callers from `VContext` |

`VContext` (`Verify/TypeChecker/Basic.lean:190`) carries `safety : DefinitionSafety`
**unconstrained**, and `VContext.Ewf` is `c.trenv.wf`, which holds at every safety level.
`TrEnv'.wf_noUnsafe` requires `safety = .safe` **as a literal** — its `unsafeDef` case is
discharged by `TrDefBlock.safe_not_unsafeDef`, stated only at `.safe`. And non-`.safe` is not
hypothetical: `Environment.lean:78–80` **rejects** a `.safe` mutual block, so `addMutual`
always runs at `.partial`/`.unsafe`, and `addAxiom`/`addDefinition` run at `.unsafe` for
unsafe declarations.

**So a `noUnsafe`-restricted `Injectivity.lean` does not serve its own consumers**, and that
is as important as the restatement. `Verify/TypeChecker/Reduce.lean:4–33` is already an
entire module about why `VContext`'s safety "cannot be dodged".

### 14.6 What would have to change, and what would become false

*Statements* (all in `Injectivity.lean`): `henv : VEnv.WF env` → the `noUnsafe` predicate,
in all seven.

*Consumers, `Theory/`* — mechanical hypothesis strengthening, nothing becomes false:
`IsDefEq.uniq` and the ~28-member `UniqueTyping` family; `WF.sortUniq`
(`SortUniqFacts.lean:20`); `ChurchRosser.Params.henv` and `HeadReduction`'s uses (vacuous
today); `absurd_of_prop_eq_propArrow` (`ConstInvWitness.lean:138`).

*Consumers, `Verify/`* — **owned by that stream, named here, not changed here.** Either
(a) `VContext` gains a `noUnsafe` field, which forces `c.safety = .safe` and therefore
splits `inferType.WF` into a `.safe` arm carrying the model obligation and a non-`.safe` arm
carrying only termination/no-crash; or (b) the `VEnvs` family (`Verify/TypeChecker.lean:10`,
`venv : DefinitionSafety → VEnv`) is used to route the injectivity obligation through the
`.safe` model only. `addDecl.WF` (`Verify/Environment.lean:235`) already quantifies over all
safety levels, so (a) is a real refactor and its size is unmeasured. Note the shape of the
opportunity: `kernel_sound` needs only the `.safe` model
(`Verify/Bridge.lean:236,249`), and a `partial` block contributes nothing to it, so the
correctness of *its* check may not need to be sound at all — only total.

**Nothing already proved becomes restatable-but-false.** Strengthening a hypothesis cannot
falsify a proved theorem, and the check that matters — are the counterexample witnesses still
in the smaller class? — passes: `ConstInvWitness.lean`'s `w1`/`w2` need a δ-rule and two
axioms, installable by `.def` and `.axiom` steps, both `noUnsafe`; `SubstCRefute` and
`SubstTRefute` are over `VEnv.empty`. The one thing that *does* go vacuous is any statement
whose only witness is `loopEnv` — and by §14.2 that witness was never doing the work
attributed to it.
