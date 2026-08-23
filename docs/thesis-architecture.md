# The thesis's architecture, read end to end

**Scope.** `~/lean-type-theory` read in full: `main.tex`, `axioms.tex`, `typesys.tex`,
`unique.tex`, `Wtypes.tex`, `soundness.tex`, `normalization.tex`, `compilation.tex`.
Cross-checked against `Theory/SetModel/`, `Theory/Typing/Stratified.lean`,
`Theory/Typing/UniqueTypingN.lean`, `Theory/Typing/Injectivity.lean`,
`Verify/Soundness.lean`.

---

## 0. The answer, first

**Does the joint induction give a route our sequential plan cannot have?**

*Partly — one specific thing, and it is the thing four separate lines of attack said was
missing.* The semantic half dissolves the `trans` obstruction: an arbitrary middle term has
a denotation, so an endpoint-asserted conclusion (`sort_inv`) becomes propagated-along in
the semantic domain. That is exactly what `docs/handoff-stratified.md` §5's criterion says
no syntactic reformulation can do, and what §8/§9/§11 reached from four directions as "what
is missing is a reduction relation". The model supplies it without a reduction relation.

**Do our three refutations block it?**

| defect | does the joint induction need it? |
|---|---|
| (a) `SubstC` false | **Yes. It survives, and it is the single blocker.** The induction must produce level-uniqueness at index `n+1` before it can build the model at `n+1`, and the only route to that is `thm:utype`, whose application case is the refuted inference. The semantic side cannot supply it: the model returns equality of *denotations*, and level-uniqueness at `n+1` needs it of terms whose interpretation is not yet defined. |
| (b) `SubstT` false | **No. Routed around completely.** `SubstT` is consumed only by `unique.tex` §§3–4 (κ-reduction, Church–Rosser, `thm:ckappa`). The joint induction replaces §§3–4 as the source of definitional inversion. Nothing in `soundness.tex` uses reduction, confluence, or `≡ₖ`. |
| (c) `thm:ckappa`'s base case false | **The theorem is not needed; the underlying fact is, in a new place.** `thm:ckappa` itself is dead with §§3–4. But what `sorts_no_common_hasType0` machine-checks — that a `⊢₁` conversion's endpoints need not share a `⊢₀` type — is the same fact that blocks the model route's prerequisite: **the stratified conversion judgment carries no typings, and the interpretation needs them.** So (c) does not kill the route, but it names its first unpaid obligation. |

**Net.** The joint induction converts a four-way-confirmed dead end (`trans` needs
normalisation) into a one-way dead end (`SubstC`). That is progress in diagnosis, not a
plan. **It does not close the reference as a source of a plan; it relocates the whole
project's blocker onto a single machine-checked-false lemma, and removes every other
consumer of the refutations.** Whether that is worth funding turns on one question that is
*not* settled here: is there any route to level-uniqueness at a preserved index other than
`thm:utype`? See §8.

**And a caution that dominates everything below.** The joint induction is *four sentences of
architecture and one theorem statement*. The proof runs to `\begin{proof}`, does the `n = 0`
case, writes "Now suppose the induction hypothesis holds for `n`. From (1), if `Γ ⊢ e:`" —
and **stops mid-sentence**, followed by the literal word `UNFINISHED` (`soundness.tex:384–387`).
Not one case of the inductive step exists. Everything in §§4–8 below is my reconstruction of
what it would have to be, not a reading of a proof.

---

## 1. Where the joint induction actually sits — and it is not the thesis's architecture for Lean

This corrects the premise of the task as posed. The quoted passage (`soundness.tex:368`) is
inside `\subsection{Equality reflection}`, whose first sentence is:

> "In this section, we seek to extend the proof of \autoref{thm:sound2} to Lean **with
> equality reflection**."

Equality reflection is the rule `Γ ⊢ h : e = e' ⟹ Γ ⊢ e ≡ e'`. `soundness.tex:364` states
plainly that Lean is *intensional* and does **not** have it. So:

* For **Lean as it is**, the thesis's architecture is strictly sequential, and the chapter
  order in `main.tex:112–119` is the dependency order:
  `axioms → typesys → unique → Wtypes → soundness → normalization → compilation`.
  `unique.tex` proves `thm:unique` standing alone (via `⊢ₙ`, `thm:utype`, κ-reduction,
  Church–Rosser, `thm:ckappa`, `thm:1dinv`); `soundness.tex` *consumes* it.
* The joint induction is an **add-on for a theory Lean is not**, and — decisively — **its own
  base case cites the sequential result.** `soundness.tex:382`: at `n = 0` the conversion
  rule does not apply, "so the equality reflection rule does not apply and hence we can use
  \autoref{thm:sound2} directly". `thm:sound2` is the sequential soundness theorem, which
  presupposes `thm:unique` for the reflection-free theory. **The joint induction does not
  replace unique typing; it re-derives it above a base case that imports it.**

So "follow the reference" cannot mean "adopt the joint induction". If one adopts the joint
induction's *mechanism* while keeping Lean's rule set, one is doing something the thesis does
not do and never wrote down.

## 2. How unique typing enters the model — precisely, and it matches our tree

The soundness development has exactly **one** consumer of unique typing, and it is not inside
the model.

1. `soundness.tex:34–50` — the `lvl` and `sort` functions. `lvl_v(Γ ⊢ α)` is the level of a
   type; `sort_v(Γ ⊢ e) = lvl_v(Γ ⊢ α)` for any type `α` of `e`. Both are *well-defined only
   because of unique typing* (that is the whole proof of the lemma).
2. `soundness.tex:51–68` — the proof-split translation `⟨·⟩_Γ`. Three of its five clauses
   case-split on `sort`/`lvl`:
   * `⟨e₁ e₂⟩` → proof-application `e₁ e₂` if `sort(Γ⊢e₁) = 0`, else type-application `e₁·e₂`;
   * `⟨λx:α.e⟩` → proof-λ if `sort(Γ⊢e) = 0`, else type-Λ;
   * `⟨∀x:α.β⟩` → `∀` if `lvl(Γ⊢β) = 0`, else `Π`.
3. `soundness.tex:127–189` — the interpretation `⟦Γ ⊢ e⟧_γ` is a recursion **on the split
   language**, by a size measure on terms (`:129–136`). It never consults a derivation and
   never mentions `lvl`. Proof-λ and proof-application go to `•`; type-Λ and type-application
   go to real ZFC functions and applications.

**So the interpretation is derivation-free and index-free; only the translation is not.**
This is exactly our tree's shape: `SetModel/InterpSubst.lean`'s docstring — "The context
enters the interpretation in only two ways — `Γ.length`, and the three proof-splitting
decisions". `PropSplit` is `lvl`/`sort` weakened to its Boolean shadow, and
`SetModel/PropSplitAudit.lean` §3 shows `PropSplit` is satisfiable exactly from `PropUniq` +
`PropTypeAgree`. **Our model stream has independently reconstructed the thesis's dependency
and weakened it; nothing in `soundness.tex` asks for more.**

One consequence worth stating because it corrects a natural reading of `handoff` §3's "the
model is *parameterised* on `SortUniq`": that was true of `LevelAssign` and is no longer the
statement. The thesis's own requirement is `lvl`/`sort`, i.e. `LevelAssign`; our tree is now
strictly below it.

Two further sequential dependencies in the same chapter, both easy to miss:

* `soundness.tex:114` — unique typing **for the split language** is obtained *from* the
  reverse translation `e ↦ ē` plus unique typing for the original language. Not independently.
* `soundness.tex:290` — the compatibility case of the conversion half: "When a case split on
  `⟦ℓ⟧ = 0` is done, **by unique typing** it must be the same for both sides." This is the
  translation's well-definedness again, at a conversion rather than a term.

## 3. What the joint induction is, as stated

`soundness.tex:372–380`. For all `n ∈ ℕ`:

1. If `⟦Γ⟧ ≠ ∅` and `Γ ⊢ₙ 𝒰_ℓ ≡ 𝒰_ℓ'`, then `ℓ ≡ ℓ'`.
2. If `⟦Γ⟧ ≠ ∅` and `Γ ⊢ₙ e : α, α'`, then `ℓ ≡ ℓ'`.
3. If `Γ ⊢ₙ e : α`, then ∃`k`: for a `k`-correct `κ`-sequence, ∀`γ ∈ ⟦Γ⟧`, `⟦e⟧_γ ∈ ⟦α⟧_γ`.
4. If `Γ ⊢ₙ e ≡ e'`, then ∃`k`: for a `k`-correct `κ`-sequence, ∀`γ ∈ ⟦Γ⟧`, `⟦e⟧_γ = ⟦e'⟧_γ`.

Three textual observations, all load-bearing:

* **(2) is malformed.** `ℓ` and `ℓ'` are not bound by its hypothesis. Two readings:
  (2a) the conclusion is `Γ ⊢ₙ α ≡ α'` — full unique typing, the statement `thm:utype` proves;
  (2b) the hypothesis is `α : 𝒰_ℓ`, `α' : 𝒰_ℓ'` and the conclusion `ℓ ≡ ℓ'` — *level*
  uniqueness, i.e. exactly what `lvl`/`sort` need and no more. **(2b) is the better reading**:
  the conclusion is copied verbatim from (1), the surrounding text says the joint induction
  exists because unique typing "underlies the `lvl` function", and `lvl` needs only (2b).
  I analyse (2b) below and note where (2a) changes things.
* **(1) and (2) carry `⟦Γ⟧ ≠ ∅` and (3),(4) do not.** The unique-typing half is only claimed
  in *semantically inhabited* contexts. That is not a technicality (see §6).
* **(3) and (4) are written with the untagged `⟦·⟩` of `thm:sound`, not the tagged `⦇⟦·⟧⦈`
  of `thm:sound2`** — even though the text one paragraph earlier says it is extending
  `thm:sound2`. For (1) that is harmless (see §4); for anything about Π-types it is not.

## 4. What the semantic half supplies that a standalone proof cannot — the real leverage

This is the question worth the whole document, and there *is* a real answer.

**Sort injectivity falls out of the model, with no reduction relation.**
`Γ ⊢ₙ 𝒰_ℓ ≡ 𝒰_ℓ'`; apply (4); `⟦𝒰_ℓ⟧_γ = U_{⟦ℓ⟧v}` and universes are a strict membership
hierarchy (`soundness.tex:123`, `:236`), so `U_a = U_b ⟹ a = b`, so `⟦ℓ⟧v = ⟦ℓ'⟧v` for every
valuation `v`, hence `ℓ ≡ ℓ'`. **Tags are not even needed for this one.**

Why this is not available syntactically, in the project's own vocabulary: `handoff` §5's
criterion says `sort_inv`'s conclusion is *asserted of its endpoints*, so `trans` fails —
`𝒰_ℓ ≡ X ≡ 𝒰_ℓ'` with nothing saying `X` is a sort. **In the model `X` has a denotation.**
`⟦𝒰_ℓ⟧ = ⟦X⟧ = ⟦𝒰_ℓ'⟧` composes by transitivity of `=`. The endpoint-asserted statement is
propagated-along *in the semantic domain*. This is precisely the "something that says what
the middle term does" that `handoff` §8, §9 and §11 each concluded was missing — supplied
without confluence, without `≡ₖ`, without `SubstT`.

**Sort/Π disjointness likewise, but only with tags.** DefInv clause (3), `𝒰_ℓ ≢ ∀x:α.β`, needs
`⟦𝒰_ℓ⟧ ≠ ⟦∀x:α.β⟧`. Untagged this fails (both can be `∅`-adjacent; and in the split language
`∀` is `{•} ∩ ⋂…`). Tagged (`soundness.tex:342–343`) `⟦𝒰_n⟧ = (𝒰,n)` and `⟦Πx:α.β⟧ = (Π,A,B)`
are distinct tuples, so clause (3) is free. **Note this is a different statement from
`SortForallEDisjoint`** (§6).

**And the corresponding consumer already exists in this tree.** `IsDefEqU.sort_inv_of_defInv`
and `sort_forallE_inv_of_defInv` (`Typing/UniqueTypingN.lean`) reduce the actual target to
`∀ n, DefInv`, using neither `uniq` nor `SubstC`; `IsDefEq.stratifyN` supplies the index.
So the wiring from "DefInv at every `n`" to `Injectivity.lean`'s targets is done.

**What the model cannot supply: DefInv clause (2).** Π-injectivity demands the *syntactic*
judgments `Γ ⊢ₙ α ≡ α'` and `α::Γ ⊢ₙ β ≡ β'`. Tags give `⟦α⟧ = ⟦α'⟧` — equality of ZFC sets.
There is no route back from a denotation to a derivation. **Clause (2) is permanently outside
what any model of this kind can return**, and that is a structural fact, not a gap in the
write-up. (Under reading (2b) clause (2) may not be needed in full; see §8.)

## 5. Running the induction — where `SubstC` comes back

The stage-`n+1` obligations must be discharged in an order, and the order is forced.

* **(4) at `n+1` first.** A `⊢ₙ₊₁` conversion's typing premises are `⊢ₙ` (`unique.tex:13`),
  so the terms it relates are interpretable by the *stage-`n`* model. This is the step that
  makes the whole idea look like it might work.
* **(1) and clause (3) at `n+1`** follow from (4) at `n+1`, as in §4. **Free.**
* **(2) at `n+1`** — here it stops. `e` has two `⊢ₙ₊₁` types. The model at `n+1` is not built
  yet (it needs `lvl` at `n+1`, which is (2) at `n+1`), so the semantic side is unavailable
  *by construction of the induction*. The only syntactic route is `thm:utype` at `n+1`, and
  using this tree's shape-inversion lemmas (`HasTypeN.{bvar,sort,const,app,lam,forallE}_inv`)
  every constructor case closes by `trans` on a *common* shape-determined type — **except
  `app`**, where the two shape-types are `B.inst a` and `B'.inst a` and bridging them is
  `unique.tex:51`, i.e. `SubstC`, i.e. `SubstCRefute.substC_false`.
* **(3) at `n+1`** needs (2) at `n+1`. Blocked behind it.

**So `SubstC` is not routed around. It is isolated.** Every other consumer of every other
refutation drops out: §§3–4 is not used, so `SubstT` is not used; `thm:ckappa` is not used,
so its base case is not used; Church–Rosser is not used; `normalization.tex` is not used.
The joint induction reduces the project's whole obstruction to one lemma — and that lemma is
machine-checked false at `n = 1` over the empty environment.

Two smaller things the reconstruction turns up, both new:

* **A prerequisite nobody has stated: soundness for the stratified conversion judgment needs
  typings the judgment does not carry.** `Stratified`'s conversion constructors `rfl`, `symm`,
  `trans`, `sortDF`, `lamDF`, `forallEDF` have **no typing premises** (`Stratified.lean:85–88`,
  `:100–103`); the reference is the same except that its `refl` does carry one
  (`axioms.tex:31`). Our model's `soundAbove`/`sound` run on the **type-indexed**
  `IsDefEqStrong`. Converting at a preserved index (`Stratified.strong`) meets the port
  artifact `handoff` §5 names: composing type-indexed conversions at two types *is* unique
  typing. **This is defect (c) in a new place**: `sorts_no_common_hasType0` machine-checks
  that `⊢₁`-convertible terms need not share a `⊢₀` type. The repair `handoff` §12 floats for
  `thm:ckappa` — two independent typings instead of a common one — is the same repair needed
  here, and it is the concrete first row-zero for this route (§8).
* **`⟦Γ⟧ ≠ ∅` is not inductively maintainable as stated.** (1) and (2) carry it; the induction
  must go under binders (`forallEDF`, `lamDF`), where the extended context `α::Γ` is
  inhabited only if `⟦α⟧_γ ≠ ∅`, which is false for `α = ⊥`. The thesis writes no case, so
  there is no way to know what it intended. Note the hypothesis is *harmless for
  `kernel_sound`* — that theorem bottoms out in the empty context (`SoundInduction.sound_nil`)
  — but it is **not** harmless for `Injectivity.lean`, whose statements are over arbitrary
  `OnCtx Γ (env.IsType U)` with no inhabitation side condition.

## 6. Tagged types and the circularity — they are two different constructions

`soundness.tex:326` promises "a ZFC analogue of unique typing" and it delivers something
real, but **it is not the construction our model stream rejected**, and the difference is
where the answer lives.

| | thesis (`soundness.tex:328–348`) | model stream (`docs/model-interface.md:815–831`) |
|---|---|---|
| what is tagged | **types**: `T_n ⊆ U_n` with `⦇·⦈ : T_n → U_n`; a *type's* denotation is a tag | **values**: type-values `⟨0,·⟩`, function-values `⟨1,·⟩` |
| what it buys | `𝒰`/`Π`/`Σ`/`W`/`+`/`ulift` are freely generated ⟹ injective and pairwise disjoint | `⟦.sort u⟧ ∩ ⟦.forallE A B⟧ = ∅` |
| target statement | DefInv clauses (1),(3): two *types* are not convertible | `SortForallEDisjoint`: one *term* has a sort type and a Π type |
| status | consistent | **circular** — `proofIrrel` forces the tag constant on a proposition's inhabitants |

**How the thesis avoids the circularity: `T_0 = U_0`, `⦇p⦈ = p` (`soundness.tex:328`).**
Propositions are **not** tagged; their denotations stay `∅` or `{•}`. Terms are never tagged
at all. So `proofIrrel` — which identifies *terms* of a proposition, all of them `•` — cannot
touch a tag. The model stream's obstruction does not arise because the thesis never asks tags
to separate inhabitants of a proposition.

**But the escape is bought, not free, and the price is the sequential dependency.** For the
tag scheme to be well-defined, a term whose denotation is a tag (a type) must not also be an
inhabitant of a proposition — otherwise `proofIrrel` would force two tags equal. The thesis
gets this from the proof-split language, where the split has *already been made using
`lvl`/`sort`*, i.e. using unique typing. Inside the joint induction the same fact is
available at index `n` from part (2) at `n` (`α : p : ℙ` and `α : 𝒰_ℓ` give `ℓ ≈ 0`, so `α`
is itself a proposition, hence untagged) — **so tagging is consistent at each index given
level-uniqueness at that index, and gives level-uniqueness at the next index only through the
route §5 shows is blocked.**

**Verdict on Q3: the thesis does avoid the circularity, and the reason is directly reusable —
tag types, not values; leave `Prop` untagged.** What is *not* reusable is any hope that this
gives `SortForallEDisjoint`: that statement is about a term with two types, tags are on types,
and the thesis's scheme says nothing about it. `model-interface.md`'s refutation stands
unchanged.

## 7. `normalization.tex`, `Wtypes.tex`, and what is *stated* versus *proved*

**Q4 — strong normalization: nothing depends on it.** `normalization.tex` is 23 lines, defines
`⇝_σ` (`⇝_κ` with `K⁺` scaled back to `K`) and stops at `UNFINISHED`. Nothing in the thesis
`\autoref`s it; nothing in `unique.tex` or `soundness.tex` uses SN. `unique.tex` uses
**confluence** (`thm:church_rosser`), which is a different theorem and is written out. So
"SN is unfinished" does **not** reframe soundness — soundness never needed it. What SN would
buy is decidability/evaluation, which `kernel_sound` does not assert. *This closes Q4 in the
benign direction.*

**Q5 — the joint induction does not need `Wtypes.tex`, but the model does, and our tree has
already replaced it.** `soundness.tex`'s interpretation clause list (`:140–189`) has **no
general inductive type**: it has `⊥, Σ, +, ulift, ‖·‖, W, =, acc, quot`, exactly the eight
primitives `Wtypes.tex` reduces inductives to. So the thesis's model is defined only for the
reduced language and the reduction is a prerequisite. But `Wtypes.tex:197` — "The remainder"
— says the introduction rules, the recursor, and the ι-rule **"will be left as future work"**.
So the bridge from Lean's inductives to the modelled language is *asserted, not proved*, in
the thesis. Our tree interprets inductives directly (`SetModel/Inductive.lean`, `IndInterp`,
`IndStage`, `IndCard`, `CtorTrans`), which is more work but is the only version that can
carry `kernel_sound`'s nested-inductive requirement. **Do not import `Wtypes.tex`.**

**The ledger, kept apart as required.**

| item | status in the thesis |
|---|---|
| `thm:sound` / `thm:sound2` (sequential soundness) | **written out in full**, case by case (`soundness.tex:224–316`, `:357–359`) |
| `thm:utype` | written out — and its application case is **machine-checked false** (`SubstCRefute`) |
| `thm:church_rosser`, `thm:ckappa`, `thm:1dinv` | written out; `thm:gg_compat`'s `:180` bullet has a reading defect with a repair; `thm:ckappa`'s base case **machine-checked false** |
| `item:p_subst`, `item:gg_subst` | stated, proof given as "All parts are easy inductions" / "It is easy to prove by induction"; both need `SubstT`, **machine-checked false** at depth ≥ 1 |
| lvl/sort lemma, translation, type preservation both ways | stated; proofs "straightforward by induction" |
| **the joint induction** | **statement only.** Base case `n = 0` in three lines, inductive step **absent** — the text stops mid-sentence |
| inductives → 8 primitives (`Wtypes`) | **explicitly future work** |
| strong normalization | **`UNFINISHED`**, nothing depends on it |
| compilation | stub, ends mid-grammar (`e ::= x |`) |

Three of the thesis's written-out arguments are machine-checked wrong in this repo. The joint
induction is not one of them, because there is nothing there to check.

## 8. If anyone funds this, the checks in order

Cheapest first; each is a row-zero that can kill the route before the expensive part.

1. **Stratified regularity at a preserved index, in the two-typing form:**
   `Γ ⊢ₙ₊₁ e ≡ e' → (∃A, Γ ⊢ₙ e : A) ∧ (∃A', Γ ⊢ₙ e' : A')`.
   Not the common-type form — that *is* unique typing, and `sorts_no_common_hasType0`
   refutes it. Without this the interpretation has nothing to evaluate at a `trans` middle
   term and §4's leverage does not exist. **This is the whole route's row zero.** Note
   `forallEDF`'s case needs "a domain's type is a sort", so price `IsType` there (trap #12).
2. **Is level-uniqueness at `n+1` reachable without `thm:utype`'s `app` case?** The `app`
   case needs only `lvl(B.inst a) = lvl(B'.inst a)`. Levels are term-independent, and
   `imax(ℓ₁,ℓ₂) ≈ 0 ↔ ℓ₂ ≈ 0` (`VLevel.imax_eq_zero`, and `SoundInduction.imax_eq_zero_iff`
   is the arithmetic already in the tree). So the **Prop-shadow** of the case may close from
   `∀A.B ≡ₙ₊₁ ∀A'.B'` plus DefInv clause (1) at `n+1` — *without* clause (2) and *without*
   `SubstC`. **This is the one genuinely untried idea this reading produced, and it is
   cheap.** If it closes, the route survives `SubstC`; if it does not, the route is dead and
   the reference is closed as a source of a plan. Run it before anything else in this file is
   acted on.
3. **A stratified `PropSplit`** (`PropSplitN n`) with the four stability fields, and
   `propSplitOf` at the index. `PropSplitAudit.lean` is the template; the audit criterion
   there ("a structure whose producers all consume the same structure has never had its
   fields tested") applies unchanged.
4. **Tags, types-only, `Prop` untagged** — `soundness.tex:328–348`. Only needed for DefInv
   clause (3); clause (1) needs no tags.
5. **The `⟦Γ⟧ ≠ ∅` question**: either maintain it under binders (unlikely, §5) or show
   `Injectivity.lean`'s consumers tolerate it. If neither, the model route delivers DefInv
   only in inhabited contexts and `sort_inv` as stated is out of reach.

Not on this list, deliberately: anything from §§3–4, `thm:ckappa`, `normalization.tex`,
`Wtypes.tex`.

## 9. Traps this reading adds

13. **A quoted architecture can be from a different theory.** `soundness.tex:368`'s "we must
    prove soundness and unique typing in one large induction" is inside the *equality
    reflection* subsection, about a rule Lean does not have, and its base case cites the
    sequential theorem. Read the enclosing `\subsection` before quoting a `\input`ed file.
14. **`UNFINISHED` in this thesis is per-chapter and it is not only `normalization.tex`.**
    `soundness.tex` ends with it too, mid-sentence, and `Wtypes.tex` ends with an explicit
    "left as future work". Grep for it before pricing anything against a chapter's tail.
15. **Two constructions can share a name and target different statements.** "Tagging" in the
    thesis (tags on types, `Prop` untagged, targets type-injectivity) and "tagging" in
    `model-interface.md` (tags on values, targets `SortForallEDisjoint`) are different, and
    the circularity that kills the second does not touch the first. Second instance of the
    §9/trap-#11 pattern: check what the statement *is* before transferring a verdict.
16. **A malformed theorem statement is evidence about intent.** `soundness.tex:376`'s
    unbound `ℓ, ℓ'` is the clue that part (2) is level-uniqueness rather than full unique
    typing — which is the difference between needing `SubstC` in full and possibly not
    (check 2 above). Do not silently repair a statement into the strongest reading.
