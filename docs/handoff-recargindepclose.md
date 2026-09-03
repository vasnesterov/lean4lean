# `VIndRecArg.exists_indep` — census, blocker correction, and a better witness

Round of 2026-09-03.  Owned files: `Lean4Lean/Theory/Inductive/RecArgIndepClose.lean` (new) and
this file.  **Nothing else was edited.**  `Decl.lean` was read only; the one edit this round
would propose to it is written out in §6 and was *not* made.

Target: `Lean4Lean.VIndRecArg.exists_indep`, `Lean4Lean/Theory/Inductive/Decl.lean`.  Real
positions, checked rather than quoted: docstring opens at **line 536**, `theorem
VIndRecArg.exists_indep` at **line 642**, the `sorry` at **line 661**.  (The brief said "around
661"; 661 is the `sorry`, 642 is the declaration.)

---

## 1. Pre-flight, both questions answered before any proving

**Does a refutation already exist?  No.**  `HEADS="Lean4Lean.VIndRecArg.BindersIndep Not"`
(`scripts/shape.lean`, 2026-09-03 18:03 UTC) returns exactly **one** constant in the whole
431-module population: `Lean4Lean.RecArgIndep.not_bindersIndep_raiRec1`.  That negates the clause
**at one `r`**, which does not refute an existential that may pick a different `r'`; and its
instance is one the hole's own `henv₀`+`hstage` pair excludes
(`Lean4Lean.RecArgIndep.rai_not_staged`).  `RecArgIndep.lean` §7.3 already grades it
"[analysis, not proved] whether the conclusion is actually false … a candidate counterexample,
not a refutation".  That grading is correct and I did not improve on it.

**Does an equivalent statement exist under another name?  The conclusion does; the theorem does
not.**  `Lean4Lean.VIndRecArg.IndepGoal` (`Theory/Inductive/RecArgIndep.lean`) is the hole's
conclusion verbatim, with `Lean4Lean.VIndRecArg.indepGoal_of_exists_indep` as the machine-checked
faithfulness link.  `HEADS="…BindersIndep Exists …IsDefEqType"` returns 8 constants: four
auto-generated `VIndField.WF` projections, the hole itself, and the three drop-ins
`exists_indep_of_pre_norec`, `exists_indep_of_binders_nil`, `exists_indep_of_i_zero` — each the
hole plus one extra hypothesis.  **No unconditional proof of the statement exists anywhere.**

---

## 2. Users, measured (`scripts/users.lean`, 2026-09-03 18:02 UTC, population 431 modules /
26075 non-internal declarations)

| name | direct | transitive |
|---|---|---|
| `Lean4Lean.VIndRecArg.exists_indep` | **1** | **1** |
| `Lean4Lean.VIndRecArg.IndepGoal` | 5 | 8 |
| `Lean4Lean.VIndRecArg.BindersIndep` | 42 | 1780 |
| `Lean4Lean.VIndField.WF.binders_indep` | 1 | 1629 |
| `Lean4Lean.VIndField.WF` | 59 | 1917 |
| `Lean4Lean.VEnv.IsDefEqU.forallE_inv` | 41 | 502 |
| `Lean4Lean.VEnv.WF.rigidShapeUniqNS` | 3 | 529 |

**The single direct consumer is `Lean4Lean.VIndRecArg.indepGoal_of_exists_indep`** — the
faithfulness check in `RecArgIndep.lean` whose only job is to apply the hole so that `IndepGoal`
is provably its conclusion.  It needs the full statement by construction (it *is* the statement).

So: **no proof in this tree stands on this hole.**  The right reading of the 1629-user figure for
`binders_indep` is that the *clause* is load-bearing, not that the *discharge lemma* is: every one
of the ~40 `binders_indep` construction sites in the tree discharges it **directly** —
`nofun`, an `r.binders = []` lemma (`ntreeAux_binders_indep`, `mp_binders_indep`,
`tq_binders_indep`), or a real syntactic proof (`NestedBuild.pfnAuxMk_bindersIndep`,
`DeclExamples.forestCons_BindersIndep`, `DeclExamples.wMk_BindersIndep`).  Sites checked:
`DeclExamples`, `NestedHead`, `NestedBuild`, `IndexedWit`, `IndexedNested`, `ParamRedex`,
`MemberRedex`, `RestoreBridge`, `RestoreOpWit`, `CompanionResolve`, `StructureEta`,
`ConstSubstNested`, `SetModel/PreludeWitness`, and six `Verify/` witnesses.  **Not one routes
through `exists_indep`.**  Its role is prospective: it is what a general proof of
`VIndCtor.WF.fields` inside `addInduct_WF` would call.

**Consequence for the brief's "special cases suffice?" question.**  The special cases *already*
suffice for every consumer that exists, and they are already in the tree and hole-free.  There
was no cheaper retirement available to buy, and the net-loss check the brief warns about is what
rules out the one apparently-cheap route that remains — see §4.

---

## 3. What was proved (all in `Theory/Inductive/RecArgIndepClose.lean`, all hole-free)

`scripts/exists.lean`, 2026-09-03 18:13 UTC.  Every row: `own value is a hole: false`,
`cone reaches sorryAx: false`.  Axioms: `[propext, Quot.sound]` or less — no `Classical.choice`,
no `sorryAx`; bar `after ⊆ before` met.

| fully-qualified name | cone |
|---|---|
| `Lean4Lean.RecArgIndepClose.indepUpgrade_of_indepGoal` | 642 |
| `Lean4Lean.RecArgIndepClose.indepGoal_iff_indepUpgrade` | 2200 |
| `Lean4Lean.RecArgIndepClose.typeConsts_map_fst` | 153 |
| `Lean4Lean.RecArgIndepClose.noConsts_of_constsIn` | 44 |
| `Lean4Lean.RecArgIndepClose.blockConst_ruleFreeHead_of_staged` | 1007 |
| `Lean4Lean.RecArgIndepClose.blockSpine_not_defeq_forallE` | 1013 |
| `Lean4Lean.RecArgIndepClose.blockSpine_not_defeq_sort` | 1013 |
| `Lean4Lean.RecArgIndepClose.env₀_const_noBlock_of_staged` | 995 |
| `Lean4Lean.RecArgIndepClose.defeq_noBlock_of_staged` | 995 |
| `Lean4Lean.RecArgIndepClose.NTreeHyps.nlPre_recArg` | 237 |
| `Lean4Lean.RecArgIndepClose.NTreeHyps.nlPre_not_norec` | 245 |
| `Lean4Lean.RecArgIndepClose.NTreeHyps.ntree_hyps_all` | 2054 |
| `Lean4Lean.RecArgIndepClose.NTreeHyps.ntree_indepGoal` | 2066 |

### §1 The reduction as an `↔`

`RecArgIndep.indepGoal_of_indepUpgrade` had only `IndepUpgrade → IndepGoal`, at the price of
`VEnv.SortUniq`.  The converse is **free**: `VIndRecArg.BindersIndep` reads only `.binders`, so
`IndepGoal`'s witness telescope *is* an `IndepUpgrade` witness with no repackaging
(`indepUpgrade_of_indepGoal`).  `indepGoal_iff_indepUpgrade` is the equivalence.  This is the
brief's fallback (e) discharged: **`IndepUpgrade` is the smallest sufficient premise**, the two
statements differ by exactly the `F.type` conversion, and `SortUniq` is exactly its price.

### §2 The blocker named in `Decl.lean` is the wrong one

`exists_indep`'s docstring says the proof needs `VEnv.IsDefEqU.forallE_inv`.  Walking the actual
obstruction gives a different and smaller answer.  For `B ∈ r.binders` to mention the earlier
recursive field `x`, `x` must occur in `B`; `B` is *syntactically* block-free (`hbind`) and `x`'s
type is a block spine `I_j params π`.  The positions `x` can occupy:

* head of an application → `x`'s type must convert to a Π;
* argument → the function's type must convert to a Π **with a block-spine domain**, and the
  function is a `bvar` of `Γ` (a parameter or an earlier field), a `const`, or a `lam`;
* Π/λ domain, or `B` itself → `x`'s type must convert to a sort.

The `const` case is closed by staging (`env₀_const_noBlock_of_staged`, §2b).  The *parameter* case
is closed syntactically and for free: `VInductDecl'.tyApp` applies **all** the parameters to
`I_j`, so a parameter whose type mentioned `I_j params π` would mention itself.  The `lam`-domain
and earlier-field cases are closed iff no block-free type converts to a block spine.

So the whole content is: **a block spine is defeq to neither a Π nor a sort** — already named in
this tree as `VEnv.RigidConstPiDisj` and `VEnv.RigidConstSortDisj`
(`Theory/Typing/RigidNodeCircle.lean`), both guarded by `VEnv.RuleFreeHead`.
`IsDefEqU.forallE_inv` is **not** on this path.  §2 proves the guard for block constants
(`blockConst_ruleFreeHead_of_staged`) — nothing in the tree had discharged `RuleFreeHead` for a
block constant — and applies both predicates to block spines
(`blockSpine_not_defeq_forallE`, `blockSpine_not_defeq_sort`).

### §2b The constant route, generalised from one witness to every staged environment

`RecArgIndep.raiCiP_type_hasBlock` observes at one witness that a declared constant whose *type*
mentions the block is what makes the candidate counterexample work.
`env₀_const_noBlock_of_staged` makes it a theorem: `Ordered.constsInC` plus
`addConstList_fresh` give `D.NoBlock ci.type` for every constant of `env₀`.  Recorded limitation,
stated at the lemma: the block's *own* type constants are exempt — `addIndTypes` adds them left to
right, so `Ordered` lets `I₁`'s stored type mention `I₀`.  That route cannot supply a binder,
because a binder must be syntactically block-free, but it is why the lemma quantifies over
`env₀`'s constants and not `env`'s.

### §2c The sharpest fact, and the reason it matters

**Both premises §2 reduces to are false at `Ordered` environments** — already machine-checked in
this tree: `VEnv.not_rigidConstPiDisj_rcPiEnv` and `VEnv.not_rigidConstSortDisj_rcSortEnv`
(`Theory/Typing/RigidConstPrice.lean`), at `ordered_rcPiEnv` / `ordered_rcSortEnv`.  Since
`exists_indep` carries `VEnv.Ordered env` and **not** `VEnv.WF env` (its docstring: naming
`VEnv.WF` at this layer is an import cycle), it cannot simply have them.  This is the strongest
thing to know about the hole and neither its docstring nor `RecArgIndep.lean` records it.

`defeq_noBlock_of_staged` is the answer.  Those refutations work by pointing a two-δ-rule **hub**
constant at a rule-free head (`rcHub ≡ rcRF.{0}`, `rcHub ≡ ∀ (_ : Prop), Prop`), so `rcRF` heads
no rule and is still convertible to a Π through the hub.  The theorem shows that route is
unavailable for a block constant at a staged environment, by **freshness alone**: `addIndTypes`
copies `env₀.defeqs` unchanged (`addConstList_defeqs`), and `Ordered env₀` makes every side and
the type of every rule in it mention only `env₀`-declared constants — none of which is a block
name.  No rule of a staged environment mentions the block anywhere, and no rule is added later.

What remains of the residual is a **confluence** question — can β, η, proof irrelevance and rules
that never mention the block relate a block spine to a Π or a sort? — which is what
`VEnv.WF.rigidShapeUniqNS` answers.  **[analysis, not proved]** that it cannot.  This file proves
only that the tree's one known refutation route is closed.

### §3 A strictly better non-vacuity witness

`RecArgIndep.rai_hyps_all` is the tree's only joint instance of the ten hypotheses and is
degenerate on three axes: `uvars = 0`, `params = []`, `pre = []` — the last being precisely the
axis `BindersIndep` is about.  `NTreeHyps.ntree_hyps_all` satisfies the same ten at
`Lean4Lean.InductiveDeclExamples.ntreeAux` (`uvars = 1`,
`params = [.sort (.succ (.param 0))]`, the parameterised nested block Lean's own kernel runs
nested elimination on), at the **second field of `_nested.List_1.cons`, whose earlier field is
recursive** — `nlPre_recArg` and `nlPre_not_norec` machine-check that
`bindersIndep_of_pre_norec` does *not* apply there.  `env₀ = VEnv.empty`, so `henv₀` is
`Ordered.empty` and `hstage` is a computation; `henv` comes from
`VInductDecl'.addIndTypes_ordered` on `ntreeAux_WF'` (which holds at *every* environment), and the
six field-level hypotheses come from `VIndCtor.WF.fields` rather than being re-derived.

**Vacuity both ways, stated apart as the ledger asks.**  *Premise satisfiable*: `ntree_hyps_all`.
*Conclusion at that instance*: `ntree_indepGoal`, and it is **degenerate** — `ntreeAux`'s
recursive fields all carry `ξ = []` (`nl_binders_nil`; it is how `NestedHead.lean` discharges the
clause for all three of them), so the instance is closed by `exists_indep_of_binders_nil` with
`r' = r`.  It is a better *non-vacuity* witness than `rai_hyps_all`; it is **not** evidence that
the residual case is reachable at a staged environment.  And the honest headline is:
**no witness anywhere in this tree needs a binder to move — the real parameterised nested block
included.**  `nfnAux` was not used and no witness here degenerates to it.

---

## 4. The net-loss check the brief asked for, run rather than assumed

The apparently-cheap retirement is: discharge the hole via `RigidShapeUniqNS.constPiDisj` /
`.constSortDisj`, which supply §2's premises from `VEnv.WF.rigidShapeUniqNS`.  **Measured, it is a
loss.**  `Decl.lean`'s `exists_indep` cone is 851 constants whose *only* hole is `exists_indep`
itself; `VEnv.WF.rigidShapeUniqNS` is a `sorry` with **529 transitive users**.  Taking that route
would put a 529-user hole into `Decl.lean`'s cone — and `Decl.lean` is upstream of `VEnv.WF`
(`Theory/Typing/Env.lean` transitively imports it), so it is an import cycle as well.  Hence the
rigidity facts stay **hypotheses** in the owned file, exactly as the three existing drop-ins keep
their extra hypothesis.

---

## 5. Verdict: not proved, not refuted, reduced — and the reduction is where the value is

* **Not refuted.**  Every counterexample route I could construct dies at one of three points:
  the `const` route at §2b, the parameter route at the `tyApp` self-reference, everything else at
  the rigidity question.  I looked specifically for the shapes the brief flags — nested and
  indexed families — and the nested case is *weaker*, not stronger: `ntreeAux`'s recursive fields
  have `ξ = []`, so nesting as this tree builds it does not produce a binder that could mention an
  earlier recursive field at all.
* **Not proved.**  Turning "nothing eliminates `I`" into a defeq argument needs, at minimum, a
  staged-environment rigidity lemma whose general form is false at `Ordered` environments (§2c);
  a proof would have to use block-name freshness in place of well-formedness, over the conversion
  relation.  That is a new induction, not an application of anything in the tree, and it was out
  of budget this round.
* **Reduced, twice, hole-free.**  `IndepGoal ↔ IndepUpgrade` (the `F.type`/`SortUniq` layer
  removed), and the residual identified as two *named existing* predicates whose guard is now
  discharged for block constants and whose only known refutation route is now closed for them.

### What a successor should and should not do

* **Do not** re-attack the hypothesis set as if `forallE_inv` were the blocker; it is not on the
  path (§2).
* **Do not** hunt for a counterexample at a non-staged environment; `RecArgIndep.lean` §7.2 is
  already that, already graded, and already excluded by the current hypotheses.
* **Do** attack the one open statement: at a staged environment, is a block spine convertible to
  a Π or to a sort?  §2c shows the hub route is closed, so this is confluence over rules that
  never mention the block — plausibly provable *without* `VEnv.WF`, which is exactly what the
  hole needs and what would let it be discharged at its own layer.
* Nothing needs `exists_indep` today.  It is a statement-quality obligation, not a critical-path
  hole; scheduling it above holes with real consumers would be a mistake the census now makes
  visible.

---

## 6. The exact edit to `Decl.lean` — written out, **not made**

`Decl.lean` is not owned by this stream and was not touched.  The edit I would propose is a
**docstring correction only; the `sorry` at line 661 stays.**  In the paragraph beginning
"**Why it is a `sorry` and not a proof.**" (`Decl.lean` lines 633–638), replace

> Turning "nothing eliminates `I`" into a defeq argument is the injectivity family — it needs
> `IsDefEqU.forallE_inv` (`Typing/Injectivity.lean`, open) to rule out the ill-formed field
> above, and that is downstream of `VEnv.WF` hence of `addInduct_WF`.

with

> Turning "nothing eliminates `I`" into a defeq argument needs, not `IsDefEqU.forallE_inv`, but
> rigidity of the block's constants: that a block spine is defeq to neither a Π nor a sort
> (`VEnv.RigidConstPiDisj`, `VEnv.RigidConstSortDisj`, `Theory/Typing/RigidNodeCircle.lean`).
> `Theory/Inductive/RecArgIndepClose.lean` §2 enumerates the routes and closes every one but
> those two, discharges their `VEnv.RuleFreeHead` guard for block constants
> (`blockConst_ruleFreeHead_of_staged`), and records that both are **false** at `Ordered`
> environments (`VEnv.not_rigidConstPiDisj_rcPiEnv`) while the refutation route that makes them
> false — a two-rule hub aimed at a rule-free head — cannot exist at a staged environment
> (`defeq_noBlock_of_staged`).  So what is open here is confluence over rules that never mention
> the block, and it does **not** obviously need `VEnv.WF`.

No other change: the statement, the hypotheses, the conclusion and the `sorry` all stay as they
are.  I did not make this edit and the orchestrator should confirm it with the human before doing
so.

---

## 7. What I could not do, and why

* **Prove the hole.**  Needs the staged-environment rigidity induction described above.  Out of
  budget; the file states what it reduces to instead.
* **Refute it.**  No route survived §2's enumeration; the surviving one is the same open question
  a proof needs, so a refutation would have to *refute* confluence at a staged environment, which
  would be a much larger claim than a counterexample.
* **Measure which hypotheses are load-bearing by `lean_minimal_hypotheses`.**  Not attempted: as
  the brief says, a `sorry` body needs no hypothesis, so the tool reports all ten unused.
  Measured by instantiation instead: `ntree_hyps_all` shows all ten jointly satisfiable, and
  `RecArgIndep.rai_hyps`/`rai_not_staged`/`raiEnvP_add` already show `henv₀` and `hstage` each
  doing work.  I did **not** establish which of `hlen`, `hΓ`, `hpre`, `hty` are load-bearing;
  the three existing drop-ins use none of them (they are `_`-prefixed there), which is evidence
  that they are load-bearing only for the residual case, not proof of it.
