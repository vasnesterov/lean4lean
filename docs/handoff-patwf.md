# Handoff: `VEnv.PatWF` beyond the δ fragment

**Question asked:** discharge `VEnv.PatWF`'s ι and quot cases, or reduce them to something
strictly smaller than `IsDefEqU.forallE_inv`; if the dependency on `forallE_inv` is
essential, say so with the measurement.

**Answer.**  The **quot case is closed** — `VEnv.patWF_quot`, `sorry`-free, in a new file this
stream owns.  Its Π-injectivity dependency is carried as the *explicit hypothesis*
`VEnv.PiInv` (`Theory/Typing/Injectivity.lean`, which is `forallE_inv`'s type verbatim), and
with that hypothesis in place the measured residual is **`IsDefEqU.forallE_inv_stratified`
alone — `forallE_inv` is not in the cone**.  `PatWF` therefore now holds for every
environment that registers no ι-rule (`patWF_of_iotaFree`), a strictly larger class than
`patWF_of_deltaFragment`'s.

The **ι case is open**, and is decomposed below into eight named obligations.

Marks: **[machine-checked]** = a named Lean declaration in this tree, with its axiom set or
cone reproduced; **[measured]** = a machine run whose output is reproduced; **[read]** = read
off source; **[analysis]** = neither.

---

## 0. Three corrections to the brief this stream was given

0. **"`Verify/` cannot import anything proved through `PatternRules.lean`"**
   (`docs/handoff-params.md` §3.3, the seven-name collision) is **stale**.
   `Verify/Typing/ConstSpine.lean` already imports `Theory/Typing/ParamsBuild.lean`, and a
   single file importing `Theory.Typing.PatWF`, `Verify.Typing.ConstSpine` *and*
   `Verify.Soundness` compiles and `#check`s all three of `patWF_quot`,
   `const_app_inv_of_patWF`, `kernel_sound`. **[measured]**  Whatever renaming §3.3 asked for
   has happened; do not re-open it.

1. **"the ι and quot cases need `IsDefEqU.forallE_inv`"** is right in substance and wrong in
   detail for the quot case.  What the quot case needs is Π-injectivity *as a hypothesis*
   (`PiInv`), one single time, at one single step (`HasArgs.of_mkApp'`'s `cons` case).  Once
   that is an argument rather than a citation, the *unconditional* residual of the whole quot
   case is `forallE_inv_stratified`, reached through `IsDefEq.uniq` / `SortUniq`, not
   `forallE_inv`.  **[measured, §3]**

2. **"discharge `PatWF`, and the three consumer holes follow"** — the quot case alone gives
   them **nothing**.  See §5.  Reporting this partial discharge as a discharge would be the
   failure mode the brief warned about, so it is stated first: **`quotReduceRec.WF`,
   `TrProj.uniq` and `TrProj.weak'_inv` are exactly as blocked as they were.**

---

## 1. What is in the tree now

`Lean4Lean/Theory/Typing/PatWF.lean` — **new**, 438 lines, **no `sorry`**, 38 declarations
(14 of them auto-generated match auxiliaries).  Nothing else in the tree changed; the census
is unchanged at **19**. **[measured: `lake env lean scripts/sorry-census.lean`, TOTAL 19;
full `lake build` clean.]**

| name | statement | cone holes **[measured]** |
|---|---|---|
| `Pattern.matches_varN_inv` | inverting a `varN` match: a term matching a `varN` chain over a `const` leaf **is** that constant applied to a spine of the chain's depth | none |
| `Pattern.matches_iota_inv` | the same for the whole ι shape — the converse of `matches_iota_paths`, which existed only in the *construction* direction | none |
| `VEnv.HasArgs.concat_inv` | `HasArgs.concat` inverted: split the last argument off a spine | none |
| `VEnv.instAll_bvar_get0` | `instAll_bvar_get` at `k = 0`, with the `liftN 0` discharged | none |
| `VEnv.HasType.mkLams_inv` | **peeling a λ-telescope off a typing** — the converse of `HasType.mkLams`.  Takes `PiInv` | `forallE_inv_stratified` |
| `VEnv.rule_body_typing` | a rule's body, typed under its own telescope, in an arbitrary context | `forallE_inv_stratified` |
| `VEnv.IsDefEq.extra_applied'` | `IsDefEq.extra_applied` with `hOn`/`hlhsTy`/`hrhsTy` discharged, so only the **spine** is left to supply | `forallE_inv_stratified` |
| `VEnv.HasArgs.of_mkApp'` | `Theory/Typing/SpineInv.lean`'s `of_mkApp` with `PiInv` as an argument instead of a citation | `forallE_inv_stratified` |
| `VEnv.patWF_quot` | **the quot case of `PatWF`, in full** | `forallE_inv_stratified` |
| `VEnv.IotaFree` | no `VInductDecl'.iotaRule` is registered | — |
| `VEnv.patWF_of_iotaFree` | **`PatWF` for every ι-free environment**, from `env.WF` + `PiInv` | `forallE_inv_stratified` |
| `VEnv.paramsOfIotaFree` | **`VEnv.Params` for every ι-free environment** | `forallE_inv_stratified` |
| `VEnv.quotPat_matches_nontrivial` | the quot conclusion is not a reflexivity — §6 | none |
| the `quot*_eq` / `quot*Doms` block | `Quot.lift`'s, `Quot.mk`'s and `quotDefEq`'s telescopes, every one of them `rfl`-checked against `Theory/Quot.lean`; **nothing transcribed by hand** | none |

Axioms, verbatim **[measured]**:

    'Lean4Lean.VEnv.patWF_quot'        depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
    'Lean4Lean.VEnv.patWF_of_iotaFree' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
    'Lean4Lean.Pattern.matches_iota_inv' depends on axioms: [propext]

The `sorryAx` is `forallE_inv_stratified`'s, inherited through `IsDefEq.uniq`; it is **not**
new and **not** `forallE_inv`'s.

---

## 2. How the quot case goes, and where each `Check` clause is spent

Five steps; the ι case is the same five steps with telescopes in place of literals.

1. **Invert the match.**  `Pattern.matches_iota_inv` turns `quotPat.Matches e m1 m2` into
   `e = Quot.lift.{ls} a₁ … a₅ (Quot.mk.{ls'} b₁ b₂ b₃)` with both readbacks.  This lemma did
   not exist: `Theory/Typing/PatternDecode.lean` had `matches_iota_paths`, which *builds* a
   match, and every `Pat.extra*` proof only ever needed that direction.  `PatWF` is the first
   consumer that has to read a match *back*.
2. **Invert the typing** of that spine against `Quot.lift`'s declared telescope
   (`HasArgs.of_mkApp'`) and then against `Quot.mk`'s.  **This is the only step that consumes
   `PiInv`** — one call, in `of_mkApp'`'s `cons` case, reconciling the domain `app_inv`
   invents for the head with the domain the declared type states.
3. **Rebuild the spine that saturates the *rule's* telescope.**  `quotDefEq` binds
   `α r β f c a`; the first five entries are literally `Quot.lift`'s first five domains
   (`quotTele.take 5 = quotLiftDoms.take 5`, by `rfl` **[machine-checked]**), and the sixth is
   `α`, whereas `Quot.lift`'s sixth is `Quot α r`.  So the rule's sixth argument is the
   constructor's field `b₃`, whose declared type is `b₁`, and it has to be retyped at `a₁`.
   **This is where the `Check`'s parameter clause is spent**: with `Check.true` there would be
   nothing to convert `b₁` to `a₁` and no `HasArgs` to hand to step 4.
4. **Fire the rule** (`IsDefEq.extra_applied'`) at that spine and read both sides:
   `Quot.lift.{ls} a₁ … a₅ (Quot.mk.{[ls₀]} a₁ a₂ b₃) ≡ a₄ b₃`.
5. **Bridge back to `e`** by one `appDF` at the major-premise position, whose own congruence
   is `IsDefEq.mkAppDF` over a `HasArgsDF` built from the two parameter clauses and a
   `constDF` at the level equivalence.  **This is where the `Check`'s level clause is spent**:
   the rule stores `Quot.mk.{p0}` against `Quot.lift.{p0,p1}`, and an arbitrary match supplies
   an unrelated `ls'`.

So `Theory/Typing/PatternDecode.lean`'s header warning — that `Check.true` would make `pat_wf`
"unprovable by anyone rather than merely unproved" — is now **confirmed by a proof that uses
the clauses**, not merely asserted.  Both non-vacuous clause groups of `quotCheck` are
consumed; the index group is genuinely empty (`Quot` has no indices), as its docstring says.

---

## 3. The measurement the brief asked for

Hole cones, transitive over `getUsedConstantsAsSet` **[measured]**:

| seed | cone size | `sorry`-carrying declarations reached |
|---|---|---|
| `VEnv.patWF_quot` | 3728 | `IsDefEqU.forallE_inv_stratified` |
| `VEnv.patWF_of_iotaFree` | 3753 | `IsDefEqU.forallE_inv_stratified` |
| `VEnv.paramsOfIotaFree` | 6708 | `IsDefEqU.forallE_inv_stratified` |
| `VEnv.HasArgs.of_mkApp` (`SpineInv.lean`, **not** this file's) | 3559 | `forallE_inv`, `forallE_inv_stratified` |
| `VEnv.IsDefEq.uniqU` | 3448 | `IsDefEqU.forallE_inv_stratified` |
| `VEnv.const_app_inv_of_patWF` | 7282 | `forallE_inv_stratified`, `forallE_inv`, `IsDefEqU.weakN_iff`, `NormalEq.descend` |
| `VEnv.constNoConf_of_patWF` | 7283 | the same four |
| `VEnv.const_sort_inv_of_patWF`, `const_forallE_inv_of_patWF` | 7257 / 7259 | the same four |
| `Lean4Lean.Pat.extra` | 4494 | **none** |

Two things to read off this.

**(a) The dependency on Π-injectivity is essential, but it is a *hypothesis* dependency, and
the corner is strictly downstream — not equivalent.**  `PiInv → PatWF(quot)` is proved;
`PatWF → PiInv` is **false as an implication**, because `PatWF` is vacuous at a rule-free
environment while `PiInv` is not.  So "this corner and the sort/Π corner are one problem" is
**too strong**: the honest statement is that the const/rule corner is *reducible to* the sort/Π
corner and adds nothing new to it.  For the quot case that reduction is now machine-checked.

**(b) What is left unconditionally is `forallE_inv_stratified`, and it enters through
`IsDefEq.uniq`.**  Every route that inverts a typing at all — `HasType.lam_inv` via
`HasType.strong`, `IsDefEq.uniqU`, `HasType.defeqU_r` — sits on top of `SortUniq`, whose only
source in this tree is `forallE_inv_stratified`.  So no amount of care in *this* corner removes
that hole; `patWF_quot`'s cone is already minimal in that sense (it equals `IsDefEq.uniqU`'s
cone plus nothing).

---

## 4. The ι case: exactly what it still owes  **[analysis]**

Not attempted.  It is the same five steps as §2, but the two telescopes are
`VInductDecl'.recType j` and `VIndCtor.type C D j` rather than six-entry literals, and the
index clause group is non-empty.  Eight obligations, none of which exists in the tree:

1. **Telescope-prefix agreement.**  `recType j`'s telescope is
   `atRecTele params ++ motives ++ minors ++ liftTele (nm+nmin) (atRecTele T.indices)` and
   `iotaCtx C` is `atRecTele params ++ motives ++ minors ++ liftTele (nm+nmin) (atRecTele
   (C.fields.map (·.type)))` (`Theory/Inductive/Decl.lean:530` and `:543`) **[read]**, so the
   first `np+nm+nmin` entries agree *syntactically*.  Needs stating as a `take` lemma with the
   three length facts.
2. **`HasArgs.append_inv`** — `concat_inv` generalised to a split at an arbitrary point, to cut
   the recursor spine into `params ++ motives ++ minors` and `indices`, and the constructor
   spine into `params` and `fields`.
3. **Field-block transport.**  The fields' declared domains come instantiated at the
   *constructor's* matched parameters `b₁ … b_np`; `iotaCtx` states them at the *recursor's*
   `a₁ … a_np`.  Bridging is `IsDefEq.instAllCongrSort`
   (`Theory/Inductive/StructureClosed.lean`) — which applies, because a field type is a type —
   and needs each field type typed at a sort in the constructor's context, i.e. `VIndCtor.WF`
   recovered from `env.WF` via `VEnv.WF.ruleShape` / `VInductDecl'.iotaCtx_of_staged`.
4. **The index clauses.**  `iotaLhs`'s index arguments are
   `C.args.map (fun a => (D.atRec a).liftN off nf)`; the check supplies
   `iotaComputed`, which is `mkLams (C.params ++ fields) a` applied to the *matched*
   constructor arguments.  Showing that `instAll` of the former at the rebuilt spine is the
   latter is `Pat.extra_iota`'s `VInductDecl'.iota_index_clause`
   (`PatternRules.lean:1416`) **run in the opposite direction** — there the match is the rule's
   own, here it is arbitrary.  Expect this to be the largest single piece.
5. **Level bridging.**  The recursor leaf carries `D.recUvars` levels and the constructor leaf
   `D.uvars`, offset by one when `D.isLE`; `VInductDecl'.iotaLevelPairs` is the intended
   bridge and `constDF` at `D.selfLvls.map (VLevel.inst ls)` the intended consumer.
6. **The constructor-side congruence**, i.e. §2 step 5 at a general arity — `mkAppDF` over a
   `HasArgsDF` whose parameter entries come from the parameter clauses and whose field entries
   are reflexivity.  This one is a direct generalisation of the quot proof and should be cheap.
7. **`instAll` at general `bvars` blocks**, replacing this file's six `instAll_bvar_get0`
   `have`s.  `VExpr.instAll_bvar_get`, `instAll_bvars`, `bvars_spine_align` and
   `instAll_map_liftN_bvars` are the existing raw material.
8. **The major-premise `appDF`**, which needs `HasType.mkApp'` at the recursor's telescope cut
   before the major premise — the general form of this file's `hfun5`.

Order to attack them in: 1, 2, 7 (pure bookkeeping, no typing); then 6, 8 (the quot proof
generalised); then 3, 5; then 4 last, because it is the one that needs `Pat.extra_iota`'s
machinery re-derived.

**Do not** state the ι case as a new named hypothesis and call it a reduction.  `PatWF` is
already one field of ten; splitting it again into "the ι case" buys nothing and hides that
nothing was proved.

---

## 5. The consumer holes, re-measured — **none of the three follow**

`quotReduceRec.WF` (`Verify/TypeChecker/WHNF.lean:109`), `TrProj.uniq` and
`TrProj.weak'_inv` (`Verify/Typing/Lemmas.lean:1528`, `:760`) are unchanged.

The reason is structural and worth stating plainly.  All three are consumed up to
`kernel_sound`, so they must hold at an **arbitrary** environment — and an arbitrary Lean
environment registers ι-rules.  `patWF_of_iotaFree` gives `PatWF` only when none is
registered.  The chain they want is
`PatWF → const_app_inv_of_patWF → quotReduceRec.WF`, and its first link is still open.

`quotReduceRec.WF`'s own docstring says "`VEnv.PatWF` for a quotient-carrying environment is
the concrete next step".  That reading is **too optimistic**: the environment it must serve is
quotient-*and*-inductive-carrying.  Closing the quot case of `PatWF` does not weaken the ι
requirement by one line, because `const_app_inv_of_patWF` quantifies over all registered rules
when it runs the Church–Rosser argument.

What *did* move: `paramsOfIotaFree` makes `VEnv.Params` — and hence every one of the ~534
`ChurchRosser.lean`/`HeadReduction.lean` declarations quantified over it — available at any
ι-free `VEnv.WF` environment from `env.WF` and `PiInv` alone.  Previously that needed
`DeltaFragment`, which excluded the quotient rule and so excluded every environment Lean
actually builds a kernel for.

---

## 6. Non-vacuity, and what is *not* checked

The acceptance criterion asks for non-vacuity, and there are two separate questions here.

* **The conclusion is not a reflexivity.**  `quotPat_matches_nontrivial` **[machine-checked]**
  exhibits a concrete match at which `quotRHS.apply m1 m2` is syntactically different from the
  matched term.  So `patWF_quot` is not discharged by `IsDefEqU.rfl` at its own hypotheses.
* **A full witness is NOT constructed.**  Nothing here builds a `VEnv.WF` environment carrying
  `quotDefEq` *together with a well-typed redex*; that needs `Quot`, `Quot.mk`, `Quot.lift` and
  `Eq` present and the environment proved `WF`.  `Verify/QuotConsts.lean`'s
  `trEnv_addQuot_wit` and `addQuot.WF'` are where such a witness would come from.  **Do not
  cite this file as establishing that**, and do not cite `patWF_of_iotaFree` as evidence that
  `IotaFree` is inhabited by an interesting environment — that too is unproved here.

The `Params`-inhabitation witnesses that *are* machine-checked remain
`ParamsWitness.lean`'s `propLoopParams` and `Verify/Typing/Rigidity.lean`'s
`propLoopEnv2_patWF`, both δ-only.

---

## 7. The design note's claim, checked

`Theory/Inductive/Decl.lean:595-616` (on `VInductDecl'.iotaRule`) ends: *"the shape chosen here
is what leaves `pat_wf` as the only field with real content."*  The brief asked for this to be
verified rather than repeated.

* **The operative half is true. [machine-checked]**  `VEnv.paramsOfWF` typechecks with `pat_wf`
  as its only hypothesis beyond `env.WF` and `U`, and `Lean4Lean.Pat.extra` — the field the
  η-expansion was designed for — has an **empty hole cone** (4494 declarations, no `sorryAx`)
  **[measured]**.  So `extra_pat` really is discharged for an arbitrary `VEnv.WF` environment,
  and `pat_wf` really is the only open field.
* **The connotation is misleading.**  "No real content" reads as "cheap", and three of the nine
  discharged fields were not: `Pat.uniq` and its supporting machinery run
  `PatternRules.lean:727-1030`, the global name-distinctness side condition it bottoms out in
  runs `:301-380`, and `Pat.extra_iota` runs `:1565-1707`.  The note's *own* next sentence —
  "the three orthogonality fields reduce to arithmetic on `Pattern.varN` depths plus one global
  side condition" — is accurate and is the sentence to quote.  Read the claim as *"`pat_wf` is
  the only field that is still open"*, which is what it is, not as a statement about effort.

No sibling claim in that docstring was found to be false this round.

---

## 8. Files

* `Lean4Lean/Theory/Typing/PatWF.lean` — **new**, 438 lines, no `sorry`.
* Everything else — **unchanged**.  In particular `ParamsBuild.lean`, `PatternRules.lean`,
  `Pattern.lean`, `PatternDecode.lean`, `KRule.lean`, `KDescend.lean` were not touched, and
  neither were the frozen files.
* `docs/handoff-params.md` §3.3 and §7 should be read together with §0 above.
