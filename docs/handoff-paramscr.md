# handoff-paramscr — Church–Rosser at a structure environment, and the `.app`-pattern census

Round of 2026-09-04.  Owner files: `Lean4Lean/Theory/Typing/ParamsCR.lean`, this document.
Everything else read-only.

The brief: Round A (`ParamsStruct.lean`) built `Lean4Lean.MutField.declParams`, a `VEnv.Params`
instance at a positive-field structure environment, and flagged that it had not discharged
`VEnv.not_crStatement_of_kstep`'s 18 hypotheses there.  Round B (`DescendSurplus.lean`) refuted
the confluence frontier and flagged that no `Params` instance registers an `.app` pattern, so
its refutation might be vacuous.  This round puts the two halves together.

---

## §1 PRIORS — written before any Lean was run this round.  NEVER EDITED.

### 1.1 What I will verify rather than trust

From the brief and from the two committed rounds, these are claims I will re-measure rather
than inherit:

| # | Claim, as handed to me | Whose | How I will check it |
|---|---|---|---|
| P1 | `VEnv.not_crStatement_of_kstep` has arity 18, cone 3579, carries `forallE_inv_stratified` | brief | `scripts/exists.lean`, `scripts/hole-cone.lean` |
| P2 | `VEnv.CRStatement` has arity 1, cone 37, hole-free | brief | same |
| P3 | `MutField.declParams` exists, arity 0, cone 6931, **no hypotheses** | Round A | `scripts/exists.lean`; read the definition |
| P4 | "no `Params` instance in the tree registers an `.app` pattern at all" | Round B (`DescendSurplus.lean:103-104`) | **I already believe this is stale** — see 1.3 |
| P5 | `crStatement_holds : CRStatement` is proved in the same file that refutes it | read in `KCanonical.lean:586` | `#print axioms`; the pair is only consistent if one side is hole-tainted, and I will say which |
| P6 | `declEnv`'s two inductive types live in `Type 0`, not `Prop` | read in `EtaStructG.lean:379,382` (`type := .sort (.succ .zero)`) | re-read + Lean `rfl` |
| P7 | `MutField.unitEnv_not_structEtaG` refutes structure eta at `unitEnv` | `EtaUnitRefute.lean:136` | read the proof — I note now that it separates an **axiom constant** `foo` from `A.mk` via `constNoConf_of_notIsProof`, which is a `const`-vs-`const` argument and therefore does **not** immediately transfer to a **bvar**-vs-`const` separation.  That gap is the thing I expect to matter. |

### 1.2 My prediction on Q1, recorded now

**I predict the 18 hypotheses do NOT discharge at `declParams`, and that Church–Rosser is
therefore NOT refuted there by this route.**  Reasoning, in advance of any Lean:

- The load-bearing hypothesis is `hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t`.
- `KStep.mk` (`KRule.lean:91`) requires, among other things,
  `IsDefEq env univs Γ h c A₀` with `h := .bvar 0` and `c` the constructor spine that the
  registered pattern's argument side matches.
- At `declParams` the only registered `.app` patterns are the ι-patterns of `MutField.decl`
  (`Pat.iota`, the only `.app`-shaped constructor of `Pat` available here besides `.quot`,
  and `declEnv` has no `Quot`).  Their argument sides are `MutField.A.mk` / `MutField.B.mk`
  spines, and the corresponding `A₀` is `MutField.A` / `MutField.B`, both **`Type 0`**
  (P6).
- So `hstep` demands a *variable* definitionally equal to a *constructor application* at a
  `Type`-valued inductive.  That is exactly structure eta for a non-structure (the whole point
  of the `MutField` block being *mutual*), and proof irrelevance — the one rule that makes this
  free — is unavailable because the type is not a `Prop`.
- Therefore I expect: **`hstep` is false at `declParams`**, semantically.  Whether this tree can
  *prove* it false is a separate question, and my prediction there is weaker: the existing
  refutation (`unitEnv_not_unitEta`) is a `const`-vs-`const` no-confusion argument and a `bvar`
  is not a `const` spine, so I expect to need a **bvar-rigidity** fact, and I do not yet know
  whether one exists in the tree.  My honest advance guess is 60/40 that I end the round with
  "`hstep` is false, reduced to a named residual" rather than "`hstep` is refuted outright".

**Consequence if the prediction holds:** Round A's instance is *not* a counterexample
generator, the eta front's being stuck is not explained by CR failing at `declParams`, and the
interesting content moves to *why* — the `Prop`/`Type` split at the major premise.

**What would falsify my prediction:** any `IsDefEq` route from `.bvar 0` to a constructor spine
at `declEnv` that I have not thought of — e.g. an ι-rule whose argument pattern is a bare
`.var` (then `c` could be the variable itself), or a `Γ` entry that makes the context degenerate.
I will check the `.var`-argument possibility explicitly, because if the pattern's argument side
can be a `.var`, `c := .bvar 0` and `hstep` fires by `IsDefEq.refl`, and my whole prediction
collapses.  **I flag now that this is the single way I could be wrong, and I will look at it
first.**

### 1.3 My prediction on Q2, recorded now

**I predict Round B's absence claim (P4) is STALE, and that I will not need to prove a negative.**
`Lean4Lean/Theory/Typing/PatAppParams.lean` (dated 2026-09-01 in its own header) announces
itself as "the first `Params` instance that registers `.app` patterns" — `appParams`, over
`cycEnv` with `P : Prop`, `D D2 : P`, `T : Type`, `C : P → T`, registering `cycQ = C D` and
`cycQ2 = C D2`.  The major premise `D : P` with `P : Prop` is exactly the `Prop`-typed major
premise Round B asks for.  `KCanonical.lean`'s own `refParams_kSmall` docstring **already
carries a dated correction saying so**, and `DescendSurplus.lean` (2026-09-04, later!) repeats
the uncorrected claim anyway.  That is a stale-absence claim of exactly the kind
`scripts/exists.lean` exists to stop, and it is claim #17 by the brief's count of 16.

**But I predict the refutation is still not thereby instantiated**, because `PatAppParams.lean`
also proves (its own §"Items 2 and 3") that `hne` — the hypothesis "the redex is not `NormalEq`
to the rule's right-hand side" — is **false** at `appParams`, both right-hand sides being closed
terms that are `NormalEq` to each other.  Round B's `not_appDFExtraStatement_of_propMajor'`
carries an `hne` of the same shape.  So my predicted Q2 verdict is the three-part one:

1. an `.app`-registering instance with a `Prop` major premise **exists** (`appParams`) — P4 is stale;
2. Round B's refutation is nonetheless **not** non-vacuous *at that instance*, because `hne`
   is refuted there;
3. so the honest verdict is "not vacuous for want of an instance; uninstantiated for want of an
   instance whose rule table has non-`NormalEq` right-hand sides", which is a different and
   sharper statement than either round had.

I do **not** predict I can prove "no instance can register such a rule" — I expect the opposite,
that one exists, so the negative is not the thing to prove.

### 1.4 Method commitments

- Every headline name gets arity, hole-cone size, and `#print axioms`, measured, not recalled.
- "false" and "unproved" get different words in every sentence I write.
- No edit outside `Theory/Typing/ParamsCR.lean` and this file.  Any implied edit elsewhere is
  written verbatim in §5 and left undone.

---
## §2 MEASUREMENTS, appended as made

### 2.1 The falsifier I named in §1.2 is closed — the ι-pattern's argument side is never a `.var`

`Pattern.SimplePattern.toPattern` (`Theory/Typing/Pattern.lean:291`) is
`| .iota r m c n => .app (.varN (.const r) m) (.varN (.const c) n)`.  So a registered `.app`
pattern's **argument** side is a `varN` chain over a `.const` — a constructor spine — never a
bare `.var`.  The one way my Q1 prediction could have collapsed does not exist.  Proved in my
file as `Lean4Lean.VEnv.Params.pat_app_iota` (the `∃`-form of `Params.pat_app_noApp`).

### 2.2 The reduction, proved: a `K⁺` step at a variable forces a variable/constructor conversion

`Lean4Lean.VEnv.kstep_bvar_ctorConv` — arity 8 (`[Params]`, `Γ`, `f`, `t`, `i`, `hstep` + 2
implicit), **no hypothesis on the environment at all**:

> `KStep Γ (.app f (.bvar i)) t →`
> `∃ cn ls as A₀, IsDefEq env univs Γ (.bvar i) ((.const cn ls).mkApp as) A₀`

So `not_crStatement_of_kstep`'s `hstep` is, at every `Params` instance, exactly the demand that
**a variable be definitionally equal to a constructor spine**.  This is the general half of the
Q1 answer and it holds at every instance, `declParams` included.

### 2.3 P4 is STALE, as predicted in §1.3 — and `KCanonical.lean` already says so

`Theory/Typing/PatAppParams.lean` exists and its header is explicit: "`appParams` below is such
an instance… registers **two** `.app` patterns".  `KCanonical.lean`'s own
`refParams_kSmall` docstring carries a dated correction ("**The reason given here was wrong,
corrected 2026-09-01**… `Theory/Typing/PatAppParams.lean` now exhibits one (`appParams`)").
`DescendSurplus.lean:103-104`, written 2026-09-04 — three days *later* — states the
uncorrected claim.  Verdict: **stale absence claim, and the correction was already in the
tree's own text at the claim site.**

### 2.4 `MutField.bigEnv` already existed — the second stale-absence check that paid

My first draft of §4 built `declEnv + bar : MutField.B` from scratch.  It was redundant:
`Theory/Typing/NoConfRepair.lean` §5 already has `MutField.bigEnv` = `declEnv` + `foo : A` +
`foo2 : A` + `bar : B`, with `bigEnv_wf`, `declEnv_le_bigEnv`, `bigEnv_bar`,
`bigEnv_ruleFreeHead`, `bigEnv_A_hasType`, `bigEnv_B_hasType` all proved — and
`Theory/Typing/ParamsStruct.lean` already imports it transitively (checked with the
`can-cite.py` closure walk), so it was citable from my file with **no new import**.  The
redundant construction was deleted.

### 2.5 The refutation instrument, and why the open node is *not* on the path

The row I need is `ShapeVar.lean`'s `VarAppDisj` — "a rule-free constant spine is not
convertible to a variable".  Two measurements about its availability:

* `VEnv.spineVarAppDisjT_wf` (`Verify/Typing/NoConfGuard.lean:272`) proves the row at **every**
  `VEnv.WF` environment — but in the `IsType`-guarded form, i.e. only when the *variable is
  itself a type*.  My variable has type `MutField.A`, which is not a sort, so `IsType` is false
  and **this theorem does not apply**.  (It would have been the cheap route; it is not
  available.)
* The `¬ IsProof`-guarded form (`VarAppDisj`, `SpineVarAppDisj`) is a **hypothesis everywhere**
  in the tree.  `ShapeIndep.lean` §3.1 says why: the guard is on the left endpoint and
  transports the wrong way along an environment extension, and turning it round is
  `ConstVar.lean`'s `AxiomConservativity`, an open node.

**The route I used avoids that node entirely**, and this is the one methodological point of the
round: I do not transport `¬ IsProof` backwards along an extension.  I *add the fresh axiom by
hand* and prove `¬ IsProof a` **at the extended environment**, exactly as
`MutField.unitEnv_not_isProof_foo` does; then plain substitution (`VEnv.IsDefEq.instN`) turns
the variable conversion into a constant/constant one, and `VEnv.constNoConf_of_notIsProof`
identifies the heads.  Nothing here needs conservativity.

`Lean4Lean.VEnv.bvar_ne_constApp_of_freshAxiom` is that lemma, stated generally (arity 14):

> at `env ≤ env'` with `env'.WF`, a fresh axiom `a : .const S []`, `S : Type 0` in `env'`, and
> `a`, `cn` both rule-free with `a ≠ cn` — no variable declared at `.const S []` is
> `env`-definitionally equal to a `cn`-headed constant spine.

### 2.6 Both members of the block are covered, the positive-field one included

* `Lean4Lean.MutField.declEnv_bvar_ne_constApp_A` (fresh inhabitant `foo`)
* `Lean4Lean.MutField.declEnv_bvar_ne_constApp_B` (fresh inhabitant `bar`) — the
  **positive-field** member, which is the one `declParams` is advertised for.

`MutField.B` is uninhabited by closed terms (`bCtor`'s single field has type `∀ p : Prop, p`),
which is why an axiom and not a term is what the argument needs.

* `Lean4Lean.MutField.declParams_no_kstep_bvar_A` and `_B`: **no `K⁺` step at `declParams`
  fires on a variable of either member.**  Proof: §1's reduction, then §5's refutation, with
  the pattern's constructor leaf shown to be a `declEnv` constant and neither recursor
  (`declParams_pat_app_leaf`, three cases of `Lean4Lean.Pat`; the δ case cannot produce an
  `.app` at all).

### 2.7 The instrument census the brief asked for, run rather than recalled

`scripts/exists.lean` on the names the brief handed me — all three of its numbers are **exact**:

| name | module | arity | cone | holes in cone |
|---|---|---|---|---|
| `Lean4Lean.VEnv.not_crStatement_of_kstep` | `Theory/Typing/KCanonical` | 18 | 3579 | `IsDefEqU.forallE_inv_stratified` |
| `Lean4Lean.VEnv.CRStatement` | `Theory/Typing/KCanonical` | 1 | 37 | none (`sorryAx`-free) |
| `Lean4Lean.MutField.declParams` | `Theory/Typing/ParamsStruct` | 0 | 6931 | `forallE_inv_stratified`, `WF.rigidShapeUniqNS` |
| `Lean4Lean.VEnv.not_appDFExtraStatement_of_propMajor'` | `Theory/Typing/DescendSurplus` | 23 | 688 | none (`sorryAx`-free) |

`scripts/shape.lean` with `HEADS="Lean4Lean.VEnv.Params"` enumerates **eight** `Params`
instances in the built population (468 modules), not the three the brief guessed at:
`Lean4Lean.refParams`, `Lean4Lean.cycParams`, `VEnv.propLoopParams`,
`VEnv.propLoopParamsOfWF`, `MutField.unitParams`, `MutField.declParams`, `VEnv.appParams`,
and **`VEnv.quotParams`** (`Verify/QuotAppParams.lean`).  `quotVEnv`'s instance the brief
speculated about *is* `quotParams`, and it is built and committed.

---

## §3 THE Q1 VERDICT

**Church–Rosser is NOT refuted at `MutField.declParams` by `not_crStatement_of_kstep`, and the
hypothesis that fails is `hstep`, which is FALSE there — not merely unproved — whenever the
Π-domain is either member of the block.**  My §1.2 prediction was correct, including the
mechanism (`Prop` vs `Type` at the major premise) and including which hypothesis carries the
weight.  It was **wrong about the difficulty**: I priced a full refutation at 60/40 against, and
it went through, because the fresh-axiom route sidesteps the open conservativity node (§2.5).

### 3.1 Hypothesis-by-hypothesis, at `declParams`

`not_crStatement_of_kstep`'s eighteen binders are `[Params]`, six implicits (`Γ e A B t u`) and
eleven explicit hypotheses.  Verdicts, with the Π-domain `A` taken to be
`.const MutField.A []` or `.const MutField.B []`:

| # | hypothesis | verdict at `declParams` |
|---|---|---|
| — | `[Params]` | **satisfied** — `declParams` is the instance, arity 0, no hypotheses (Round A) |
| 1 | `hΓ : OnCtx Γ (IsType env univs)` | **satisfiable** (e.g. `Γ = []`) |
| 2 | `hΓA : OnCtx (A::Γ) …` | **satisfiable**; both members are types (`declEnv_A`, `declEnv_B`) |
| 3 | `hA : Γ ⊢ A : .sort u` | **satisfiable**, `u = .succ .zero` |
| 4 | `he : Γ ⊢ e : .forallE A B` | **satisfiable** in principle (a recursor spine one argument short); not constructed here, and not needed — see below |
| 5 | **`hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t`** | **FALSE** — `MutField.declParams_no_kstep_bvar_A` / `_B` |
| 6 | `hlam : ∀ A' e', e ≠ .lam A' e'` | **satisfiable** (a recursor spine is not a λ) |
| 7 | `hnp : e is not a proof` | **satisfiable** (the motive lands in `Type`) |
| 8 | `hrig : e is ParRed-normal` | **satisfiable** (one argument short of the ι-pattern) |
| 9 | `hrigA : A is ParRed-normal` | **satisfiable** (`.const` with no rule) |
| 10 | `hrigT : t is ParRed-normal` | **satisfiable** (choose a normal minor premise) |
| 11 | `hne : the redex is not NormalEq to t` | **satisfiable** — and note this is the *opposite* of the situation at `appParams`, where `hne` is the false one |

**Only #2 and #5 are consumed.**  `MutField.declParams_kstep_absurd_at_members` (arity 7) is the
verdict with the surplus deleted; `MutField.declParams_not_crStatement_of_kstep_hyps_absurd`
(arity 18) is the same thing with the whole list written out in the original order, so a reader
can check it is that theorem's bundle and not a weakening.  Because #5 is refuted **from #2
alone**, no amount of work on #1, #3, #4, #6–#11 can rescue the refutation: this is not "14
discharge and 4 do not", it is "one is false and the rest are irrelevant".

### 3.2 Why `hstep` is false, in one paragraph

`VEnv.kstep_bvar_ctorConv` (mine, cone 750, `sorryAx`-free) says a `K⁺` step at a variable major
premise **is** a demand that the variable be definitionally equal to a constructor spine — at
every instance, with no environment hypothesis.  At `declParams` the pattern's constructor leaf
is a declared constant of `declEnv` and neither recursor
(`MutField.declParams_pat_app_leaf`; the δ constructor of `Lean4Lean.Pat` cannot produce an
`.app` at all, and the ι and quot ones both carry the leaf's `constants` field).  Both members
of the block live in `Type 0` (`decl`'s `type := .sort (.succ .zero)`), so **proof irrelevance
is unavailable** — and proof irrelevance is the only rule that makes a variable convertible to a
constructor.  Substituting a fresh axiom inhabitant for the variable then turns the conversion
into a constant/constant one, where `constNoConf_of_notIsProof` identifies the two heads and the
axiom's freshness contradicts it.

**This is the same universe boundary the whole eta/K front sits on**, and it is the reason the
`Prop`-major refutations (`quotParams`, `appParams`) work while the structure-environment one
cannot: `declEnv` has no `Prop`-valued inductive.

### 3.3 Consequences for Round A's stated risk

Round A wrote: "if they are dischargeable, this instance is a counterexample generator rather
than an unblocker."  **They are not dischargeable, so `declParams` is not a counterexample
generator** — at least not through `not_crStatement_of_kstep`, and not at either member.  What
`declParams` is, is an instance at which the K-rule's redex shape simply never occurs: `KStep`
is empty at any variable major premise of the block.  That is a *positive* fact about the
instance, and it is why the eta front being stuck is **not** explained by confluence failing at
`declParams`.

### 3.4 The honest limit, and it is one line

`hAmem` — the Π-domain is taken **syntactically** equal to a member.  A domain merely
*convertible* to one is not covered.  `MutField.KStepBvarFreeAtConvMembers` is that residual,
named in my file so a later round can attack it; `kStepBvarFreeAtConvMembers_of_syntactic` checks
that it implies what §7 proves, so it is a strengthening of the same statement and not a
different one.  Closing it needs three things, **none of them false, all of them work**:
unique typing at `.bvar 0` (`WF.uniq'`, available), an enumeration of `declEnv`'s constants at
their stored types (`addInduct'_constants_inv` plus a `decide` over `decl.allConsts`, plus "a
constructor's stored type is not a sort"), and un-lifting a conversion
(`IsDefEqU.weakN_iff`, a census hole already in `declParams`' own cone).

---

## §4 THE Q2 VERDICT

**Yes — two instances register `.app` patterns, and one of them has a `Prop`-typed major
premise, so Round B's refutation is NOT vacuous.  I proved it fires.**

### 4.1 The absence claim was stale twice over

`DescendSurplus.lean:103-104` (2026-09-04): "no `Params` instance in this tree registers an
`.app` pattern".  Measured:

* `VEnv.appParams` (`Theory/Typing/PatAppParams.lean`, arity 0, cone 5220, **`sorryAx`-free**)
  registers two `.app` patterns over `cycEnv`, major premise `D : P` with `P : Prop`.
* `VEnv.quotParams` (`Verify/QuotAppParams.lean`, arity 0, cone 9265, holes
  `forallE_inv_stratified` + `WF.rigidShapeUniqNS`) registers `quotPat` at a `VEnv.WF`
  environment; at `u = 0` the major premise `Quot.{0} α r` **is** a proposition while the motive
  is `Type 0`.

`KCanonical.lean`'s `refParams_kSmall` docstring already carried a dated correction naming
`appParams`; `DescendSurplus.lean` was written three days after that correction and repeats the
uncorrected claim.  **Flagging the docstring defect the brief warned about, as instructed**:
`KCanonical.lean:614` still says, in the *same* docstring, "The instance that would test it does
not exist: no `Params` instance in this tree registers an `.app` pattern", and only the
following paragraph corrects it.  A reader who stops at the first sentence gets the wrong
answer; that first sentence is now wrong twice (`appParams`, `quotParams`).

### 4.2 The refutation, fired

`Lean4Lean.VEnv.quotParams_not_appDFExtraStatement` (arity 0, cone 9368, holes
`forallE_inv_stratified` + `WF.rigidShapeUniqNS`): **`AppDFExtraStatement` — the statement of
`NormalEq.appDF_extra_of_descend`, the single frontier lemma between `NormalEq.descend` and
`IsDefEq.church_rosser` — is false at `quotParams`.**  Every one of
`not_appDFExtraStatement_of_propMajor'`'s hypotheses is discharged there, `hbrig` included
(`VEnv.qParRed_qMk_bvar`, mine: the matched `Quot.mk` spine at a variable argument is
`ParRed`-normal).  So Round B's own vacuity worry is answered in the negative: the shape exists,
and the refutation is a refutation.

**Its limit, stated:** the *statement* `not_appDFExtraStatement_of_propMajor'` is `sorryAx`-free,
but the *instance* is not — `quotParams` is `paramsOfPiInv … (piInv_axiom …)`, so its existence
is modulo `PiInv`, i.e. modulo `forallE_inv_stratified` and `WF.rigidShapeUniqNS`.  The honest
reading is "false at an instance that exists modulo the two ambient injectivity holes", which is
exactly the status of `quotParams_not_crStatement` already in the tree.

### 4.3 Where it is vacuous, and that is also worth saying

`Lean4Lean.VEnv.appParams_no_appDFExtra_refutation` (arity 21, cone 5233, **`sorryAx`-free**):
at `appParams` the same refutation's hypothesis list is **contradictory**, because `hne` is
false there — both right-hand sides are closed terms that `NormalEq.appDF` + `NormalEq.proofIrrel`
relate to the redex (`appParams_normalEq_rhs`).  So the two `.app` instances split cleanly:
`appParams` cannot host any of the `propMajor` refutations, `quotParams` hosts all of them.  The
discriminating property is `quotRHS_depends_on_match` — `quotParams`' right-hand sides are not
closed.

### 4.4 The one thing this changes about the tree's map

`CRStatement` is already refuted in the tree — `VEnv.quotParams_not_crStatement`
(`Verify/QuotAppParams.lean`, arity 0, cone 9383), committed as `a561fa9`.  So the question
"is Church–Rosser false?" was **already answered yes** before this round, at a quotient
environment; what this round adds is that it is **not** false at a *structure* environment by
that route, and why.  Note also that `KCanonical.lean` proves `crStatement_holds : CRStatement`
(cone 4385) in the same file that refutes it — consistent only because `crStatement_holds` is
`sorryAx`-tainted through four holes (`weakN_iff`, `forallE_inv_stratified`,
`rigidShapeUniqNS`, `NormalEq.descend`).  P5 verified: measured, and the taint is real.

---

## §5 EDITS I WOULD MAKE ELSEWHERE — WRITTEN, NOT MADE

I own only `Theory/Typing/ParamsCR.lean` and this file.  Three edits are implied elsewhere and
I have made none of them.

1. **`Lean4Lean/Theory/Typing/DescendSurplus.lean`, lines 103-107.**  Replace

   > every hypothesis is a property of the *witness*, but no `Params` instance in this tree
   > registers an `.app` pattern (`PatWFIota.lean` is where that would come from).  So this
   > refutation, like `not_parRedStatement_of_propMajor` and `not_hK_of_propMajor`, is
   > conditional on an instance of a shape that does not exist yet

   with

   > **Stale as of this file's own commit date.** Two instances register `.app` patterns:
   > `VEnv.appParams` (`Theory/Typing/PatAppParams.lean`, 2026-09-01) and `VEnv.quotParams`
   > (`Verify/QuotAppParams.lean`).  At `quotParams` the major premise is a proof of the `Prop`
   > `Quot.{0} α r` and this refutation **fires**:
   > `VEnv.quotParams_not_appDFExtraStatement` (`Theory/Typing/ParamsCR.lean`).  At `appParams`
   > it does not, because `hne` is false there
   > (`VEnv.appParams_no_appDFExtra_refutation`, same file).

2. **`Lean4Lean/Theory/Typing/KCanonical.lean`, the `refParams_kSmall` docstring.**  The
   sentence "The instance that would test it does not exist: no `Params` instance in this tree
   registers an `.app` pattern." should be deleted rather than corrected two sentences later,
   and the correction paragraph should name `VEnv.quotParams` as well as `appParams`.

3. **`Lean4Lean/Theory/Typing/ShapeVar.lean`, near `VarAppDisj` (line 372).**  Worth a
   cross-reference: the row is open in general, but
   `VEnv.bvar_ne_constApp_of_freshAxiom` (`Theory/Typing/ParamsCR.lean`) proves it at the
   shape "variable declared at a `Type 0`-valued constant type carrying a fresh axiom", by
   substitution alone — no `AxiomConservativity`.  That is a route the file's §3.1 discussion
   does not mention and a later round may want.

None of the three is a frozen file.  `Verify/Soundness.lean`, `Verify/Axioms.lean` and
`Verify/Guard.lean` are untouched and unread-for-editing by me.

---

## §6 MY METHOD'S GAPS, stated because the next round will hit them

1. **I did not construct hypothesis #4 (`he`), or #6–#11, at `declParams`.**  I did not need to
   — #5 is refuted from #2 alone — but that means my table's word "satisfiable" for those rows
   is an **argument**, not a machine-checked witness.  If a later round needs them (e.g. to show
   the *rest* of the bundle is consistent, which would sharpen "one is false" to "exactly one is
   false"), they are unbuilt.  I have flagged each such row as satisfiable-by-argument above and
   none of my Lean theorems depends on any of them.
2. **`hAmem` is syntactic** (§3.4).  I know of no reason the convertible case behaves
   differently and I did not prove it.
3. **I did not check whether `declParams` registers an `.app` pattern at all.**  `Pat.iota` at
   `declEnv` needs its closedness and `constants` fields discharged for `decl`'s two ι-rules,
   and nobody in the tree has built them.  So it is possible that `declParams`' `Pat` table is
   *empty*, in which case my refutation is true but for a duller reason than the universe
   argument.  My theorems are stated so this does not matter (they refute the step whatever the
   table is), but the *interpretation* in §3.2 assumes the table is non-empty, and that is
   unverified.  **A later round should measure it before quoting §3.2's reading.**
4. **The eight-instance census is of the built population** (468 modules).  A `Params` instance
   in an unbuilt or `Experimental/` module would not appear.  `Experimental/SExpr.lean` has its
   own separate `Params` class, which is a different constant and was correctly excluded.
5. `quotParams`' `Prop`-major property I took from `QuotAppParams.lean`'s own prose plus the
   fact that `not_parRedStatement_of_propMajor` and `not_crStatement_of_kstep` both fire there
   (both of which demand `Γ ⊢ A : .sort .zero` and are machine-checked).  I did not
   independently re-derive `qA0_isProp`; I used it.

---

## §7 AXIOM CENSUS FOR `Theory/Typing/ParamsCR.lean`, measured

Build: zero errors, zero warnings from this file; `lake build` completes (1654 jobs).

| name | arity | cone | `#print axioms` | holes in cone |
|---|---|---|---|---|
| `VEnv.Params.pat_app_iota` | 5 | 123 | `[propext, Quot.sound]` | none |
| `VEnv.kstep_bvar_ctorConv` | 6 | 750 | `[propext, Quot.sound]` | none |
| `VEnv.bvar_ne_constApp_of_freshAxiom` | 18 | 7558 | `+ sorryAx, Classical.choice` | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend` |
| `MutField.declEnv_Arec` | 0 | — | `[propext, Classical.choice, Quot.sound]` | none |
| `MutField.declEnv_ctor_ne_recs` | 4 | — | `[propext, Classical.choice, Quot.sound]` | none |
| `MutField.declEnv_contains_ne_axiom` | 2 | — | `[propext, Classical.choice, Quot.sound]` | none |
| `MutField.declEnv_bvar_ne_constApp_A` | 10 | 7642 | `+ sorryAx` | the same four |
| `MutField.declEnv_bvar_ne_constApp_B` | 10 | 7642 | `+ sorryAx` | the same four |
| `MutField.declParams_pat_app_leaf` | 4 | — | `+ sorryAx` | the same four |
| `MutField.declParams_pat_nonempty` | 0 | — | `+ sorryAx` | the same four |
| `MutField.declParams_no_kstep_bvar_A` | 5 | 7662 | `+ sorryAx` | the same four |
| `MutField.declParams_no_kstep_bvar_B` | 5 | 7662 | `+ sorryAx` | the same four |
| **`MutField.declParams_not_crStatement_of_kstep_hyps_absurd`** | **18** | **7667** | `+ sorryAx` | the same four |
| `MutField.declParams_kstep_absurd_at_members` | 7 | 7667 | `+ sorryAx` | the same four |
| `MutField.KStepBvarFreeAtConvMembers` (residual, unproved) | 0 | 6933 | `+ sorryAx` | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `VEnv.appParams_no_appDFExtra_refutation` | 21 | 5233 | `[propext, Classical.choice, Quot.sound]` | **none — `sorryAx`-free** |
| `VEnv.qParRed_qMk_bvar` | 5 | — | `+ sorryAx` | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| **`VEnv.quotParams_not_appDFExtraStatement`** | **0** | **9368** | `+ sorryAx` | `forallE_inv_stratified`, `rigidShapeUniqNS` |

`Lean4Lean.VEnv.IsDefEq.uniq` and `IsDefEq.uniqU` are in the cone of every `sorryAx`-carrying row
(watched-by-policy, **not** holes).  Where four holes appear rather than two, the extra pair
(`IsDefEqU.weakN_iff`, `NormalEq.descend`) enters through `VEnv.patWF_of_wf` →
`VEnv.constNoConf_of_notIsProof`, i.e. through the no-confusion instrument, not through
`declParams`.  `declParams`' own cone carries only two.

**Nothing in this file has `own value is a hole: true`.**  Every `sorryAx` line is a theorem
standing on named census holes — priced, not blocked — and the two `sorryAx`-free headline rows
(`kstep_bvar_ctorConv`, `appParams_no_appDFExtra_refutation`) are the ones a later round can use
unconditionally.

## §8 Files touched

* `Lean4Lean/Theory/Typing/ParamsCR.lean` — new, mine, 487 lines.
* `docs/handoff-paramscr.md` — new, mine, this file.

Nothing else.  `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` untouched.
Three edits elsewhere are written verbatim in §5 and **not made**.  No git command was run.
