# handoff-crshape — what is the RIGHT confluence statement?

Round of **2026-09-04**. Stream owns exactly `Lean4Lean/Theory/Typing/CRShape.lean` and this file.
Everything else read-only. `ConfluenceRebuildPrice.lean` / `CRSEScope.lean` are another stream's.

The brief's question: `VEnv.CRStatement` is refuted at `VEnv.quotParams` and *not* refutable at
`MutField.declParams`; three of five open census holes bottom out in confluence. So: **what is the
right confluence statement, given the current one is false where proofs are involved and
apparently fine where they are not?**

The brief's hypothesis, offered as a guess to be tested and not trusted:

> the failure is routed through a `Prop`-typed major premise; `CRStatement` is *too syntactic*;
> confluence of the *reduction* fails on proof terms while the *conversion* relation is unharmed,
> because proof irrelevance identifies the divergent results anyway. So the correct statement
> quotients by proof irrelevance — confluence "up to `IsProof`".

---

## §1 PRIORS — written before any Lean tool ran. **Never edited.** Corrections go to §2.

### §1.0 What I read before writing this section (source text only, no Lean tooling)

`CLAUDE.md`; `docs/audit-hole-producers.md` (preview); `scripts/shape.lean`, `scripts/exists.lean`,
`scripts/can-cite.py` headers; `Theory/Typing/ParamsCR.lean` (§0–§5); `Theory/Typing/KCanonical.lean`
`:500–620` (`CRStatement`, `not_crStatement_of_kstep`, `crStatement_holds`, `refParams_kSmall`);
`Verify/QuotAppParams.lean` `:560–660` (`quotParams_kstep_eta`, `quotParams_not_crStatement`);
`Theory/Typing/ChurchRosser.lean` `:165–205` (`NormalEq`), `:752–770` (`ParRed`), `:2435–2480`
(`CRDefEq`, `CRDefEq.trans`, `ParRedS.church_rosser`); grep hits for `CRStatement` tree-wide.

### §1.1 Which of the brief's claims I will verify rather than trust

| # | brief's claim | trust or verify | why |
|---|---|---|---|
| B1 | `quotParams_not_crStatement` refutes `CRStatement`, arity 0, cone 9383, commit `a561fa9` | **verify** (`exists.lean`, `git show`) | a count without a date is a defect; three counts moved under the orchestrator today |
| B2 | of `not_crStatement_of_kstep`'s eighteen binders only two are consumed at `declParams`, and `hstep` is **false** there | **verify the binder count** (`lean_minimal_hypotheses` / count the signature); trust the falsity (`ParamsCR.lean` proves it with bodies) | the signature I read has ~11 explicit binders, not 18 — the 18 may count `Params` field projections or the instance's own binders |
| B3 | `scripts/shape.lean HEADS="Lean4Lean.VEnv.Params"` finds **eight** instances | **verify — brief itself says do not trust it** | |
| B4 | three of five open holes bottom out in confluence; every cheap producer of `forallE_inv_stratified` / `rigidShapeUniqNS` has hypothesis ≡ conclusion in-tree | **verify by reading the audit's own §-rows and re-measuring the two names** | restatement-vs-reduction is exactly the claim that has been wrong here before |
| B5 | the hypothesis itself (Prop-routing ⇒ quotient by proof irrelevance) | **verify, and expect to split it** | see §1.3 |

### §1.2 Numbered predictions, with probabilities

| # | prediction | P |
|---|---|---|
| P1 | `HEADS="Lean4Lean.VEnv.Params"` does **not** return exactly eight `Params` *instances* (the number will be a count of constants mentioning `Params`, most of them lemmas, not instances) | 0.80 |
| P2 | **Part (a) of the hypothesis holds**: every refutation of `CRStatement`/its frontier siblings now in the tree fires its ι/K step through a **`Prop`-typed major premise**, i.e. via `IsDefEq.proofIrrel` | 0.80 |
| P3 | **Part (b) fails.** In the `quotParams` refutation the *divergent pair* (`e` and `.lam A t`) is **not** proof-typed — `qLiftT0_not_proof` is fed in as `hnp` — so weakening `CRStatement`'s conclusion by "…or one side is a proof" / "…or `A` is a `Prop`" leaves it **still refuted at `quotParams`** | 0.90 |
| P4 | `NormalEq` **already contains** a `proofIrrel` constructor, so `CRDefEq`'s joining relation is *already* a proof-irrelevance quotient; the proposed repair is in the tree and does not repair | 0.95 |
| P5 | I can *prove in Lean* `¬ CRStatementUpToProof` (conclusion weakened by a proof/Prop disjunct) at `quotParams`, reusing `not_crStatement_of_kstep`'s witness unchanged | 0.75 |
| P6 | The real defect is **`ParRed.extra` matching syntactically** (`p.Matches e m1 m2`) where `KStep` matches **up to conversion** at the major premise (`hdq : IsDefEq … major … (ctor spine)`). Proof irrelevance is the cheapest *non-directional* producer of such a conversion, not the only conceivable one; but it is the only one that is *irreparable*, because delta/beta-convertible major premises are reachable by `ParRedS` first-reduce-then-match | 0.75 |
| P7 | Therefore the right statement is confluence over a reduction **closed under `KStep`** (`ParRedK`), or `NormalEq` gaining a closure at the K-redex position (the `hne` residual). The tree already has `ParRedK` (`ParRedKGraded`, `ParRedKWeakN`, `KDiamondJoin`) — so this is **not** a new proposal | 0.85 |
| P8 | …and that statement is **also already known false as formulated**: commit `a561fa9`'s message says "KDiamond and M3 are themselves FALSE". So the answer to "what is the right statement" is not reached by either of the two obvious repairs | 0.60 |
| P9 | `Verify/Typing/ConstSpine.lean` is **not** served by a Prop-exempt / proof-quotiented weakening: the shapes it separates are Π-vs-const-spine at arbitrary sorts, so a Prop escape clause is available to its adversary too | 0.65 |
| P10 | The three holes: a corrected confluence statement plausibly reaches `forallE_inv_stratified` and `rigidShapeUniqNS`, but **not** `IsDefEqU.weakN_iff`, which is a weakening/context lemma and not a confluence consequence | 0.55 |
| P11 | `Theory/Typing/CRShape.lean` **can** cite `Verify.QuotAppParams` without a layer violation (because `Theory/Typing/ParamsCR.lean` already imports it and the layer check reports that cluster as a SOFT REPORT) | 0.95 |
| P12 | Something in the tree **already** states a Prop/proof-irrelevance-weakened confluence variant (so my §3 is a restatement unless I check first) | 0.30 |
| P13 | I will find at least one docstring in the tree that calls a non-hole "(open)" or equivalent (method rule 4's flagged error class) | 0.60 |
| P14 | `crStatement_holds : CRStatement` and `quotParams_not_crStatement : ¬ CRStatement` coexist only because `crStatement_holds` is `sorryAx`-tainted; I will confirm which side carries the taint | 0.90 |

### §1.3 My own reading, stated up front so it can be scored

I expect the hypothesis to **split**: right about where the failure enters (a `Prop`-typed major
premise, i.e. proof irrelevance), wrong about the repair. The reason I expect the repair to fail is
that the refutation's *large elimination* is essential: at `quotParams` the major premise is a proof
(`Quot.{0} α r : Prop`) but the two divergent results live in `Type 0` (`B = .bvar 4`, the target of
`Quot.lift` at `v = .succ .zero`). Proof irrelevance cannot identify results that are not proofs.
That is what "large-eliminating subsingleton" means, and it is the same thing `KCanonical.lean`'s own
prose says (`typesys.tex:19-48`'s incompleteness). If so, quotienting by proof irrelevance is not a
repair but a category error: the quotient is already there (`NormalEq.proofIrrel`) and the failure is
one level down, in `ParRed.extra`'s **syntactic** `Matches`.

---

## §2 MEASUREMENTS

All measurements **2026-09-04**, commit `e4e01c6` (`git log -1 --format=%h`), population
**469 built modules** (`scripts/exists.lean`).

### §2.1 The census names, measured (answers B1, B4, P14, and method rule 4)

| name | module | arity | cone | own value a hole | holes in cone |
|---|---|---|---|---|---|
| `VEnv.CRStatement` | `Theory/Typing/KCanonical` | 1 | 37 | false | **none, `sorryAx`-free** |
| `VEnv.crStatement_holds` | `Theory/Typing/KCanonical` | 1 | 4385 | false | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend` |
| `VEnv.not_crStatement_of_kstep` | `Theory/Typing/KCanonical` | **18** | 3579 | false | `forallE_inv_stratified` |
| `VEnv.quotParams_not_crStatement` | `Verify/QuotAppParams` | **0** | **9383** | false | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `VEnv.IsDefEq.church_rosser` | `Theory/Typing/ChurchRosser` | 7 | 4383 | false | same four as `crStatement_holds` |
| `VEnv.IsDefEqU.forallE_inv` | `Theory/Typing/Injectivity` | 10 | 3574 | **false** | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `VEnv.IsDefEqU.forallE_inv_stratified` | `Theory/Typing/Injectivity` | 16 | 48 | **true** | itself |
| `VEnv.WF.rigidShapeUniqNS` | `Theory/Typing/Injectivity` | 3 | 630 | **true** | itself |
| `VEnv.IsDefEqU.weakN_iff` | `Theory/Typing/UniqueTyping` | 11 | 3231 | **true** | itself |
| `VEnv.NormalEq` | `Theory/Typing/ChurchRosser` | 4 | 4 (no proof term) | false | none |
| `VEnv.ParRed` | `Theory/Typing/ChurchRosser` | 4 | 4 (no proof term) | false | none |
| `VEnv.ParRedK` | `Theory/Typing/KEta` | 4 | 4 (no proof term) | false | none |
| `VEnv.KDiamond` | `Theory/Typing/KDescend` | 1 | 34 | false | none |

**Verdicts recorded against §1.**

* **B1 CONFIRMED** — arity 0, cone 9383, `Verify/QuotAppParams`, commit `a561fa9`
  (`Tue Sep 1 17:55:48 2026 +0200`, subject verified verbatim).
* **B2 CONFIRMED on the binder count** — `not_crStatement_of_kstep` really has **arity 18**
  (my §1.1 guess of "~11 explicit" was wrong: the count includes the `Params` instance and the
  implicit term/level binders).
* **P14 CONFIRMED, and sharpened into a finding the brief does not state.** The pair
  `crStatement_holds` / `quotParams_not_crStatement` is consistent because **both** sides are
  `sorryAx`-tainted, not just the positive one. And the refutation's taint is exactly
  `forallE_inv_stratified` + `rigidShapeUniqNS` — **two of the three holes the brief wants a
  corrected confluence statement to close.** See §2.2.
* **method rule 4, CONFIRMED at the named example** — `IsDefEqU.forallE_inv`, arity 10, cone 3574,
  `own value is a hole: false`. It is a theorem *standing on* two holes, not a hole.

### §2.2 FINDING C — the refutation is circular with the holes it is meant to explain

`quotParams_not_crStatement` is **not an unconditional refutation of `CRStatement`.** Its cone
reaches `sorryAx` through exactly `IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS`.
Those are two of the three genuinely-open holes that `docs/audit-hole-producers.md` says bottom
out in confluence.

So the brief's opening sentence — "`Lean4Lean.VEnv.CRStatement` is **already false** at a real
instance" — overstates what is measured. What is measured is:

> `CRStatement` is false at `quotParams` **modulo `forallE_inv_stratified` and
> `rigidShapeUniqNS`**.

Commit `a561fa9`'s own body says this in as many words and asks not to be quoted otherwise:
"CONDITIONAL, and it must not be quoted otherwise. All four results carry sorryAx with direct
sorry sites exactly forallE_inv_stratified and rigidShapeUniqNS — verified by me. … Two citations,
not one: every ¬NormalEq must block proofIrrel, so it is modulo PiInv AND propTypeAgreeOn."
**I confirm that independently today.** The brief dropped the condition; the commit did not.

Consequence for the round's question: one cannot ask "what is the right confluence statement,
given the current one is false" without noting that *the falsity itself is priced in the holes
confluence is supposed to discharge*. A corrected confluence statement that closed
`forallE_inv_stratified` and `rigidShapeUniqNS` would simultaneously make the refutation of the
old statement unconditional. The two are not independent.

### §2.3 The eight `Params` instances — P1 SCORED **WRONG**, the brief's number is right

Structural query (result type `= Lean4Lean.VEnv.Params`, whole 469-module population,
2026-09-04): **14 declarations**, of which **exactly 8 have arity 0**, i.e. are closed instances.
The brief's "eight" is correct and my P1 (0.80 that it was not eight) is **refuted**. The other
six are instance *constructors*: `paramsOfWF` (4), `paramsOfDelta` (4), `paramsOfPiInv` (4),
`paramsOfIotaFree` (5), `paramsOfWFAx` (3), `Params.mk` (10).

| instance | module | cone | `sorryAx` |
|---|---|---|---|
| `VEnv.propLoopParams` | `Theory/Typing/ParamsWitness` | 3480 | false |
| `VEnv.appParams` | `Theory/Typing/PatAppParams` | 5220 | false |
| `VEnv.propLoopParamsOfWF` | `Theory/Typing/ParamsWitness` | 6543 | false |
| `cycParams` | `Theory/Typing/ParRedCycle` | 6546 | false |
| `refParams` | `Theory/Typing/DescendRefute` | 6549 | false |
| `MutField.declParams` | `Theory/Typing/ParamsStruct` | 6931 | **true** |
| `MutField.unitParams` | `Theory/Typing/ParamsStruct` | 6946 | **true** |
| `VEnv.quotParams` | `Verify/QuotAppParams` | 9265 | **true** |

### §2.4 P4, P7, P12 scored — and FINDING D: the "right statement" is already in the tree

* **P4 CONFIRMED.** `VEnv.NormalEq` (`ChurchRosser.lean:165`) has a `proofIrrel` constructor:
  `Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ₚ h'`. `CRDefEq`'s third conjunct is
  `∃ e₁' e₂', e₁ ≫* e₁' ∧ e₂ ≫* e₂' ∧ e₁' ≡ₚ e₂'`, so the joining relation **already** quotients
  by proof irrelevance, and `CRDefEq` is already a *joinability* statement, not a
  syntactic-identity one. The brief's proposed repair is present in the object it proposes to
  repair.
* **P12 SCORED — no such variant exists.** `grep` over `--include=*.lean --include=*.md` for
  `CRDefEqK|CRStatementK|crStatementK|CRStatementUpToProof|UpToProof|crUpToProof|CRProp|ProofQuotient`
  returns **only this handoff file's own §1**. So neither a proof-quotiented nor a K-closed
  `Prop`-level confluence statement is stated anywhere in the tree. (Checked against method
  rule 3: this is a *shape*-negative too — see §2.6.)
* **P7 CONFIRMED, and more strongly than I predicted.** `Theory/Typing/KEta.lean` already
  contains the reduction relation *and the verdict*:

  `VEnv.ParRedK` (arity 4, `KEta.lean:341`) is `ParRed` plus one constructor
  `keta : EtaK Γ e w → ParRedK Γ w w' → ParRedK Γ e w'`, with `ParRedKS := ReflTransGen (ParRedK Γ)`,
  `ParRed.toK`, `ParRedK.hK : KStep Γ a b → ParRedK Γ a b`. And:

  ```
  theorem not_crStatement_of_kstep_dead
      (he : Γ ⊢ e : .forallE A B) (hstep : KStep (A::Γ) (.app e.lift (.bvar 0)) t)
      (hlam : ∀ A' e', e ≠ .lam A' e') (hrig : ∀ o, ParRedK Γ e o → o = e) : False :=
    hlam A t (hrig _ (.keta (.under he (.here hstep)) .rfl)).symm
  ```

  Its docstring: *"Four of its eleven hypotheses are already contradictory: `he`, `hstep`,
  `hlam`, `hrig`. The other seven — including `hne`, the `NormalEq` gap that §S3 and §S4
  identify — are not needed, which is the precise sense in which the repair belongs to the
  reduction relation and not to `NormalEq`."*

  So the tree's own answer to "what is the right confluence statement" is **confluence over
  `ParRedK`**, and it is not a proof-irrelevance quotient. What is *missing* is that nobody has
  written the statement down as a `Prop` and shown it survives at `quotParams` — that gap is what
  `CRShape.lean` fills.

  Note the docstring says **eleven** hypotheses where `exists.lean` measures arity **18**; the
  eleven are the *explicit* binders. Not an error, but the two numbers are both in the tree
  meaning different things, and the brief's "eighteen binders" is the arity.

### §2.5 FINDING E — the discriminator is NOT "a `Prop`-typed position". Measured, two ways.

The brief's hypothesis (a) — every refutation routes through a `Prop`-typed / proof-irrelevant
position — is **true but does not discriminate**, and the tree already contains the proof that it
does not.

`appParams` (`PatAppParams.lean`) fires the *same* K⁺ step through the *same* rule: a variable
major premise of the `Prop` `P`, made definitionally equal to the constant proof `D` by proof
irrelevance (`appParams_stuck_fires`). And `CRStatement` is **not** refutable there:

```
/-- …the reason is the same one, in its sharpest form: **every `K⁺` step whose major premise is a
proof of `P` is already a `NormalEq`**, so the `hne` that refutation needs is unsatisfiable here. -/
theorem appParams_normalEq_of_kstep (hΓ) (hh : cycEnv.HasType 0 Γ h (.const `P []))
    (hstep : KStep Γ (.app f h) t) : NormalEq Γ (.app f h) t
theorem appParams_no_crStatement_refutation … (hne : ¬ NormalEq …) : False
```

At `quotParams` the major premise is *also* a proof (`.bvar 0 : Quot.{0} α r`, a `Prop`) and the
step *also* fires by `IsDefEq.proofIrrel` (`quotParams_kstep_eta`) — yet
`not_normalEq_redex_rhs : ¬ NormalEq qc0 (.app (qLift 0 1) (.bvar 0)) (.app (.bvar 3) (.bvar 1))`
holds. So "the major premise is a proof" is satisfied at both and decides nothing.

**What actually decides it** is whether the rule's right-hand side is `NormalEq` to the redex:

| | `appParams` | `quotParams` |
|---|---|---|
| K⁺ step fires by proof irrelevance | yes | yes |
| major premise is a `Prop`-typed variable | yes | yes |
| rule's RHS | `appPat_rhs_eq`: the **closed** terms `cycG`/`cycG2` — the rule *permutes a proof* | `quotRHS = g x`, **depends on the matched argument** (`quotRHS_depends_on_match`) — the rule *computes*, discarding the eliminator head |
| redex `≡ₚ` contractum | **yes** (`appDF` + `proofIrrel` on the proof argument) | **no** (`not_normalEq_redex_rhs`) |
| `hne` satisfiable | no | yes |
| `CRStatement` refuted | **no** | **yes** (modulo §2.2's two holes) |
| result type of the redex | `T : Type` | `β : Type 0` (`B = .bvar 4`, `v = .succ .zero`) |

So the failure boundary is **rule contractivity, not `Prop`-ness**: `appParams`' table is
degenerate (both right-hand sides are closed and mutually `NormalEq`, which its own docstring flags
as "a weak test of M3"), and a *real* ι/quotient rule is not. `quotParams` is the generic case.

**Consequence for hypothesis (b), and it is fatal.** A proof-irrelevance quotient is exactly what
already makes the degenerate instance safe (`NormalEq.appDF` + `NormalEq.proofIrrel`). It cannot
help at the contractive instance, because the two divergent terms there are *not proofs* — the
refutation feeds `hnp := qLiftT0_not_proof`, i.e. **"`e` is not a proof" is a hypothesis of the
refutation, not a conclusion.** Quotienting the conclusion by proof-ness therefore leaves the
refutation standing verbatim. That is §3's theorem.

### §2.6 Consumer-side availability, measured before pricing (P9's inputs)

`Verify/Typing/ConstSpine.lean`'s three consumers of `IsDefEq.church_rosser` all use the same
three-line pattern: `obtain … := H.church_rosser hΓ` then one or two *reduction inversion* lemmas
then a `NormalEq` lemma. Over `ParRedKS` those inversions are:

| needed | exists? | where |
|---|---|---|
| `ParRedKS.constApp_inv` | **yes** | `Theory/Typing/DescendConstSpineK.lean:120` |
| `ParRedK.forallE_inv` | **yes** | `Theory/Typing/KEta.lean:454` |
| `ParRedK.sort_inv` | **yes** | `Theory/Typing/KEta.lean:462` |
| `ParRedKS.forallE_inv` | **NO** | — (only the single-step form) |
| `ParRedKS.sort_inv` | **NO** | — |
| `ParRedS.toKS` (`ParRedS ⊆ ParRedKS`) | **NO** | (`ParRed.toK` exists, `KEta.lean:360`) |
| `ParRedK.hasType` | **yes** | `KEta.lean:702` |
| `ParRedKS.hasType` | **NO** | — |
| `NormalEq.constApp_inv` / `_forallE` / `_sort` | **yes**, and **unchanged** — they are about `NormalEq`, which the K repair does not touch | `Verify/Typing/ConstSpine.lean:186,301,320` |

The three missing ones are reflexive-transitive closures of lemmas that exist; `CRShape.lean`
supplies them. **`ParRedS.toKS` is the load-bearing one**: it is what makes `CRStatementK` a
*weakening* of `CRStatement` rather than an incomparable statement.

Import route, checked (P11): `Verify.QuotAppParams`'s import closure (194 modules) already contains
`Verify.Typing.ConstSpine`, `Theory/Typing/{KEta, KCanonical, PatAppParams, Injectivity, PatKHead}`.
So `import Lean4Lean.Verify.QuotAppParams` + `import Lean4Lean.Theory.Typing.DescendConstSpineK`
suffices for everything above, and `Theory/Typing/ParamsCR.lean` is the standing precedent for a
`Theory/` module importing `Verify.QuotAppParams`.

### §2.7 FINDING F — HEAD does not build, and my own build attempt unmasked it

`lake build Lean4Lean.Theory.Typing.CRShape` fails at **`Lean4Lean/Verify/Environment/Checker.lean:86`**,
in `checkConstantValCore.WF`:

```
error: Type mismatch
  TypeChecker.M.WF.bind (TypeChecker.M.WF.liftExcept (checkNoMVarNoFVar.WF env ci.name ci.type))
    fun x x_1 x_2 hclosed => ?m.97
has type   TypeChecker.M.WF ?m.87 ?m.88 (liftM (env.checkNoMVarNoFVar ci.name ci.type) >>= ?m.90) ?m.92
but is expected to have type
  TypeChecker.M.WF … (do liftM (Environment.checkDuplicatedUnivParams …); liftM (env.checkNoMVarNoFVar …); …)
```

i.e. the third `refine` is being matched against a goal whose head statement is still
`checkDuplicatedUnivParams`, so the second `refine`
(`(TypeChecker.M.WF.liftExcept (Except.WF.trivial _)).bind`, whose `Except` action is a bare
metavariable) does not commit. Reproduced on its own: `lake build
Lean4Lean.Verify.Environment.Checker` → 162/162 jobs, same error, 1.4s.

* `Checker.lean` is **unmodified** at HEAD (`git status` clean apart from another stream's
  `ConfluenceRebuildPrice.lean` and my two files), and `git log` shows its last touch was
  `b58b248`. So this is a **pre-existing HEAD break**, not a regression from this round's edits.
* **But I made it visible, and I should say so plainly.** Before my build, a stale
  `Checker.olean` existed and every LSP session and `scripts/exists.lean` run loaded it happily —
  which is why `exists.lean` worked for my first measurement and threw `Boundaries.olean does not
  exist` for my second. My `lake build` judged `Boundaries`/`Checker` out of date, rebuilt
  `Boundaries.olean` (12:16) and **deleted `Checker.olean`, which it then could not rebuild.**
  Anything importing `Verify/Environment/Extension.lean` (the sole direct importer) is now
  un-loadable until `Checker.lean:86` is fixed. That includes `Verify/QuotAppParams.lean`.
* **Consequence for this round**: `quotParams` became unreachable mid-round. `CRShape.lean` is
  therefore built on the Checker-free closure (`PatAppParams` 74, `DescendConstSpineK` 72,
  `Verify.Typing.ConstSpine` 59 modules — none reaches `Checker`), and the four `quotParams`
  instantiations are recorded verbatim in the file's §2.2 rather than compiled. Their argument
  lists are `quotParams_not_crStatement`'s, unchanged, because `not_crUpToProof_of_kstep` takes
  `not_crStatement_of_kstep`'s hypotheses in the same order.
* **I did not edit `Checker.lean`** — it is not one of my two files. The diagnosis above is
  everything I have; the likely shape of the fix is to give `Except.WF.trivial`'s action
  explicitly (`Except.WF.trivial (Environment.checkDuplicatedUnivParams …)`) so the second
  `refine` cannot postpone, but **I have not tested that** and it should not be quoted as verified.

### §2.8 Corrections to my own §2.6 table (found by building, not by reading)

| §2.6 row | verdict | correction |
|---|---|---|
| `ParRedKS.hasType` "**NO**" | **WRONG** | it exists: `Theory/Typing/KMeasure.lean:851`, arity 8, cone 3712, holes `{forallE_inv_stratified, rigidShapeUniqNS}`. My draft re-proved it and Lean rejected the duplicate. The grep that produced the row searched `theorem ParRedKS.hasType` in `Theory/Typing/*.lean` and missed it because I ran the pattern list against a stale grep of *single-step* names. Method-rule-3 failure of my own making: I did the source grep but not `exists.lean` on that name. |
| `ParRedKS.forallE_inv`, `ParRedKS.sort_inv`, `ParRedS.toKS` "**NO**" | **right** | confirmed absent; supplied in `CRShape.lean`. |

### §2.9 What `CRShape.lean` proves — measured 2026-09-04, build **green** (93 jobs), file has **no `sorry`**

`python3 scripts/layer-check.py`: HARD RULE ok (66 SetModel modules, none reaches `Verify/`).
`CRShape` appears in both SOFT REPORTs with **1** Verify module (`Verify.Typing.ConstSpine`) — the
smallest entry of the thirteen; the next smallest is 30, `ParamsCR`'s is 51.

| declaration | arity | cone | holes in cone | `#print axioms` |
|---|---|---|---|---|
| `isDefEq_lam_of_kstep` | 11 | 3532 | `{forallE_inv_stratified}` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| **`not_crDefEq_of_kstep`** | 11 | 729 | **`{}`** | `[propext, Quot.sound]` |
| `CRUpToProof` | 1 | 40 | `{}` | `[propext, Quot.sound]` |
| `CRStatement.toUpToProof` | 2 | 43 | `{}` | `[propext, Quot.sound]` |
| **`not_crUpToProof_of_kstep`** | 18 | 3584 | `{forallE_inv_stratified}` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `KStepNormalEq` | 1 | 34 | `{}` | `[propext, Quot.sound]` |
| `no_crStatement_refutation_of_kstepNormalEq` | 9 | 161 | `{}` | `[propext, Quot.sound]` |
| **`ParRedS.toKS`** | 5 | 679 | `{}` | `[propext, Quot.sound]` |
| `CRDefEqK` | 4 | 16 | `{}` | `[propext, Quot.sound]` |
| `CRStatementK` | 1 | 37 | `{}` | `[propext, Quot.sound]` |
| `CRDefEq.toK` | 5 | 685 | `{}` | `[propext, Quot.sound]` |
| **`CRStatement.toK`** | 2 | 692 | `{}` | `[propext, Quot.sound]` |
| **`crDefEqK_of_kstep`** | 11 | 3554 | `{forallE_inv_stratified}` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `ParRedKS.forallE_inv` | 6 | 755 | `{}` | `[propext, Quot.sound]` |
| `ParRedKS.sort_inv` | 5 | 755 | `{}` | `[propext, Quot.sound]` |
| `IsDefEqU.constApp_forallE_false_ofK` | 10 | 3810 | `{forallE_inv_stratified, rigidShapeUniqNS}` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `IsDefEqU.constApp_sort_false_ofK` | 9 | 3629 | `{forallE_inv_stratified}` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `appParams_kStepNormalEq_at_proofMajor` | 7 | 5237 | **`{}`** | `[propext, Classical.choice, Quot.sound]` |
| `appParams_crDefEqK` | **0** | 5461 | `{forallE_inv_stratified}` | `[propext, sorryAx, Classical.choice, Quot.sound]` |

Reference points measured in the same run: `KStep.defeq` arity 6, cone 3529, holes
`{forallE_inv_stratified}` — **that is where every taint above comes from**, because K-step
admissibility is what `isDefEq_lam_of_kstep` uses; and `not_crStatement_of_kstep_dead` arity 10,
cone 162, holes `{}`.

**P5 SCORED — CORRECT in substance, PARTIAL in delivery.** `not_crUpToProof_of_kstep` is proved
(and, unlike the tree's composite, its joinability core `not_crDefEq_of_kstep` is **hole-free**).
The instantiation at `quotParams` is written and blocked by §2.7's build break, so it is not
machine-checked; `appParams_crDefEqK` (arity 0, a closed instance) is the compiled anti-vacuity
witness instead.

### §2.10 P9 SCORED — **WRONG**, and the consumers do better than survive

Prediction P9 (0.65) said `ConstSpine.lean` would **not** be served by a weakened statement.
Measured, in one run, same environment:

| consumer | cone | holes in cone |
|---|---|---|
| `IsDefEqU.constApp_forallE_false` (tree, via `IsDefEq.church_rosser`) | 4431 | `{weakN_iff, forallE_inv_stratified, rigidShapeUniqNS, NormalEq.descend}` — **4** |
| `IsDefEqU.constApp_forallE_false_ofK` (mine, via `CRStatementK` as a hypothesis) | 3810 | `{forallE_inv_stratified, rigidShapeUniqNS}` — **2** |
| `IsDefEqU.constApp_sort_false` (tree) | 4429 | same **4** |
| `IsDefEqU.constApp_sort_false_ofK` (mine) | 3629 | `{forallE_inv_stratified}` — **1** |
| `IsDefEq.constApp_inv` (tree, the critical-path one) | 4446 | same **4** |
| `ParRedKS.constApp_inv` (the K-side inversion it would use) | 803 | **`{}`** |

The statements are unchanged and the proofs are unchanged except that `ParRedS.constApp_inv`/
`ParRedS.forallE_inv`/`ParRedS.sort_inv` become the `ParRedKS` ones. So **the weaker statement
serves the consumers, verbatim.**

The honest reading of the hole drop, which is the part that matters: taking confluence as a
*hypothesis* obviously removes the holes in its *proof*, so 4 → 2 is not free progress. What it
measures is **where those holes actually enter**:

> `IsDefEqU.weakN_iff` and `NormalEq.descend` reach `ConstSpine.lean`'s consumers **only through
> the proof of confluence, never through its statement or through the reduction inversions.**
> `forallE_inv_stratified` and `rigidShapeUniqNS` enter twice over — through confluence *and*
> independently through `IsType.not_isProof` / `HasType.forallE_inv` / `ParRedKS.hasType`.

That is a sharp hole-accounting fact and it is the one thing here that changes the critical-path
picture: proving `CRStatementK` would retire `NormalEq.descend` and `IsDefEqU.weakN_iff` from the
`ConstSpine` route, and would **not** retire the other two.

### §2.11 Two docstring defects, per method rules 4 and 5

1. **`docs/handoff-nested-build.md:280`** — "*proof needs `IsDefEqU.forallE_inv`
   (`Typing/Injectivity.lean`, **open**)*". Measured today: `IsDefEqU.forallE_inv`, arity 10,
   cone 3574, **`own value is a hole: false`**, holes in cone
   `{forallE_inv_stratified, rigidShapeUniqNS}`. It is a theorem standing on two holes, not an
   open node — the exact error the brief says cost three rounds this week. Flagged, not edited
   (not my file).
2. **`Lean4Lean/Theory/Typing/KSite7.lean:118`** — "*As always: no `Params` instance in this tree
   registers an `.app` pattern, so `hin` has no witness here, and that is **not** evidence of
   truth.*" The absence claim is false since 2026-09-01: `PatAppParams.appParams` and
   `VEnv.quotParams` both register `.app` patterns. Note that **the same sentence has already been
   corrected in two other files** — `KEta.lean:884` ("*The parenthetical … was stale and is
   removed*", citing vacuity-ledger row 96) and `ParamsCR.lean:376` ("*a **stale absence
   claim***"). `KSite7.lean` is the last holdout. The surrounding warning ("not evidence of
   truth") is still sound; only its reason is stale.

---

## §3 VERDICTS

### §3.1 The failure boundary, across all eight closed `Params` instances

`not_crStatement_of_kstep` (arity 18) needs, in order: `hΓ hΓA hA he hstep hlam hnp hrig hrigA
hrigT hne`. Only two of the eleven explicit ones ever decide the outcome — **`hstep`** (is there a
K⁺ step at a variable major premise under an `eta`?) and **`hne`** (is the redex *not* `NormalEq` to
the contractum?). The table is those two columns.

| instance | rule table | `hstep` satisfiable? | `hne` satisfiable? | `CRStatement` | **the discriminating feature** |
|---|---|---|---|---|---|
| `refParams` | **empty** (`refNoPat`) | **no** — `refParams_no_kstep` (`KDescend.lean:402`) | n/a | not refutable, **vacuously** | no rule at all |
| `cycParams` | empty (`cycNoPat`, cited from `PatAppParams.lean`'s item 1, not re-measured) | no | n/a | not refutable, vacuously | no rule at all |
| `propLoopParams` | two **δ**-rules, both `.const` patterns (`PropLoopParams.Pat`'s `.app` case is literally `False`) | **no** — `KStep` requires `Pat (.app p₁ p₂) r` | n/a | not refutable | **no ι-rule**: δ-rules have no major premise |
| `propLoopParamsOfWF` | same environment via `paramsOfWF` | no | n/a | not refutable | same |
| `MutField.declParams` | ι-rules of a two-member structure block | **no — and `hstep` is FALSE, not unproved** (`ParamsCR.lean` §7, `declParams_not_crStatement_of_kstep_hyps_absurd`; only `hΓA` and `hstep` consumed) | untested | not refutable | **the major premise's type is not a `Prop`**: both members live in `Type 0`, so proof irrelevance — the only rule identifying a variable with a constructor spine — is unavailable, and a fresh axiom inhabitant refutes the conversion outright |
| `MutField.unitParams` | ι-rule of a one-member block | same route, same reason (`unitParams` is `paramsOfWFAx unitEnv_wf 0`, same `Type 0` situation) — **not re-measured this round** | untested | not refutable | same |
| `VEnv.appParams` | **two `.app` ι-patterns**, `cycQ = C D` / `cycQ2 = C D2` over `P : Prop` | **yes** — `appParams_stuck_fires`, K⁺ fires at `.app (.const C) (.bvar 0)` **by proof irrelevance** | **no — `hne` is FALSE** (`appParams_normalEq_of_kstep`, `appParams_no_crStatement_refutation`) | not refutable | **the rule is degenerate**: both right-hand sides are the *closed* terms `cycG`/`cycG2` (`appPat_rhs_eq`), so redex and contractum differ only in a proof argument and `NormalEq.appDF` + `NormalEq.proofIrrel` joins them |
| `VEnv.quotParams` | the **quotient** rule, `Quot.lift` at `u = 0`, `v = 1` | **yes** — `quotParams_kstep_eta`, K⁺ fires at `.app (qLiftT 0 1).lift (.bvar 0)` **by proof irrelevance**, the major premise being `.bvar 0 : Quot.{0} α r`, a `Prop` | **yes** — `not_normalEq_redex_rhs` | **REFUTED**, modulo `{forallE_inv_stratified, rigidShapeUniqNS}` (§2.2) | **the rule computes**: `quotRHS = g x` depends on the matched argument (`quotRHS_depends_on_match`), discarding the eliminator head, and the two results live in `Type 0` — large elimination of a subsingleton |

Reading the table by column rather than by row is the finding:

* **`hstep` fails ⇔ the environment has no ι-rule whose major premise slot is `Prop`-typed.** Six
  of eight instances die here, and at `declParams`/`unitParams` the reason is *exactly* the brief's
  hypothesis (a): no `Prop`, no proof irrelevance, no variable-to-constructor conversion.
* **`hne` fails ⇔ the rule is degenerate.** This column is invisible to hypothesis (a): `appParams`
  and `quotParams` are identical in the `hstep` column and opposite in the `hne` column.

So `Prop`-routing is **necessary** for the failure and **not sufficient**. Contractivity of the
rule is the second, independent condition, and it is the one a repair has to address.

### §3.2 The verdict on the hypothesis, and the right statement

**Hypothesis (a) — right, and now sharp.** Every refutation in the tree fires its K⁺ step through
proof irrelevance at a `Prop`-typed major premise, and `ParamsCR.lean`'s `kstep_bvar_ctorConv`
shows that is forced: a K⁺ step at a variable major premise *is* the demand that a variable be
definitionally equal to a constructor spine, at every instance. Where the type is not a `Prop` that
demand is refutable, which is why `declParams` is safe.

**Hypothesis (b) — wrong, three ways, and this is the round's main result.**

1. **The quotient is already in the statement.** `NormalEq` has a `proofIrrel` constructor and
   `CRDefEq`'s third conjunct joins *reducts* by `NormalEq`. `CRStatement` is already
   joinability-up-to-proof-irrelevance. There is nothing to add.
2. **The proposed quotient is what makes the *degenerate* instance safe, not the failing one.** At
   `appParams` the join is literally `NormalEq.appDF` over `NormalEq.proofIrrel`. So the repair is
   already doing all the work it can do, at the instance that did not need repairing.
3. **A conclusion-level proof-irrelevance escape clause is refuted at the same witness.**
   `CRUpToProof` weakens `CRStatement`'s conclusion to
   `CRDefEq Γ e₁ e₂ ∨ IsProof … e₁ ∨ IsProof … e₂ ∨ HasType … A (.sort .zero)`
   (`CRStatement.toUpToProof` checks it *is* a weakening), and
   `not_crUpToProof_of_kstep` derives `¬ CRUpToProof` from `not_crStatement_of_kstep`'s own
   hypothesis list, unchanged. All three escape clauses die on `hnp` — "`e` is not a proof" — which
   the refutation **already assumes** and which `qLiftT0_not_proof` discharges at `quotParams`.
   Concretely: the divergent pair at `quotParams` is a `Quot.lift` spine and a λ, both of type
   `Quot.{0} α r → β` with `β : Type 0`; neither is a proof and the equation's type is not a `Prop`.

**The right statement is confluence over `ParRedK`** — `ParRed` plus the η-guarded K step — and it
was already the tree's answer (`KEta.lean`'s `not_crStatement_of_kstep_dead`, cone 162, hole-free).
This file writes it down (`CRDefEqK`, `CRStatementK`), checks it is a genuine weakening
(`ParRedS.toKS`, `CRDefEq.toK`, `CRStatement.toK` — all hole-free), and supplies the positive half
the tree did not have:

> **`crDefEqK_of_kstep`**: at exactly the configuration that refutes `CRStatement`, `CRDefEqK`
> **holds**, from four typing hypotheses and in one `keta` step. The old statement fails there for
> want of a *reduction step*, not for want of a *quotient*.

Anti-vacuity: `appParams_crDefEqK` is a closed instance (arity 0) of that theorem.

### §3.3 Consumers — **served**, and see §2.10 for the numbers

`Verify/Typing/ConstSpine.lean`'s consumers re-run over `CRStatementK` with **unchanged statements
and unchanged proofs**, substituting the `ParRedKS` inversions for the `ParRedS` ones
(`IsDefEqU.constApp_forallE_false_ofK`, `IsDefEqU.constApp_sort_false_ofK`, both compiled here).
The three inversions they need all exist over `ParRedKS`: `constApp_inv` (`DescendConstSpineK`,
cone 803, hole-free), and `forallE_inv`/`sort_inv` (new here, cone 755, hole-free). The `NormalEq`
lemmas they finish with are untouched, because the K repair does not touch `NormalEq`.

`ParRed.constApp_inv` — the third `ParRed`-casing declaration, and the one `KEta.lean` §T5 flagged
as needing an edit — is already covered by `ParRedKS.constApp_inv`, so **no consumer is left
without a K-side counterpart.** P9 is scored WRONG.

### §3.4 The three holes — **NO for all three, and here is why**

| hole | does a corrected confluence statement reach it? | why |
|---|---|---|
| `IsDefEqU.forallE_inv_stratified` (arity 16, cone 48, own value a hole) | **No — the dependency runs the other way, and it is circular.** | It is *upstream*: `KStep.defeq` (cone 3529) is tainted by it, so **every** K⁺ step's admissibility already depends on it, and therefore so do `isDefEq_lam_of_kstep`, `crDefEqK_of_kstep`, `not_crUpToProof_of_kstep` and the existing `quotParams_not_crStatement`. Worse, `KEtaDiamond.piDomAgree_tree` — the extra hypothesis `EtaKDiamond` needs — costs *exactly* `{forallE_inv_stratified, rigidShapeUniqNS}` (`KEta.lean`'s Round-6 note). So proving `CRStatementK` **consumes** this hole rather than producing it. |
| `WF.rigidShapeUniqNS` (arity 3, cone 630, own value a hole) | **No**, same shape. | Same `piDomAgree_tree` citation; and it enters `ConstSpine`'s consumers independently of confluence, via `IsType.not_isProof` / `ParRedKS.hasType` (§2.10). A confluence statement cannot discharge a hole its own proof needs. |
| `IsDefEqU.weakN_iff` (arity 11, cone 3231, own value a hole) | **No, and for a different reason — but there is real news.** | It is not a confluence consequence; it is a weakening/context lemma. What §2.10 measures is that it, together with `NormalEq.descend`, reaches `ConstSpine.lean`'s consumers **only through the current proof of `IsDefEq.church_rosser`** — `constApp_forallE_false_ofK`'s cone does not contain either. So a proof of `CRStatementK` would **retire `weakN_iff` and `NormalEq.descend` from the `ConstSpine` route**, without proving them. That is a hole-*routing* win, not a hole-closing one, and it is the only movement this round found on the three. |

**So the audit's framing needs a correction.** `docs/audit-hole-producers.md` says three of five open
holes "bottom out in normalisation/confluence for the conversion relation". Two of them
(`forallE_inv_stratified`, `rigidShapeUniqNS`) are better described as **what confluence bottoms
out in**: they are Π-injectivity facts that the K⁺ step's own admissibility already consumes.
Confluence is downstream of them, not upstream. The third (`weakN_iff`) is upstream of the current
*proof* and not of the statement, so it moves when the statement changes.

P10 is scored **half right**: I predicted "reaches the first two, not `weakN_iff`". The measurement
is the reverse — none is closed, and the only one that *moves at all* is `weakN_iff`.

### §3.5 Prediction scorecard (§1.2, never edited)

| # | P | verdict |
|---|---|---|
| P1 | 0.80 | **WRONG** — there are exactly eight closed instances (§2.3) |
| P2 | 0.80 | **RIGHT**, but not discriminating (§2.5, §3.1) |
| P3 | 0.90 | **RIGHT** — and proved, `not_crUpToProof_of_kstep` |
| P4 | 0.95 | **RIGHT** — `NormalEq.proofIrrel` |
| P5 | 0.75 | **RIGHT in substance, PARTIAL in delivery** — general theorem compiled, `quotParams` instantiation blocked by §2.7 |
| P6 | 0.75 | **RIGHT** — `ParRed.extra` matches syntactically, `KStep` up to conversion |
| P7 | 0.85 | **RIGHT, and stronger** — `ParRedK` *and* the verdict were already in `KEta.lean` |
| P8 | 0.60 | **RIGHT in outcome, wrong in mechanism** — commit `a561fa9` refutes `KDiamond` and M3 for demanding `NormalEq` of reducts *on the nose* (the repair is a restatement to joinability, and `quotParams_kDiamond_joinable` shows the reducts *are* joinable), not because K-closure is the wrong axis |
| P9 | 0.65 | **WRONG** — consumers are served verbatim, at lower hole cost (§2.10) |
| P10 | 0.55 | **HALF** — none of the three is reached; the one that moves is the one I said would not (§3.4) |
| P11 | 0.95 | **RIGHT** but moot — `Verify.QuotAppParams` became un-loadable (§2.7); the file cites `Verify.Typing.ConstSpine` instead, 1 Verify module, the smallest of the thirteen |
| P12 | 0.30 | **RIGHT** (no such variant existed) |
| P13 | 0.60 | **RIGHT** — two found (§2.11) |
| P14 | 0.90 | **RIGHT, and sharpened** — *both* sides are tainted, which is finding C |

Calibration note: I was over-confident on the two predictions about *other people's* work
(P1, P9) and correctly confident on the ones about the mathematics (P3, P4, P6, P7). Both misses
were cases where I predicted the tree was weaker than it is. That is the same direction as the
brief's own standing complaint about stale-absence claims, and it is worth me noticing.

### §3.6 Limits of this round's result, stated and where possible proved

1. **`CRStatementK` is not proved.** Its price is `EtaKDiamond` (`KEta.lean`), and
   `KEtaDiamond.etaKDiamondAt_of_kDiamond` shows the base case is `KDiamond` **verbatim** — which
   commit `a561fa9` refutes at `quotParams`, and whose repair (restatement to joinability) is
   another stream's. So §3.2's "right statement" is the right *shape*; its provability is open and
   is **circular with two of the three holes** (§3.4).
2. **The `quotParams` refutation of `CRUpToProof` is not machine-checked**, only the general
   theorem it instantiates. Cause is §2.7's build break, not a gap in the argument; the argument
   list is `quotParams_not_crStatement`'s verbatim.
3. **`CRUpToProof` is one formulation of "up to proof irrelevance", not all of them.** I refute the
   *conclusion-weakened* form. I do **not** refute a form that quotients the syntax of terms by
   proof-erasure before comparing, because no such relation exists in this tree and building one is
   a different round. I record why I expect it to fail all the same: at `quotParams` the two
   divergent terms differ in their *heads* (a `Quot.lift` spine vs a λ over `g x`), not in a proof
   subterm, so an erasure quotient has nothing to erase. That expectation is **not proved.**
4. **`unitParams`' row in §3.1 is inherited, not measured.** I assert it follows `declParams`'
   route because it is `paramsOfWFAx unitEnv_wf 0` over a `Type 0` block; I did not run the
   argument. Likewise `cycNoPat` is cited from `PatAppParams.lean`'s docstring.
5. **The `declParams` row carries `ParamsCR.lean` §8's own limit**: the Π-domain is pinned
   *syntactically* (`hAmem`), so what is refuted is the route at a syntactically-named domain, not
   at every domain convertible to one.
6. **My own §2.6 table was wrong about `ParRedKS.hasType`** (§2.8) — a measurement I claimed from a
   grep and did not check with `exists.lean`. Corrected in place, in §2.8, not in §2.6.

### §3.7 Method gaps

* I ran `scripts/exists.lean` and `scripts/shape.lean`-style structural queries before every
  absence claim **except one** (`ParRedKS.hasType`), and that one was wrong. The rule works; the
  exception proves it.
* `scripts/can-cite.py` I did **not** run: it invokes `exists.lean` per declaration and
  `exists.lean` was broken by §2.7's missing oleans for most of the round. I substituted a direct
  import-closure computation in Python (same algorithm as `can-cite.py`'s `closure`) and
  `scripts/layer-check.py`, which does run. So the citability claims are measured, but by a
  reimplementation rather than by the sanctioned script.
* Two measurements I would have made with more time: whether `KStepNormalEq` holds at `appParams`
  for *every* K-step rather than only proof-typed major premises (I proved only the latter, which
  is `appParams_normalEq_of_kstep` restated), and the `unitParams` row.
