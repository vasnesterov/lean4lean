# The `Stratified` package's nine `sorry`s: there are none

Audit of the eight files `Theory/Typing/{Stratified, CycleConv, SortClauses, SortRedApp,
PropConv, AppCase, RegPiSat, StrengthenWitness}.lean`, commissioned as "inventory the 9
`sorry`s, close what you can, refute what is false".

**Headline: the brief's premise is wrong.  None of those eight files contains a `sorry`.**
Together they hold **617 declarations**, of which **exactly one** is `sorryAx`-tainted, and
that one is also a tautology.  The real finding is a different defect, in a different place,
and it is fixed below.

Everything in §§1–4 is machine-checked at commit `3e13a0f` (plus the `StrengthenWitness.lean`
edit of §4) unless a line says "read off source".

---

## 0. The two answers that were asked for first

### `CycleConv.propLoopEnv` **is** well formed — the witness exists

> *"If `propLoopEnv` is not actually well-formed, a large amount of recent work is resting on
> a witness that does not exist."*

It is well formed, and it is proved, not assumed:

```
'Lean4Lean.propLoopEnv_wf'            depends on axioms: [propext, Quot.sound]
'Lean4Lean.propLoop_wf'               depends on axioms: [propext, Quot.sound]
'Lean4Lean.propLoop_isProp'           depends on axioms: [propext, Quot.sound]
'Lean4Lean.propLoop_headStep_not_wf'  depends on axioms: [propext, Quot.sound]
'Lean4Lean.loopEnv2_wf_noUnsafe'      depends on axioms: [propext, Quot.sound]
```

`propLoopEnv_wf : propLoopEnv.WF` is `⟨_, .decl propLoop_wf .empty⟩` — one `.unsafeDef` step
from `VEnv.empty`, with both members' types and both defining equations discharged inline
(`CycleConv.lean:210–219`).  No hypothesis, no `sorry`, no taint.  The non-vacuity evidence in
`SortClauses.lean`, `SortRedApp.lean`, `RegPiSat.lean`, `StrengthenWitness.lean` and
`ParamsWitness.lean` that rests on this environment is **standing**.

`CycleConv.lean` itself is `sorry`-free (38 declarations, `[propext, Quot.sound,
Classical.choice]`).  Its one *open* item is a **hypothesis, not a hole**:
`propLoop_no_direct_collapse` takes `propLoopEnv.SortUniq U` as an argument, and the file's
own docstring already says so.  That is the honest shape and needs no repair.

### `Stratified.lean` is `sorry`-free, and `Stratified.uniq` / `HasTypeN.uniq` do not exist

69 declarations, axioms `[propext, Quot.sound]`, zero taint.  The brief warned that
`Stratified.uniq` and `HasTypeN.uniq` are "known void" through the refuted `DefInv` clause (2)
and that a restatement, not a proof, would be the deliverable.  **Neither name exists anywhere
in the tree.**  The only near-match is `HasTypeN.uniq_zero` — uniqueness of `⊢₀` typing — which
is a different, proved statement (`⊢₀` conversion is syntactic equality, so `⊢₀` types are
syntactically unique).  There is nothing to restate.

---

## 1. Machine-checked inventory

`collectAxioms` sweep over every non-internal declaration of the eight modules
(script form retained in the report; re-runnable as a `#eval` over
`env.getModuleIdx?` + `collectAxioms`):

| file | decls | axioms | `sorryAx`-tainted |
|---|---:|---|---:|
| `Stratified.lean` | 69 | propext, Quot.sound | 0 |
| `CycleConv.lean` | 38 | + Classical.choice | 0 |
| `SortClauses.lean` | 115 | + Classical.choice | 0 |
| `SortRedApp.lean` | 109 | + Classical.choice | 0 |
| `PropConv.lean` | 82 | + Classical.choice | 0 |
| `AppCase.lean` | 93 | propext, Quot.sound | 0 |
| `RegPiSat.lean` | 90 | + Classical.choice | 0 |
| `StrengthenWitness.lean` | 21 | + Classical.choice, **sorryAx** | **1** |

Every axiom seen is on `Guard.lean`'s whitelist.  A literal `grep` for `sorry` in the eight
files returns only the word inside doc-comments ("sorry-free").  `lake build` of the eight
targets emits no `declaration uses 'sorry'` warning for any of them.

The single tainted declaration is
`VEnv.propLoopEnv_piDescend_sortDescend_fires` (`StrengthenWitness.lean`), tainted through
`Strengthen.PiDescend.sortDescend` → `IsDefEqU.forallE_inv` and `IsDefEq.uniq`
(`Theory/Typing/Injectivity.lean`, `Theory/Typing/UniqueTyping.lean` — **not** files this
stream owns).

### The brief's nine, item by item

| brief's claim | actual |
|---|---|
| `Stratified.lean` — 2 `sorry`s | 0.  69 decls, clean. |
| `CycleConv.lean` — 1 | 0.  One open *hypothesis* (`SortUniq`), documented at its use. |
| `SortClauses.lean` — 1 | 0.  115 decls, clean. |
| `SortRedApp.lean` — 1 | 0.  109 decls, clean. |
| `PropConv.lean` — 1 | 0.  82 decls, clean. |
| `AppCase.lean` — 1 | 0.  93 decls, clean. |
| `RegPiSat.lean` — 1 | 0.  90 decls, clean. |
| `StrengthenWitness.lean` — 1 | 0 `sorry`; 1 *inherited* taint, and a worse defect — §4. |

The brief's supporting claims about `Stratified.uniq`/`HasTypeN.uniq` being void, and about
`propLoopEnv`'s well-formedness being in doubt, are both wrong; see §0.  Its claim that
`SortRedAppDF ∅ 1 0` is an equivalence rather than a weakening, and that the spine
generalisation is false, are both correct and both machine-checked in the tree
(`empty_chain`, `spineInv_one_false`).

---

## 2. The defect that is actually there: `StrengthenWitness.lean`'s five witnesses are tautologies

Every "non-vacuity witness" in `StrengthenWitness.lean` has the form `OpenStatement → C`.
**Each of those `C` is provable outright, without the hypothesis.**  Machine-checked, all
`[propext, Quot.sound]`:

| `_fires` theorem | its conclusion, proved with no hypothesis |
|---|---|
| `propLoopEnv_sortDescend_fires` | `⟨_, propLoopEnv_hA⟩` |
| `propLoopEnv_piDescend_fires` | `⟨_, _, .lamDF (.sortDF trivial trivial rfl) (.bvar .zero), propLoopEnv_hA⟩` |
| `propLoopEnv_piDescend_sortDescend_fires` | same as the first |
| `propLoopEnv_typingStrengthening_fires` | `⟨_, propLoopEnv_hA⟩` |
| `propLoopEnv_trans_strengthening_fires` | `⟨_, propLoopEnv_AB⟩` |
| `propLoopEnv_strengthening_fires` | `⟨_, propLoopEnv_AB⟩` |

So **no `_fires` statement certifies anything about its hypothesis.**  The premise discharge
does happen — inside the proof term, where the elaborator checked
`HS (n := 1) (k := 0) propLoopEnv_W trivial propLoopEnv_onCtx …` — but it is invisible in the
statement, so the witness would evaporate silently under any re-proof.  This is the same
failure mode as commit `ce760c0` ("the strengthening capstone was a TAUTOLOGY"), and it was
present in this file from its first commit.

It also means the one `sorryAx`-tainted declaration in the whole package currently carries
**zero information**: it is tainted *and* tautological.

**Scope of the finding.**  I checked every other `_fires` theorem in the tree
(`SortClauses.lean:116`, `SortRedApp.lean:429,435,669`, `RegPiSat.lean:277`,
`ParamsWitness.lean:157,162,171,183`).  None has the defect: they are all **unconditional**
statements that apply a *proved* theorem, not an open hypothesis.  The defect is confined to
`StrengthenWitness.lean`, and the reason is structural — it is the only witness file whose
subject statements are all still open.

`ParamsWitness.propLoopEnv_church_rosser_fires` is `sorryAx`-tainted and its conclusion is
proved sorry-free two lines above it (`propLoopEnv_crDefEq_fires`), so it too carries no
statement-level information — but its docstring says exactly that, so it is honest, and it is
not this stream's file.

---

## 3. Two independent defect sweeps that came back clean

* **Unused hypotheses.**  A `MetaM` sweep over all 617 declarations, checking each leading
  explicit `Prop`-typed binder against the proof term's loose-bvar occurrences, found two
  hits, both benign: `PropConv.propNotProof_appCase_ih_vacuous` (whose *point* is that the
  induction hypotheses are unnecessary — it is the companion test) and
  `RegPiSat.defEqTypeN_single` (already underscore-marked `_h3`).  No accidental vacuity.

* **Unwitnessed statements.**  Of the 52 `Prop`-valued statement definitions declared across
  the eight modules, every one is either satisfied at some instance, or refuted, or is an open
  residual named as such.  Spot-verified by construction, all `[propext, Quot.sound]` (+
  `Classical.choice` where noted):

  ```
  propLoopEnv.EnvReg 1 0            := EnvReg.of_constPropType propLoopEnv_constPropType
  (∅ : VEnv).SortRedAppDFVar 1 0    := sortRedAppDFVar_vacuous .empty
  propLoopEnv.SortRedAppDFVar 1 0   := sortRedAppDFVar_vacuous propLoopEnv_wf.ordered
  (∅ : VEnv).AppNotProof 1 0        := AppNotProof.iff.2 PropNotProof.AppCase.zero
  (∅ : VEnv).AppPropAgree 1 0       := AppPropAgree.iff.2 PropTypeAgree.AppCase.zero
  (∅ : VEnv).PiTypedNotSortRed 1 0  := PiTypedNotSortRed.zero .empty
  (∅ : VEnv).ProofNotSortRed 1 0    := ProofNotSortRed.zero .empty
  ¬ (∅ : VEnv).RegPi 1 0            := regPi_false          -- refuted, as documented
  ¬ propLoopEnv.RegPi 1 0           := regPi_false          -- refuted, as documented
  ```

  The only statements with no instance at any index are the open residual family
  `SortRedAppDF` / `SortRedAppDF'` / `SortRedAppDFSort` / `SortRedLamExpose`, which is one
  statement in four equivalent forms (§5), and `SpineInv`, which is refuted
  (`spineInv_one_false`).

---

## 4. What was changed

`Lean4Lean/Theory/Typing/StrengthenWitness.lean` only.  Additive: nothing was deleted or
renamed, so `docs/handoff-weakn.md` §7's names all still resolve.  Builds clean; the module
went 11 → 21 declarations and is still exactly 1 tainted (the same one).

* **§3, new — the premises, as statements.**  `propLoopEnv_sortDescend_premises`,
  `propLoopEnv_piDescend_premises`, `propLoopEnv_strengthening_premises` each assert the
  *literal premise list* of the corresponding definition in `Strengthen.lean`, at the exact
  instantiation `n = 1`, `k = 0`, `Γ = []`, `Γ' = [A]` the `_fires` theorems use.  These are
  the theorems to quote for non-vacuity: none of them mentions the open statement, so none of
  them can be a tautology about it.  All `[propext, Quot.sound]`.
  Plus `propLoopEnv_liftA` / `_liftB` / `_liftId`, the three `liftN 1 0`-is-the-identity facts
  that make those statements readable against `Strengthen.lean`'s `e.liftN n k` premises.

* **§4, new — the tautology, certified.**  `propLoopEnv_sortDescend_concl_free`,
  `propLoopEnv_piDescend_concl_free`, `propLoopEnv_typingStrengthening_concl_free`,
  `propLoopEnv_strengthening_concl_free`: each `_fires` conclusion, proved with no hypothesis.
  The defect is now machine-checked in the file rather than discoverable only by trying it.

* **Docstring** rewritten to state the correction, to record that
  `propLoopEnv_piDescend_sortDescend_fires` is `sorryAx`-tainted *and* tautological, and to
  explain why no non-tautological implication exists at this witness:

  > A witness for a `∀`-statement can only discharge premises the reader can check, and for
  > all five statements the premises are typings *upstairs* while the conclusion is the
  > corresponding fact *downstairs*.  Over `propLoopEnv` every term whose upstairs typing can
  > be exhibited is closed, so its downstairs typing is the same derivation and the conclusion
  > is always free.  Making it non-free needs a term typeable only with the stripped entry in
  > scope — which is precisely what strengthening says does not exist.

  Premise-satisfiability is therefore the strongest honest form, and §3 is it.

The instance remains non-degenerate in the two ways that matter, and this is unchanged from
before: `n = 1`, so `Γ ≠ Γ'` and the statement is not being read at its trivial `Ctx.LiftN 0`
instance; and the stripped entry is the environment's proposition `A`, for which no inhabitant
over `[]` is known, so `IsDefEqU.strengthen_of_instN` — the easy half — does not discharge it.

**Not proved, and worth someone's time:** that `A` is genuinely uninhabited over `[]` at
`propLoopEnv`.  That would upgrade "the easy half does not obviously apply" to "the easy half
provably does not apply".  It is a consistency statement about the environment and needs the
inversion machinery that is itself open, so it is not cheap.

---

## 5. The one open residual, and why I did not close it

`SortRedLamExpose ∅ 1 0` — equivalently `SortRedAppDFSort ∅ 1 0`, `SortRedAppDF ∅ 1 0`,
`SortRedInv ∅ 1 1` (`SortRedApp.empty_chain`, every link an iff) — is what is left of
definitional-inversion clauses (1) and (3) at index 1 over the empty environment.  It is
neither proved nor refuted, and I did not move it.

Applying `docs/handoff-stratified.md` §5's criterion, written down before investing, as
instructed: **the induction does have to look at a conversion derivation**, and
`SortRedApp.lean` §2 already machine-checks that it learns nothing when it does
(`sortRedAppDF_fun_ih_vacuous` — the induction hypothesis at the function position is vacuous,
both sides false).  The obvious repair (generalise the predicate to carry a spine) is refuted
(`spineInv_one_false`).  So the criterion's answer is *unfavourable*, and it was already
recorded as such.

**What I added by hand, and it is analysis, not a machine-checked theorem.**  Enumerating the
`⊢₁` rules over `∅` — `constDF` and `extra` are vacuous there, `sortDF`/`lamDF`/`forallEDF`
relate two terms that agree on `SortRed`, `beta` relates a term to its own head-reduct,
`rfl`/`symm`/`trans` compose — the only rules that could relate a `SortRed`-ing term to a
non-`SortRed`-ing one are `eta`, `proofIrrel` and `appDF`.  Of these:

* **`proofIrrel` cannot fire.**  Both endpoints would need `⊢₀` type `p` with `Γ ⊢₀ p : Sort 0`;
  by `HasTypeN.uniq_zero` that `p` is also the shared Π-type `∀A.B`, and
  `.sort (.imax u (.succ w)) = .sort .zero` is unsatisfiable.  (Already in the tree as
  `proofIrrel_not_at_pi` and `SortClauses`' docstring; I re-derived it and it agrees.)
* **`eta` cannot fire either.**  Taking `f` η-expanded and `f' = e`, the natural witness
  `Γ = [∀ (_ : Prop), Prop]`, `f = .lam (.sort .zero) (.app (.bvar 1) (.bvar 0))`,
  `f' = .bvar 0` has both endpoints `⊢₀`-typed at one Π-type and `≡₁` by `eta` — but its
  `SortRed u (e.inst a)` premise is `SortRed u (.app (.bvar 0) a)`, which is **false**: a
  variable-headed application never head-β-reduces.  This is the same obstruction the tree
  already discharges in general as `sortRedAppDFVar_premise_empty`.  Taking the expansion the
  other way round reduces to the residual itself.
* **`appDF` is the residual.**

So the residual is genuinely self-referential over `∅`, and no counterexample is reachable from
the rule set — which is *weak evidence that the statement is true*, and no evidence at all
about how to prove it.  A proof needs a Church–Rosser-shaped argument for βη + proof
irrelevance, which is exactly `ChurchRosser.NormalEq.descend`, which carries five `sorry`s.

**The `Params`-is-now-instantiable news does not help here**, and I checked before assuming:
the Church–Rosser theorem those 545 declarations lead to (`IsDefEq.church_rosser`) is itself
`sorryAx`-tainted through `NormalEq.descend` and `IsDefEqU.forallE_inv_stratified` — see
`ParamsWitness.propLoopEnv_church_rosser_fires`'s own docstring, which says so.  Reaching
`SortRedInv` through it would import the taint rather than remove it.

---

## 6. What to pick up first

1. **Stop counting `sorry`s in this package — there are none.**  Any ledger row that prices
   `Theory/Typing/{Stratified, CycleConv, SortClauses, SortRedApp, PropConv, AppCase,
   RegPiSat, StrengthenWitness}` at 9 holes is nine rows wrong.  The package's real cost is
   **one open statement in four equivalent forms** (§5) plus the residuals `PropExtraConv`,
   `PropConvInv`'s `app` case, and the five converging `app` cases of `AppCase.lean` — all of
   which the files already name and none of which is a hole.

2. **Retire, or re-prove, `propLoopEnv_piDescend_sortDescend_fires`.**  It is the package's
   only `sorryAx`, and §2 shows it earns nothing: tainted *and* tautological.
   `propLoopEnv_piDescend_premises` (§4) now carries its content, sorry-free.  I did not delete
   it — it is named in `docs/handoff-weakn.md` §7 and deletion is the orchestrator's call — but
   deleting it takes the package to **zero `sorryAx` across all 616 remaining declarations** at
   no cost.

3. **Apply §2's lesson to any future witness file.**  A non-vacuity witness for an *open*
   statement must be phrased as premise-satisfiability, never as `Open → C`, because the
   only `C` a witness can exhibit is one it could have proved anyway.  The three `_premises`
   theorems in `StrengthenWitness.lean` §3 are the pattern to copy.  Witness files for
   *proved* theorems (`SortClauses`, `SortRedApp`, `RegPiSat`, `ParamsWitness`) are unaffected
   and need no change.

4. **The `app`-case convergence is the better target than the `SortRed` residual.**  Read off
   `AppCase.lean`'s own tables, not re-derived here: five statements converge on one subject
   shape, the natural unifier (`AppTypeUniq`) is refuted at `n = 1`, and the schema collapse
   (`sortForallEDisjoint_of_rel`) shows no strengthening of the induction makes the remainder
   cheaper.  That file has done the negative work; what it has not done is decide any of the
   five.  `SortRedLamExpose` by contrast needs a normalisation argument nobody has.
