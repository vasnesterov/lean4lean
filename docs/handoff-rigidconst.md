# Handoff — the price of hole B's three constant-spine conjuncts

File: `Lean4Lean/Theory/Typing/RigidConstPrice.lean` (66 declarations, **no `sorryAx`
anywhere**, 86 jobs green). Written 2026-09-03.

## The question

`ForallInvPrice.piInvStrat_and_rigidShapeUniqNS_of_shapeLinkAgree` gets **both** injectivity
holes from one hypothesis set, hole A from a strict subset of it. Call the subset **the base**:

    base  :=  VEnv.WF env  ∧  ConvStep2 env U  ∧  ShapeLinkAgree env U

Hole B additionally needs `RigidConstAppInv`, `RigidConstPiDisj`, `RigidConstSortDisj`. Were
those three free over the base, hole B (460 users) would cost no more than hole A (736 users).

## The answer: (b), in the sharpest form — the three ARE hole B

`constFamily_iff_rigidShapeUniqNS` (§3), both directions, `sorryAx`-free:

    base ⊢ (RigidConstAppInv ∧ RigidConstPiDisj ∧ RigidConstSortDisj) ↔ RigidShapeUniqNS

* `←` of the iff (`⟸` of hole B) is `PiInvResidual.rigidShapeUniqNS_of_constSpine`, already
  in the tree.
* `→` (hole B gives all three back) is new, and is what makes it an equivalence. It needs
  `SortUniq` and `ProofTransport`; **both come from the base**:
  * `SortUniq` — `PiInvResidual.sortUniq_of_shapeLinkAgree`.
  * `ProofTransport` — `proofTransport_of_shapeLinkAgree` (§1), the composition of
    `InjSpineTransport.proofTransport_of_convInv` with
    `PiInvResidual.convInv_of_shapeLinkAgree`. **Nobody had composed those two.** It is the
    `sorryAx`-free supply; `Injectivity.WF.proofTransport` is tainted through
    `HasType.defeqU_l'`.

### Consequences, machine-checked, quantified over all `env` and all `U`

* `constFamily_free_iff_holeB_free` : "the three conjuncts are free once hole A is paid"
  **is** "hole B is free once hole A is paid". Outcome (a) for all three was never a pricing
  question — it is hole B itself.
* `piInvStrat_and_rigidShapeUniqNS_iff_constFamily` : over the base, adding the three is
  exactly adding hole B, and both holes then follow.
* `constHyp_inhabited_iff` : the §0 `∃`-form of the same.

### Therefore: `rigidShapeUniqNS_of_constSpine` is a COLLAPSE

By the standing rule of `docs/vacuity-ledger.md` rows 51 / 77b / 82b / 94a — *test every
proposed localisation against its own target first* — the corner's plan-of-record theorem
reduces hole B to a hypothesis set that, over hole A's own price, **is** hole B. This is the
eleventh collapse in this corner. It should be recorded as one.

The positive reading is real and should not be lost: the three conjuncts are **not extra
strength beyond hole B**. The corner's price is hole A + hole B, not hole A + hole B + three
unknown side conditions. Each of the three also comes back from hole B *individually* over the
base (§2), so none is stronger than hole B; `RigidConstAppInv` comes back with **no hypothesis
at all** (`RigidShapeUniqNS.constAppInv`, print `[propext]`).

### Individually: not settled

Whether any *one* of the three is free from the base is open. All three cannot be (§4). No two
are shown to imply the third. Separating them needs a `VEnv.WF` model and none is available.

## Negative controls (§5) — three environments, each `Ordered`, none `VEnv.WF`

The `InjPiRogue` rogue idiom needs one extra constant here, because `RuleFreeHead c` is a
condition **on `c`**: the two δ-rules go on a *hub* constant, leaving `c` rule-free.

| witness | rules | refutes |
| --- | --- | --- |
| `rcSortEnv` | `rcHub ≡ rcRF.{0}`, `rcHub ≡ Prop` | `RigidConstSortDisj` |
| `rcPiEnv` | `rcHub ≡ rcRF.{0}`, `rcHub ≡ ∀ (_ : Prop), Prop` | `RigidConstPiDisj` |
| `rcLvlEnv` | `rcHub ≡ rcRF.{0}`, `rcHub ≡ rcRF.{1}` | `RigidConstAppInvNP` outright; `RigidConstAppInv` conditionally on `¬ IsProof` |

`not_wf_rcSortEnv` / `not_wf_rcPiEnv` / `not_wf_rcLvlEnv`: each witness carries two δ-rules on
one constant, so `DeltaUnique.WF.defEqHeadsUnique` refutes `VEnv.WF`. **Each control is a
control, not a refutation of the corner** — `ForallInvPrice.not_wf_sortPiEnv`'s discipline.

Three witnesses rather than one deliberately: a single environment carrying all four rules
would also link `Prop` to a Π and hence refute `SortPiDisjUC`, i.e. refute `ShapeLinkAgree`,
making it worthless as a control *over the base*. As built, no rule of any witness has a sort
on one side and a Π on the other. **Not claimed**: that these three *satisfy* `ShapeLinkAgree`.

Row 148b's antitonicity caveat applies and is not evaded: the counterexamples add rules, so
they refute the target at a **stronger** environment. What they establish is that the "at most
one δ-rule per constant" clause of `VEnv.WF` is load-bearing in all three conjuncts — the same
thing row 69 established for `ConvPiFromEntry`.

## Anti-vacuity (§6) — both halves supplied

* `exists_wf_constFamily` : the three hold at a `VEnv.WF` environment, every `U`.
* `exists_wf_constFamily_degenerate` : **and that witness is provably degenerate** — at the
  empty environment no constant spine is typeable at all, by the new spine-typing inversion
  `constants_of_isDefEqU_mkApp` (`HasType.app_inv` up the spine, then `HasType.const_inv`).
  So it shows non-contradiction and nothing more.
* `constFamily_premises_fire` (§6.1) is the control the degenerate witness cannot be: at
  `rcEnv0` — one axiom `rcRF : Sort 1`, **no δ-rules at all**, `VEnv.WF` by `wf_rcEnv0` — every
  head is rule-free and the spine is typeable, so all three conjuncts are **non-vacuous at a
  well-formed environment**. Nothing here proves them there.

**`rcEnv0` is the smallest open instance in this corner.** A one-axiom, zero-rule, well-formed
environment where the three conjuncts say something and are unproved. Anyone attacking them
should start there, and should expect the `trans` case to bite: with no δ-rules, the `extra`
case of an `IsDefEqStrong` induction is vacuous and the residual is exactly the midpoint case
that row 94a's `midShapeless_vacuous` says no syntactic condition can localise.

## Where I did not get, and at which step

1. **No one of the three derived from the base.** The route I would have taken — run the
   `IsDefEqStrong` induction for a `const`-spine/shape link, as `sortLinkInv_of_wf` does for
   sort/sort — stops at the `trans` case, and by row 94a (`midShapeless_vacuous`) a
   midpoint-restricted version of that case is *equivalent* to the unrestricted statement. I
   did not write that induction, because its residual is known in advance to be the target.
   Stated as the obstruction, not as a proof that no route exists.
2. **No refutation at a `VEnv.WF` environment.** The mechanism all three controls use is
   excluded at `VEnv.WF` by `WF.defEqHeadsUnique`, so a genuine outcome (c) would have to be a
   non-confluence of Lean's own rule set. I looked at `WeakNProjGate.exists_typingStrengthening_env`'s
   witness as the coordinator suggested: it is `StrengthenVerdict.exists_univInhabEnv`'s
   environment, whose only constant `univInhab` **heads a δ-rule** (`univDV`'s value is the
   constant itself), so `RuleFreeHead` fails there and all three conjuncts are vacuous. It
   cannot refute anything here.
3. **`RigidConstAppInv` is refuted at `Ordered` only in its `¬ IsProof`-free variant**
   (`RigidConstAppInvNP`, defined here with the conjunct's binders otherwise unchanged — the
   anti-strawman check). The premise is not dischargeable at `rcLvlEnv`: doing so is
   `sort_not_proof`-shaped and wants `SortUniq`. Whether `rcRF.{0}` is a proof at `rcLvlEnv`
   is undecided here in **both** directions.
4. **`PatWF` route untouched.** `RigidNodeCircle.lean` §5's non-circular route (re-derive
   `Verify/Typing/ConstSpine.lean`'s Church–Rosser argument with `PiInv` threaded through in
   place of its internal `forallE_inv` call, and `KCanonical.CRStatement` hypothesised rather
   than `crStatement_holds` applied) is not attempted and nothing here bears on it. Note
   `KCanonical.not_crStatement_of_kstep` before starting it.

## Pick up first

1. **Record the collapse** in `docs/vacuity-ledger.md` and correct the corner table: hole B's
   "three const-spine conjuncts ∧ `ConvStep2`" is, over hole A's price, *hole B*. The table
   currently reads as if the three were a separable further cost.
2. `rcEnv0` (§6.1) as the minimal open instance — see above.
3. The still-open coordinate from row 177b is unchanged and remains the best single target:
   `PiInvStrat → SortPiDisjUC`.

## Corrections to the brief I was given

* "`VEnv.WF` occurs only in binder position anywhere in `Lean4Lean/`, never as a conclusion" —
  false, and by more than the one file the coordinator's mid-task correction named. `∃ env,
  VEnv.WF env ∧ …` occurs at least at `Theory/Typing/StrengthenVerdict.lean:146,176`,
  `Theory/Typing/StrengthenAudit.lean:333`, `Theory/Typing/SortPiDisjPrice.lean:338`,
  `Theory/SetModel/CoherentConstShape.lean:286,296`, `Verify/Typing/ProjWeakInvSplit.lean:213,227`,
  plus `WeakNProjGate.lean`. Measured by `grep -rn "∃ env" --include=*.lean Lean4Lean/ | grep -i wf`
  over the whole `Lean4Lean/` tree; that is a floor, since it only catches the `∃ env` idiom.
* "Outcome (a) for all three would be the strongest result available in this corner" — it is
  not *a* result in this corner, it **is** hole B (`constFamily_free_iff_holeB_free`). The
  brief's three outcomes were not exhaustive for this target: the true answer, (b), was
  available and is the one that lands.
