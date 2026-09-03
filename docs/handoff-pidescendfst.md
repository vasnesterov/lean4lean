# Handoff: `PiCodLift` — the subject eliminated, and the split moved off `f` onto `T`

Round 9b of the `VEnv.IsDefEqU.weakN_iff` line. Resumes the stream that crashed mid-round with
`Lean4Lean/Theory/Typing/PiDescendFstCod.lean` on disk (§4's round trip
`piDescendFst_iff_codLift_of_sortConv`, machine-checked). File owned and continued; nothing else
in the tree was edited.

Marks: **[measured]** = a run reproduced here; **[read]** = read off source; **[analysis]** =
neither. Everything relayed to me in the brief that I did not re-run is marked where it is used.

---

## 0. Verdict, up front

* **`PiCodLift` is not proved and not refuted.** Two reshapings of it are machine-checked, both
  as `iff`s, so no strength is claimed and none is lost.
* **The subject is eliminable** (§2). `PiCodLift ↔ PiCodLiftInhab`: `f` enters only through
  `uniqU` and `a` only through `S`, so the entire residual of `PiDescend` is a **conversion**
  `Γ' ⊢ T↑ ≡ ∀(S↑).B` between a lift and a Π whose two types are inhabited downstairs. No
  typing has to be produced anywhere. This is the cheapest declaration in the file: cone 3486,
  and `WF.rigidShapeUniqNS` is **not** in it — only `forallE_inv_stratified` **[measured]**.
* **The crashed stream's plan is rejected, and the reason is a result** (§3). It intended to
  "restructure with a head-local generalisation and add the case split" on the head of **`f`**,
  as `docs/handoff-pidescend.md` §2.5 has it. After §2 there is no `f`. Splitting on the head of
  the **type** `T` instead discharges **three of the six constructors** uniformly — `.forallE`,
  `.sort`, `.lam` — where the `f`-split discharged one (`.lam`) and needed a hole for two.
* **The residual is: `T` neutral-headed (`.bvar` / `.const` / `.app`), minus the rule-free
  constant slice** (§4), and by §6 it depends only on `T`'s **downstairs conversion class**: the
  live case is exactly "no member of that class is Π-headed", instance by instance.
* **A gap in the instrument, not a new hole** (§5): `RigidShape` (`Injectivity.lean:918`) has
  three entries — `sort`, `pi`, `app c ls as` — and **no `bvar` entry**, and `SPShape`
  (`InjOneFact.lean:170`) has two. So the variable-headed case of the residual has **no slot in
  the injectivity corner's shape machinery at all**.
* **Nothing traded.** `IsDefEqU.weakN_iff` is in **no** cone of the file — measured on all 28
  seeds (25 declarations of this file plus 3 positive controls, `weakN_iff` itself among them) **[measured]**. That is *not* hole-freeness:
  every substantive result carries `sorryAx` through `IsDefEqU.forallE_inv_stratified`, most also
  through `WF.rigidShapeUniqNS`, and §3's `.sort`/`.lam` cases through
  `IsDefEqU.sort_forallE_inv`.
* **Census unchanged**: 13 holes over the whole built population (372 modules, pass A 369 +
  pass B 3), `scripts/sorry-census-all.lean` **[measured]**. `scripts/dup-names.lean`: no
  duplicates. Module builds at **68 jobs**. Layering clean:
  `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is empty **[measured]**.

---

## 1. The chain as it now stands

All four links are machine-checked over `VEnv.WF`; all four carry `forallE_inv_stratified`.

| link | statement | file |
| --- | --- | --- |
| round 8 | `PiDescend ↔ PiDescendFst ∧ SortConvStrengthening` | `PiDescendSplit.lean` |
| round 9 | `PiDescendFst ↔ PiCodLift` given `SortConvStrengthening` | `PiDescendFstCod.lean` §4 |
| **9b §5** | `PiCodLift ↔ PiCodLiftInhab` (no subject) | §5 |
| **9b §6** | `PiDescend ↔ PiCodLiftNeutral ∧ SortConvStrengthening` | §6 |

and the whole thing is pinned to the target from above:
`piCodLift_sortConv_iff_typingStrengthening : PiCodLift ∧ SortConvStrengthening ↔
TypingStrengthening` (§8), so `PiCodLift` is the typing half of `IsDefEqU.weakN_iff` reshaped,
not a statement that might be stronger. `TypingStrengthening.iff_piDescend`'s own cone does
**not** contain `weakN_iff` **[measured]**, so that bound is not circular.

## 2. §5: the subject drops out

```
PiCodLiftInhab : Ctx.LiftN n k Γ Γ' → OnCtx Γ → OnCtx Γ' →
  Γ ⊢ f : T → Γ ⊢ a : S → Γ' ⊢ T↑ ≡ ∀(S↑).B →
  ∃ B₀, S↑::Γ' ⊢ B ≡ B₀↑
```

`→` is one `uniqU`; `←` is one `defeqU_r`. What survives of the two subjects is **inhabitation**
of `T` and `S`, and that is kept on purpose rather than dropped: uninhabited context entries are
the entire difficulty of strengthening (`Strengthen.lean` §1 closes the inhabited case, ledger row
64a), so a version quantifying over uninhabited `T` would be a *different*, possibly strictly
stronger statement. Dropping the inhabitation would be the easy overstatement here and it is not
made.

## 3. §6: the split is on `T`, not on `f` — and that is the round's main correction

`docs/handoff-pidescend.md` §2.5, relayed to me in the brief as the plan to adopt or reject,
splits on `f`'s head and reports: `.lam` free; `.sort`/`.forallE` refutable only via the
`sorryAx` `sort_forallE_inv`; `.bvar`/`.const`/`.app` the genuine residual, with `.const` "the
sharpest form". **All of that was [analysis] and I re-checked it rather than relying on it.** The
first two rows survive in substance but they are rows about the wrong variable:

* `f = .lam _ _` is free *because a λ's own type is a Π* — i.e. because `T` is `.forallE`-headed.
* `f = .sort _` / `.forallE _ _` need sort/Π disjointness *because their types are sorts* — i.e.
  because `T` is `.sort`-headed.

So both closed cases are cases of `T`, and splitting on `T` gets a third one free that the
`f`-split does not see at all: **`T = .lam A' b` is impossible, because a λ is not a type**
(`not_isType_lam`, §6 — apparently new; see §7 for how that absence was measured). Result:

| head of `T` | status | how |
| --- | --- | --- |
| `.forallE A' B'` | **closed** | `IsDefEqU.forallE_inv` on `T↑`, `B₀ := B'`, domain conversion moves the context |
| `.sort u` | **closed** | `T↑ = T`, then `IsDefEqU.sort_forallE_inv` |
| `.lam A' b` | **closed** | `not_isType_lam`: a λ's own type is a Π and a Π is not a sort |
| `.const c ls`, `RuleFreeHead c` | **closed** | `IsDefEqU.const_forallE_inv` (§7 of the file) |
| `.const c ls` with a δ-rule | open | |
| `.app g x` | open | |
| `.bvar i` | open, **and unsupported by the shape lattice** | §5 above |

`piDescend_iff_neutral_sortConv` is the resulting decomposition, an `iff` over `VEnv.WF`.

**This is a case analysis on an *endpoint*, not a side condition on a `trans` midpoint.** The
distinction is the one `docs/vacuity-ledger.md` row 94a (`midShapeless_vacuous`) exists to
enforce: the split is exhaustive, each closed case is closed outright, and the residual predicate
constrains the universally-quantified `T` of the statement rather than a midpoint of a derivation.
Had I restricted a midpoint I would have been the twelfth collapse; I did not, and I say so
because the brief asked to be told which of its warnings applied.

## 4. §6+§10: the sharp form of the residual

`codLift_conv_invariance`: replacing `T` by anything convertible to it *downstairs* leaves the
instance unchanged (one `weakN`, one `trans`). `codLift_of_conv_forallE`: a Π **anywhere** in
`T`'s downstairs conversion class closes the instance. Hence the residual is not "`T` is
neutral-headed" but the stronger

> **no member of `T`'s downstairs conversion class is Π-headed.**

and producing such a member *is* `PiDescendFst` at `f`. §4's `iff` already said the two are
equivalent globally; §10 says they are equivalent **instance by instance**, which is what rules
out the shape of proof that closes some instances by exhibiting a Π and leaves the rest. This is
`docs/handoff-pidescend.md` §2.3's circle (`argPin_ascription_circle`) seen from the codomain
side, and **my route does not reintroduce it as a hypothesis** — it lands on it as the residual,
which is where it belongs.

## 5. The `RigidShape` gap

`RigidShape` (`Injectivity.lean:918`) = `sort u | pi A B | app c ls as`, with
`RigidShape.RuleFree` carrying `RuleFreeHead` on the spine entry only; `SPShape`
(`InjOneFact.lean:170`) = `sort u | pi A B`. **Neither has a variable entry** [read, and the
inductives are three and two constructors as quoted]. Consequently:

* there is **no** declaration in the import closure of `PiDescendFstCod.lean` stating that a
  variable is not convertible to a Π — scanned over the *compiled environment*, not the source:
  of all non-internal constants whose type mentions `Not`, `VExpr.bvar` and `VExpr.forallE`, 12
  are hits and every one is a recursor/`casesOn` or one of my own controls **[measured]**;
* the `.bvar` row of §3's table therefore cannot be closed by the corner's existing machinery
  even in principle; it needs a fourth shape entry and a `Compat` row for it, in
  `Injectivity.lean`, which I do not own.

I am **not** claiming that entry is hard, and I am not claiming it is missing from the whole tree
— only from the closure I can load, which is the largest environment in which the question is
well-posed for this module.

## 6. Anti-vacuity, and one honest gap in it

* **Inhabited.** `exists_env_piCodLift`: `PiCodLift`, `PiCodLiftInhab` and `PiCodLiftNeutral` all
  hold at the `VEnv.WF` environment of `WeakNProjGate.exists_typingStrengthening_env`, at every
  `U`; `exists_env_piDescend_iff_neutral` fires both `iff`s there. That environment's cone is
  **hole-free** — 3271 constants, zero `sorryAx`-carrying, measured, not relayed **[measured]**.
  Read its scope statement with it (`docs/handoff-weakn.md` §3): it declares
  `univInhab : ∀ (α : Sort u), α`, so it is inconsistent and has no uninhabited context entry. It
  is a satisfiability witness and nothing more.
* **The conclusion is a proper constraint**, not a shape triviality:
  `bvar1_not_liftN_one_one` — `.bvar 1`, the stripped variable itself, is not in the image of
  `liftN 1 · 1`, so `∃ B₀, B ≡ B₀↑` really does say something about `B`. Hole-free
  (`[propext, Quot.sound]`) **[measured]**.
* **The excluded region of the split is non-empty**: `forallE_headed_inhabited` — whenever `A` is
  a type, `.lam A (.bvar 0)` is typed at a `.forallE`-headed type, so §6 removed **live**
  instances, not empty ones. `piDescendNeutral_proper` pins the six-way split in both directions.
  Both hole-free.
* **Degenerate instance**: `piCodLift_at_zero` — at `n = 0`, `B₀ := B` works and the conclusion is
  its own premise, so all content lives at `n ≥ 1`. It is a control and not an assumption because
  `VExpr.liftN_zero` is an equation. (Ledger blindness 7: I instantiated at the degenerate
  instance deliberately.)
* **The residual's own premises**: `piDescend_of_no_neutral_pi` — **if they are never satisfiable,
  `PiDescend` follows.** So an absolute inhabitation witness for the residual is exactly as hard
  as refuting the target, and a proof of vacuity is exactly as hard as proving it. This is
  `ForallInvPrice.hyp_inhabited_iff`'s situation, stated as a theorem rather than pleaded. It is
  **not** a claim that no such instance exists (that would be ledger kind 4).
* **The gap, stated plainly: there is no `Ordered`-but-not-`WF` refutation control here**, of the
  kind `rogueSortPiEnv` is for `ShapeLinkAgree`. I did not build one and I do **not** claim one
  cannot exist. What I can say is why the obvious constructions fail, and it is **[analysis]**,
  not a theorem: `VDefEq.WF` types both sides of a rule in the *empty* context, so `extra`'s
  endpoints are closed and hence lifts; `beta`'s right endpoint is a lift whenever its left one
  is; `forallEDF`/`lamDF`/`appDF`/`sortDF`/`constDF`/`eta`/`defeqDF` relate terms of the same
  head; and `proofIrrel` cannot fire because a Π is a type. What is left is **`trans`** — an
  arbitrary midpoint — which is precisely the node row 94a proves no syntactic condition can
  localise. A refutation, if one exists, has to be built there.

## 7. Measurements

`lake build Lean4Lean.Theory.Typing.PiDescendFstCod`: **68 jobs**, green. 544 lines, **30**
top-level declarations (7 inherited from the crashed stream, 23 new), one of them hole-free.

Cones and axioms, my own walker (reproduced in the appendix -- it was run from `/tmp`, so it is
not in the repo; internal names kept as graph nodes,
`allowOpaque := true` so `.thmInfo` values are read), run **immediately after** a build of the
module, with positive controls **[measured]**:

| seed | cone | named holes in cone |
| --- | --- | --- |
| `piCodLift_iff_inhab` | 3486 | `forallE_inv_stratified` |
| `PiCodLift.of_inhab` | 3478 | `forallE_inv_stratified` |
| `codLift_conv_invariance` | 3479 | `forallE_inv_stratified` |
| `PiCodLiftInhab.of_neutral` | 3646 | `+ rigidShapeUniqNS`, `sort_forallE_inv` |
| `piDescend_iff_neutral_sortConv` | 3720 | `+ rigidShapeUniqNS`, `sort_forallE_inv` |
| `codLift_const_ruleFree` | 3599 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `piCodLift_sortConv_iff_typingStrengthening` | 3682 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `exists_env_piCodLift` | 3674 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `const_admits_closed_type` | 3358 | **none** — hole-free, no `sorryAx` |
| `bvar1_not_liftN_one_one` / `forallE_headed_inhabited` / `piDescendNeutral_proper` / `piCodLift_at_zero` | 1487 / 393 / 376 / 176 | **none** |
| *control* `IsDefEqU.weakN_iff` | 3231 | `weakN_iff` (it reaches itself) |
| *control* `TypingStrengthening.iff_piDescend` | 3644 | `forallE_inv_stratified`, `rigidShapeUniqNS` — **not** `weakN_iff` |
| *control* `exists_typingStrengthening_env` | 3271 | **none**, and axioms `[propext, Classical.choice, Quot.sound]` |

`#print axioms`-equivalent (axiom constants in the cone) for every substantive declaration:
`[propext, sorryAx, Classical.choice, Quot.sound]`. Names were read off the file's own
`namespace VEnv` lines (`Lean4Lean.VEnv.*`), never composed from the path — `PiDescendNeutral` is
the one exception and it is deliberately `_root_.Lean4Lean.VExpr.PiDescendNeutral`.

## 8. Where the brief and its inputs are wrong

1. **"restructure with a head-local generalisation and add the case split"** (the crashed
   stream's own last recorded intent, relayed as the plan to adopt or reject): the case split is
   right, the variable is wrong. It belongs on `T`, and on `T` no generalisation is needed at all
   — the split is six `cases`, three of them one line. §3.
2. **"`.const` is the sharpest and unexamined case, because the downstairs type is closed so
   `T↑ = T`"** (relayed as the crashed stream's analysis): closedness is the wrong lever, and the
   sentence conflates the head of `f` with the head of `T`. Closedness of `T` buys `T↑ = T`, which
   removes the lift from the *left* endpoint but leaves the shape problem untouched — and it is
   not what closes any case. What actually closes part of the `.const` slice is `RuleFreeHead`
   plus `IsDefEqU.const_forallE_inv`, which was sitting in `Injectivity.lean` unused by this line
   (§7 of the file). What closedness *does* buy is now **machine-checked** rather than asserted
   (§11, `const_admits_closed_type`): a `.const`-headed subject always admits a *closed* type,
   which is lift-invariant and in particular not a variable, so it never reaches the unsupported
   row of §3's table. That declaration is the one **hole-free** substantive result in the file —
   `[propext, Classical.choice, Quot.sound]`, cone 3358, zero `sorryAx`-carrying constants
   **[measured]**.
3. **"`.lam` free / `.sort`,`.forallE` need `sort_forallE_inv` / three heads open"**: the counts
   are right for the `f`-split and misleading as a statement about the problem — on `T` it is
   three closed and three open, and the `.lam` row of the `T`-split has no analogue in the
   `f`-split.
4. **"outcome 1 = `PiCodLift` proved"** needs a qualifier the brief does not give. `PiDescend` is
   *already* a theorem modulo the hole — `TypingStrengthening.iff_piDescend` plus
   `CRPiDescend.typingStrengthening_of_weakN_iff` (`CRPiDescend.lean:351`) derive it from `IsDefEqU.weakN_iff` [read] —
   so a proof of `PiCodLift` is worth nothing unless `weakN_iff` is absent from its cone. Any
   future round on this target must report the cone, not the axiom set; `#print axioms` cannot
   tell the two apart, since both come out `[propext, sorryAx, Classical.choice, Quot.sound]`.
5. **The CR route is circular, and this is where a reader will lose a day.**
   `IsDefEq.church_rosser` (`ChurchRosser.lean:2480`) exists and would give the residual: a
   conversion between `T↑` and a Π yields a common reduct, and the Π side keeps its shape under
   `ParRedS`, so `T↑` reduces to a Π; descending that reduction to `Γ` finishes. But descending it
   is `ParRed.weakN_inv` (`ChurchRosser.lean:951`), whose `extra` case is literally
   `(IsDefEqU.weakN_iff henv hΓ W).1 h` [read] — the hole itself — and the K-version's lifting
   inversion needs `KEta.PiTypeDescend` (`kStepLiftInv_of`, `KEta.lean:859`), which is
   `PiDescend` without the two `WF` premises. So the reduction route re-enters the target at a
   named single point in both variants.

## 9. What to pick up first

1. **`.const`/`.app` with a δ-active head, at a `trans` midpoint.** That is the residual, and §4
   says it is "no Π in `T`'s downstairs class". The only routes I can see that are not circular
   are (a) an induction on the derivation of `Γ' ⊢ T↑ ≡ ∀(S↑).B` — which **fails structurally**,
   not at one case: the IH needs "the left endpoint is a lift" and every `trans` midpoint breaks
   it, so this is not "one open case" but a non-inductive statement **[analysis]**; or (b) a
   κ-normality/CR argument that does not go through `ParRed.weakN_inv` (§8.5).
2. **The fourth `RigidShape` entry** (§5). It is a `Injectivity.lean` edit, so it needs the
   orchestrator; the payoff is that `.bvar`-headed `T` becomes a *supported* case rather than an
   unsupported one, and by ledger row 86b the sort/Π/bvar disjointness facts are all instances of
   one fact ("a κ-normal rigid head has no reduct of another shape"), so the entry may be nearly
   free once that fact is available.
3. **Do not** apply `docs/handoff-pidescend.md`'s sites 2–4 (its §3.4 stands), and if `PiDescend`
   ever lands, do its §3.3 instead.

---

## Appendix: the walker, disclosed

Run with `lake env lean <file>` **immediately after** `lake build` of the module, per the standing
warning in `docs/handoff-pidescend.md` §1.5 (`lake env lean` reads `.olean`s, not sources). Two
disclosures the standing rule demands: **internal names are kept as graph nodes** (only the
printed set is filtered, and here nothing is filtered), and **`.thmInfo` values are read**
(`allowOpaque := true`).

```lean
import Lean4Lean.Theory.Typing.PiDescendFstCod
open Lean

def deps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => s.union v.getUsedConstantsAsSet
  | none => s

partial def go (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then go env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | some ci => go env ((deps ci).toList ++ rest) seen
    | none => go env rest seen

def cone (env : Environment) (seed : Name) : NameSet := go env [seed] {}

-- axioms of a cone: the `.axiomInfo` constants it contains (this is what `#print axioms` reports)
def axset (env : Environment) (c : NameSet) : List Name :=
  c.toList.filter fun n => match env.find? n with | some (.axiomInfo _) => true | _ => false

run_cmd do
  let env ← Lean.getEnv
  for s in seeds do            -- the 28 names of §7
    let c := cone env s
    let sorries := c.toList.filter fun n =>
      match env.find? n with
      | some ci => (ci.value? (allowOpaque := true)).any
          (·.getUsedConstantsAsSet.contains ``sorryAx)
      | none => false
    logInfo m!"{s} size={c.size} axioms={axset env c} sorry-carrying={sorries}"
```

The ABSENCE scan of §5 is the same import, replacing `run_cmd` with a loop over
`env.constants.toList` that keeps non-internal `n` whose **type**'s constant set contains
`Not`, `VExpr.bvar` and `VExpr.forallE` (12 hits, 10 recursors + my 2 controls), and separately
`Not`, `VExpr.lam` and one of `IsType`/`HasType` (2 hits, both mine).
