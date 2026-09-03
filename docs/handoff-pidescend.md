# Handoff: `PiDescend`, and §7.4 site 1 applied

Round 8 of the `VEnv.IsDefEqU.weakN_iff` line (`Theory/Typing/UniqueTyping.lean:172`).
Input: `docs/handoff-weakn.md` §7 and `Theory/Typing/WeakNProjGate.lean` (commit `155402b`).

Marks, as in `docs/handoff-weakn.md`: **[measured]** = a run reproduced here;
**[read]** = read off source; **[analysis]** = neither.

---

## 0. Verdict, up front

* **Part 1 (§7.4 site 1): landed and measured.**  The corner's hole-reaching count moves
  **32 → 31**, its gate call sites **4 → 3** in `ProjSkip.lean`.  Full `lake build` green, 1549
  jobs, guards 1/2/3 unchanged, no consumer needed a proof change.  The previous stream's
  "cannot regress anything" is **verified**, not assumed (§1.2).
* **Part 2 (`PiDescend`): not proved, not refuted — decomposed, with the obstruction named.**
  New machine-checked `iff`: **`PiDescend ↔ PiDescendFst ∧ SortConvStrengthening`**, where the
  second conjunct is a *known consequence* of `PiDescend` itself (round 6 §6.2).  So the whole
  residual is `PiDescendFst`: Π-shape recovery.  This **corrects `docs/handoff-weakn.md`
  §A.6(4)**, which prices the second conjunct as `TransStrengthening`; it is the strictly weaker
  sort-typed slice, and it is free.
* **Sites 2–4: refused, and the refusal is a measurement.**  Their ripple is **189** non-internal
  transitive users across ~25 modules, reaching `Verify.SoundnessAssembly`; 2 of the 8 direct
  callers live in `ProjGenSwap.lean`, which I do not own.  `docs/handoff-weakn.md` §7.4 describes
  this as five callers.  §3.3 gives a strictly better edit that touches **zero** call sites.
* **Nothing discharged.**  The census is unchanged, `IsDefEqU.weakN_iff`'s `sorry` stands, and
  every substantive result in `PiDescendSplit.lean` carries `sorryAx` through
  `IsDefEqU.forallE_inv_stratified` (and most also `WF.rigidShapeUniqNS`).  "`weakN_iff` absent
  from the cone" is not "hole-free".

---

## 1. Part 1: §7.4 site 1 is landed, and the corner moved by exactly **one**

### 1.1 The edit

`Lean4Lean/Verify/Typing/ProjSkip.lean`, `OnCtx.of_appendTele` (`:327` before the edit):

```lean
-- before
theorem OnCtx.of_appendTele {env : VEnv} {U : Nat} (henv : VEnv.WF env) :
    ∀ {As Γ : List VExpr}, OnCtx (As.reverse ++ Γ) (env.IsType U) → OnCtx Γ (env.IsType U) :=
  fun {As Γ} h => OnCtx.weakN_inv henv (Ctx.LiftN.zero (Γ := Γ) As.reverse rfl) h

-- after
theorem OnCtx.of_appendTele {env : VEnv} {U : Nat} :
    ∀ {As Γ : List VExpr}, OnCtx (As.reverse ++ Γ) (env.IsType U) → OnCtx Γ (env.IsType U) :=
  fun {_ _} h => VEnv.onCtx_of_appendTele_free h
```

plus `import Lean4Lean.Theory.Typing.WeakNProjGate` and the two in-file call sites
(`:345`, `:371`, both inside `VEnv.HasType.swapCtx` / `OnCtx.swapCtx`) dropping their `henv`
argument.  **The ripple is zero outside `ProjSkip.lean`**: `of_appendTele`'s only two callers
are in that file (`grep -rn "of_appendTele" --include=*.lean .` -- the only other hits are
doc-comment mentions in `WeakNProjGate.lean` and `WeakNProjSwap.lean`) **[measured]**.

### 1.2 The previous stream's claim, verified rather than assumed

> "This one is free and independent of everything else … cannot regress anything."

Checked, three ways **[measured]**:

* **The replacement is axiom-free.**  `#print axioms Lean4Lean.VEnv.onCtx_of_appendL` and
  `… .onCtx_of_appendTele_free`: both **"does not depend on any axioms"**.
* **The result strictly improves.**  `#print axioms Lean4Lean.OnCtx.of_appendTele` is now
  `[propext]`; before the edit it inherited `OnCtx.weakN_inv`'s
  `[propext, sorryAx, Classical.choice, Quot.sound]`.  **`sorryAx` is gone from that
  declaration.**  (The residual `propext` is not from the replacement -- it comes from
  `of_appendTele`'s own statement/eta, not from `onCtx_of_appendTele_free`, which has none.)
* **Every consumer still builds**: `Verify.Typing.Lemmas`, `Verify.Typing.ProjGenSwap` (the
  only two `^import`ers), and downstream `ProjGenTerm`, `ProjGenTermWitness`,
  `ProjWeakInvSplit`, `WeakNProjSwap`, `Verify.Guard`, `Experimental.ConeJoin` -- all green,
  no proof change required anywhere **[measured]**.

### 1.3 The measurement -- which is the point of the edit

Instrument: the §7.9 walker, reproduced in §8 below with the two disclosures the standing rule
demands.  **It keeps internal names as graph nodes** and **it does read `.thmInfo` values**.
Import closure: `Verify.Guard`, `Experimental.ConeJoin`, `Theory.Typing.StrengthenNarrow`,
`Verify.Typing.ProjGenTerm`, `Verify.TypeChecker.ProjGenTermWitness`,
`Verify.Typing.ProjWeakInvSplit`.  Seeds: the 197 non-internal declarations of the six corner
modules, plus `TrProj.wf`, `TrProj.weak'_inv`, `VEnv.HasType.{swapCtx,swapTele}`,
`OnCtx.swapCtx`, `VEnv.IsStructureG.projTermG_hasType`.

|  | before | after |
|---|---|---|
| corner seeds scanned | 197 | 197 |
| **corner seeds reaching the hole** | **32** | **31** |
| still reaching, typing gates cut | 3 | 3 |
| survivors | `constAppDefeqStrengthenRF_of_constRigid`, `TrProj.weak'_inv_of_constRigid`, `constAppDefeqStrengthenInh_of_constRigid` | identical |
| gate call sites in the corner's cone | 5 (4 in `ProjSkip`) | **4 (3 in `ProjSkip`)** |
| `TrProj.wf` cone size | 5091 | 5095 |
| `projTermG_hasType` cone size | 5271 | 5275 |

**The before-column reproduces §7.1(b) exactly** (32 / 3 / same three survivors, cones 5091 and
5271), so the instrument is the same one, run on the same tree.

**Read the "one" honestly.**  Site 1 frees exactly one declaration -- `OnCtx.of_appendTele`
itself -- because it was the only declaration in the corner whose *entire* route to the hole
was that call.  The other 31 all still route through `VEnv.HasType.swapSkipped` or the two
`swapCtx` equation bodies, which are sites 2-4.  `TrProj.wf` and `projTermG_hasType` still
reach the hole.  Site 1 is not a partial unblocking of the corner; it is the removal of one
spurious edge, and the number that says so is 1, not 29.

**And one cost, recorded because it is a real regression in one direction**: both headline
cones *grew* by 4 constants (5091 → 5095, 5271 → 5275).  The replacement introduces
`onCtx_of_appendL`, `onCtx_of_appendTele_free` and two equation-compiler auxiliaries where the
old body reused a constant already in the cone.  Cone size is not a hole count and nothing here
depends on it; recorded so nobody reads the growth later as a regression of substance.

### 1.4 Where the input brief was wrong about site 1

The relay said *"29 are freed by cutting the typing gates"* immediately next to *"site 1 is
spurious"*, which invites reading site 1 as buying a large part of the 29.  It buys **1 of the
32**.  The 29 is what sites 2-4 buy *in addition*, and only if `PiDescend` is then discharged;
until then sites 2-4 trade a hole in the cone for an open hypothesis, which the count does not
show.  `docs/handoff-weakn.md` §7.0(2) is not wrong -- it never claimed otherwise -- but the
two numbers sitting side by side in the relay are misleading, and the ledger row 180 has the
same juxtaposition.

### 1.5 A controlled measurement, because HEAD moved under me

Between the before-run and the after-run the orchestrator committed three other streams' work
(`f5c94c0`, `e701a3f`, `d6d92bd`), and the `.olean` for `ProjSkip.lean` went stale in a way that
made one intermediate scan silently report the **pre-edit** numbers from a post-edit source
tree.  I caught it only because the site list still contained `of_appendTele`.  So the
before/after table is not two runs on one tree, and I do not report it as one.  What *is*
measured on the current tree, as a positive control that the removed edge was real
**[measured]**:

```
control: OnCtx.weakN_inv           reaches hole = true      <- the gate itself still does
control: OnCtx.of_appendTele       reaches hole = false     <- the edited site no longer does
control: onCtx_of_appendTele_free  reaches hole = false     <- and the replacement never did
```

and the 31 reaching seeds are listed by name in §8.3; `Lean4Lean.OnCtx.of_appendTele` is absent
from that list, and was present (as a gate call site) before.  Together with the site list
losing exactly its row, the delta is exactly the one declaration.

**Standing warning for the next stream**: `lake env lean <script>` reads `.olean`s, not sources.
Rebuild the modules your scan imports *immediately before* running it, and put a positive
control in the scan (a constant whose answer you already know) so a stale read is visible.
This is the fifth instrument failure in this document's history and the first of this *kind*.

---

## 2. Part 2: `PiDescend` is not proved.  It is decomposed, and the residual is named

New file, mine: `Lean4Lean/Theory/Typing/PiDescendSplit.lean` — 20 source declarations
(3 `def`s -- `PiDescendFst`, `ArgPin`, `SortConvStrengtheningWF` -- and 17 theorems), no `sorry`,
`lake build` green.  Imports `Theory.Typing.NormalEqStrengthen` and `Theory.Typing.WeakNProjGate` only, both
under `Theory/` — layering clean (`grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is
empty **[measured]**).

### 2.1 The result

`PiDescend`'s conclusion is a **conjunction**, and the two halves are different problems:

```
PiDescend : Ctx.LiftN n k Γ Γ' → OnCtx Γ → OnCtx Γ' →
  Γ' ⊢ f↑ : ∀A.B → Γ' ⊢ a↑ : A → WF Γ f → WF Γ a →
  ∃ A₀ B₀, Γ ⊢ f : ∀A₀.B₀   ∧   Γ ⊢ a : A₀
           ^^^^^^^^^^^^^^^^       ^^^^^^^^^^
           Π-shape recovery       type pinning
```

**Machine-checked this round:**

| name | statement | axioms | holes in cone |
|---|---|---|---|
| `PiDescendFst` | the first conjunct alone, **same premises** | — | — |
| `PiDescend.fst` | `PiDescend → PiDescendFst`, a projection | `propext` | **none** |
| `ArgPin` | the second conjunct alone, isolated | — | — |
| `SortConvStrengtheningWF` | `SortConvStrengthening` with both endpoints already `IsType Γ _` | — | — |
| `SortConvStrengthening.wf` | the unrestricted form implies it | `propext` | **none** |
| **`ArgPin.of_sortConvWF`** | **sort-typed conversion strengthening pins types** | `+ sorryAx` | `forallE_inv_stratified` **only** |
| `SortConvStrengtheningWF.of_argPin` | the converse | `+ sorryAx` | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `sortConvWF_iff_argPin` | **the two are the same statement** | `+ sorryAx` | both |
| **`PiDescend.of_fst_argPin`** | **`PiDescendFst ∧ ArgPin → PiDescend`** | `+ sorryAx` | both |
| `PiDescend.of_fst_sortConv` | the same off the tree's own form | `+ sorryAx` | both |
| **`piDescend_iff_fst_sortConv`** | **`PiDescend ↔ PiDescendFst ∧ SortConvStrengthening`** | `+ sorryAx` | both |
| `piDescend_iff_fst_argPin` | …and with `ArgPin`, `SortDescend` free on the right | `+ sorryAx` | both |
| `argPin_ascription_circle` | the circle of §2.3, as a theorem | `+ sorryAx` | both |
| `exists_env_piDescendFst_argPin`, `exists_env_piDescend_iff` | anti-vacuity (§2.4) | `+ sorryAx` | both |
| `argPin_type_restriction`, `piDescendFst_forgets_arg`, `argPin_at_zero`, `piDescendFst_at_zero` | controls (§2.5) | `≤ propext, Quot.sound` | **none** |

`+ sorryAx` means the full axiom set is `[propext, sorryAx, Classical.choice, Quot.sound]`.
**Cones measured** with the §8 walker: `ArgPin.of_sortConvWF` 3484, `PiDescend.of_fst_argPin`
3618, `piDescend_iff_fst_sortConv` 3681, against baselines `IsDefEq.uniqU` 3474,
`IsDefEqU.forallE_inv` 3574, `TypingStrengthening.hasType_inv` 3631,
`SortConvStrengthening.of_typing` 3640 **[measured]**.

**Nothing traded.**  `IsDefEqU.weakN_iff` is in **no** cone of this file — checked on all ten
substantive declarations, not just the headline **[measured]**.  And `rigidShapeUniqNS` is not
new: it is `TypingStrengthening.hasType_inv`'s and `SortConvStrengthening.of_typing`'s hole too,
and it enters here through exactly one lemma, `IsDefEqU.forallE_inv` (Π-injectivity).  **The
useful half, `ArgPin.of_sortConvWF`, avoids even that** — `forallE_inv_stratified` only.

**And say the thing plainly, as the brief asks**: none of this is hole-free.  Every substantive
row above carries `sorryAx` through `IsDefEqU.forallE_inv_stratified`, and most also through
`WF.rigidShapeUniqNS`.  "`weakN_iff` absent from the cone" is **not** "hole-free".

### 2.2 The correction: `docs/handoff-weakn.md` §A.6(4) prices the second conjunct wrong

§A.6(4) says `PiDescend`

> "is now known to need *conversion* strengthening too, not just typing strengthening: its
> second conjunct asks for `Γ ⊢ a : A₀` with `A₀` **f's** domain, and reconciling `a`'s own
> downstairs type with `A₀` is `TransStrengthening`."

**The diagnosis is right and the price is wrong.**  `a`'s downstairs type `S` and `f`'s domain
`A₀` are both **types**, so the conversion to be strengthened is `Γ' ⊢ S↑ ≡ A₀↑ : .sort v` — a
*sort-typed* conversion between two lifts, i.e. one instance of `SortConvStrengthening`
(`NormalEqStrengthen.lean:95`), **not** of `TransStrengthening`.  `ArgPin.of_sortConvWF` is that
derivation, machine-checked, and it is the cheapest thing in the file.

The consequence matters for planning: round 6 §6.2 already proved `SortConvStrengthening` is a
**consequence** of the typing half (`SortConvStrengthening.of_piDescend`), so the second
conjunct is **not an additional unknown**.  `piDescend_iff_fst_sortConv` is the statement that
the whole residual of `PiDescend` is the **first** conjunct: Π-shape recovery.

This also means §A.6(4)'s implicit warning — "`PiDescend` is contaminated by the `trans`
residual after all, so it is not really the cheaper target" — is **withdrawn**.  It is still the
cheaper target, and `TransStrengtheningNarrow` is not on its route.

### 2.3 The obstruction, named

`piDescend_iff_fst_sortConv` would be decoration if `PiDescendFst` alone gave the second
conjunct.  It does not, and the reason is one sentence:

> **Π-shape recovery is existential and type pinning is not.**  `PiDescendFst` returns *some*
> Π type `∃ A₀ B₀`; `ArgPin` must land on a **given** type.  The move that converts one into
> the other is the ascription redex of `Strengthen.lean` §3 — type `.app (.lam A₀ (.bvar 0)) a`
> downstairs and invert it — and that redex's typing *is* `Γ ⊢ a : A₀`, the conclusion sought.

`argPin_ascription_circle` **[machine-checked]** is that circle as a theorem rather than a
claim: for every `Γ`, `A₀` with `IsType Γ A₀`, the redex is typeable at `A₀` **iff** `a` is, and
the function half `Γ ⊢ .lam A₀ (.bvar 0) : .forallE A₀ A₀.lift` needs only `IsType Γ A₀`, which
is already a hypothesis.  So the redex route hands back a hypothesis, not a conclusion.  This is
`NormalEqStrengthen.lean` §4's `sortConv_encoding_vacuous` one level up: the `forallE` former
has a slot for a *type* but the ascription redex has no slot for a *pinned* type it does not
already know.

`SortConvStrengthening.of_typing`'s proof is where the pinning is essential and visible: it
needs `Γ ⊢ .lam A₂ (.bvar 0) : .forallE A₁ A₁.lift` with the type pinned **to `A₁`**, because
that is what makes `uniqU` against the term's natural type `.forallE A₂ A₂.lift` produce
`A₂ ≡ A₁`.  Feed it `PiDescendFst`'s unpinned `∃ A₃ B₃` and `uniqU` returns `A₃ ≡ A₂`, which is
information you put in.  `SortConvStrengtheningWF.of_argPin` is that proof with `ArgPin` in the
pinning slot, and it goes through — which is why §2.1's `sortConvWF_iff_argPin` is an `iff` and
why the second conjunct has a name in typing terms as well as in conversion terms.

### 2.4 Anti-vacuity

* **Every hypothesis is inhabited.**  `exists_env_piDescendFst_argPin` **[machine-checked]**: a
  `VEnv.WF` environment at which `PiDescend`, `PiDescendFst`, `SortDescend`, `ArgPin` and
  `SortConvStrengthening` all hold, for every `U`, built on
  `WeakNProjGate.exists_typingStrengthening_env` (which the orchestrator verified hole-free).
  `exists_env_piDescend_iff` fires the `iff` there with nothing left over.
  **Read the scope statement with it**, as `docs/handoff-weakn.md` §3 insists: that environment
  declares `univInhab : ∀ (α : Sort u), α`, so it is inconsistent and by
  `univInhab_no_uninhabited_entry` has **no uninhabited context entry** — precisely the case
  `Strengthen.lean` §1 already closes.  It is a *satisfiability* witness and nothing more.  I am
  not claiming any hypothesis here is easy.
* **`PiDescendFst` keeps all of `PiDescend`'s premises deliberately.**  A version without the
  argument `a` would be `KEta.lean:847`'s `PiTypeDescend`, and there is **no route from
  `PiDescend` to that** — `A` need not be inhabited, so no argument can be manufactured, and
  `PiDescend → PiTypeDescend` is therefore not available.  Keeping `a` makes `PiDescend.fst` a
  projection (`[propext]`, hole-free), so `PiDescendFst` is *provably* no stronger than
  `PiDescend` and the `iff` cannot be a strengthening in disguise.
* **Negative controls, all machine-checked:**
  (a) `argPin_type_restriction` — `.bvar 0` is not in the image of `liftN 1 · 0`, so `ArgPin`'s
  "type is a lift" premise is a *proper* restriction: it is not the (false) claim that every
  upstairs typing descends.
  (b) `piDescendFst_forgets_arg` — the truncation is strict: `PiDescendFst`'s conclusion does
  not mention `a` at all, and the statement pairs the free implication with the full conclusion
  so the difference is exactly `ArgPin`.
  (c) `argPin_at_zero`, `piDescendFst_at_zero` — at `n = 0` both conclusions **are** their
  premises (a `Ctx.LiftN 0 k` is the identity on contexts), so all content lives at `n ≥ 1`.
  This is §5.1's `vacuous_at_zero` discipline, and it is a genuine control: the split has not
  hidden content in the degenerate case.
  **And show the control is a control**: (a) is not vacuous because `bvar0_not_liftN_one` is
  proved for *every* `b`, so the excluded region is non-empty; (c) is not vacuous because
  `liftN_zero_ctx_eq` is an equality of contexts, not an assumption — the `n = 0` case really
  does collapse, so a lemma that claimed content there would be wrong.
  **What is missing, and why**: there is no `⊬` control — no witness at which `PiDescendFst`
  *fails* — because §A.2's census found the tree's 31 non-derivability instruments are all
  head-shape facts and all lift-stable, so none separates two contexts.  I did not re-measure
  that census; I am relying on it **[read]**.

### 2.5 What I did **not** achieve

* **`PiDescend` is not proved and not refuted.**  I did not attempt a refutation; §A.2 and §A.5
  of `docs/handoff-weakn.md` argue no instrument exists, and I found no reason to doubt them.
* **`PiDescendFst` is not reduced further.**  I checked the syntactic case split on `f` by hand
  and it does not close: `f = .lam _ _` is **free** (the Π is built downstairs — CRPiDescend's
  §1 insight); `f = .sort _` / `.forallE _ _` are refutable only via `IsDefEqU.sort_forallE_inv`,
  which is `sorryAx`; and `f = .bvar i`, `.const c ls`, `.app g b` are all the genuine residual
  — for `.bvar` the downstairs type is an arbitrary context entry, for `.const` it is a *closed*
  term (so `T↑ = T` and the conversion `Γ' ⊢ T ≡ ∀A.B` lives entirely upstairs), and for `.app`
  it recurses.  **[analysis, not machine-checked]**  The `.const` case is the sharpest form: it
  is Π-shape descent for a **closed** type, which no lift can touch.
* **I did not measure the corner after sites 2–4**, because they cannot be applied — §3.

---

## 3. Sites 2–4: **do not apply**, and the reason is a measurement, not a judgement

### 3.1 They terminate outside `ProjSkip.lean`, so I stopped as instructed

Sites 2–4 add `(HT : VEnv.TypingStrengthening env U)` to five declarations and restrict `B` to
`.sort u`: `VEnv.HasType.{swapSkipped, swapSkipped_one, swapTele, swapCtx}` and `OnCtx.swapCtx`.
Every caller must then either supply `HT` or acquire it.  **Direct callers, internal names
included [measured]:**

```
[Verify.Typing.ProjSkip]    6: barField1_hasType_swapped, VIndCtor.swapData,
                               VEnv.HasType.swapCtx._f, bar_swapTele,
                               ftype_hasType_swapped, bar_swapCtx
[Verify.Typing.ProjGenSwap] 2: VIndCtor.swapDataG, ftype_hasType_swappedG
```

Two of the eight are in `ProjGenSwap.lean`, which I do not own, and threading a hypothesis
through them is a real proof change.  Per the brief I stopped there.

### 3.2 The ripple is **189**, not 5

Reverse reachability from the five site declarations, to fixpoint (11 rounds), reporting
non-internal names **[measured]**:

```
transitive users of the five site declarations (non-internal): 189
```

by module (top): `Verify.Primitive` 29, `Verify.Typing.Lemmas` 24, `Verify.TypeChecker.IsDefEq`
22, `Verify.TypeChecker.InferType` 12, **`Verify.Typing.ProjSkip` 8**,
`Verify.Typing.ProjGenTerm` 6, `Verify.Bridge` 6, `Verify.Environment` 6,
`Verify.TypeChecker.Basic` 6, `Verify.Typing.ProjGenSwap` 5, `Verify.EquivManager` 3,
`Verify.Typing.ConditionallyTyped` 3, **`Verify.SoundnessAssembly` 2**, and eleven more with 1–2
each — about 25 modules.

**This corrects `docs/handoff-weakn.md` §7.4 directly.**  It describes sites 2–4 as "a body
replacement plus, for three of them, one added hypothesis `(HT …)` threaded to the callers
(`ftype_hasType_swapped`, `ftype_hasType_swappedG`, `VIndCtor.swapDataG`, and onward to
`projTermG_hasType` / `TrProj.wf`)" — five names.  The true set is **189 declarations across ~25
modules, reaching `Verify.SoundnessAssembly`**.  Sites 2–4 are a **flag day**, not a four-site
edit, and no stream owning only `ProjSkip.lean` can land them.  (§6.5 of that document already
calls the analogous `ChurchRosser.lean` edit "the `TypingStrengthening` flag day, which
terminates outside this stream's files"; §7.4 does not carry the same warning and should.)

The threading *can* be stopped early — `CRPiDescend.typingStrengthening_of_weakN_iff`
(`CRPiDescend.lean:351`) inhabits `TypingStrengthening` from the hole itself — but every
termination point re-introduces `weakN_iff` there, so a partial application buys nothing.  The
ripple is therefore 189 or 0, with nothing useful in between.

### 3.3 And they are the **wrong shape of edit** even if `PiDescend` lands

This is the highest-value thing in this handoff, so it is stated as an explicit proposal with
the part I measured separated from the part I read.

The ten typing gates are **defined** in `Theory/Typing/UniqueTyping.lean:200–260`
(`VExpr.WF.weakN_iff`, `IsDefEq.skips`, `IsDefEq.weakN_iff'`, `OnCtx.weakN_inv`,
`IsDefEq.weakN_iff`, `HasType.weakN_iff`, `IsType.weakN_iff`, `HasType.skips`, and the two
`weak'` forms), each with a **body** that calls `IsDefEqU.weakN_iff` (`:190`).  If `PiDescend`
becomes a theorem, the right edit is to replace those **bodies** — not to thread a hypothesis
through 189 call sites.  Then **zero call sites change**, and every gate-only user in the tree is
freed at once: 59 globally and 28 of the corner's 31 (the corner's other 3 are
`ProjWeakInv{,Split}`'s `constRigid` line, a different residual).

The obstruction to doing that today is import order, and **it is not a real obstruction**
**[measured]**: `Strengthen.lean` imports `UniqueTyping.lean`, so `TypingStrengthening` is
currently downstream of the gates — but every module in the cone of
`TypingStrengthening.of` / `.sortDescend` / `.piDescend` is **already inside
`UniqueTyping.lean`'s own 43-module import closure**, with the single exception of
`Strengthen.lean` itself, where the three statements live.  I checked this by walking the
`import` headers and by taking the constant cones of all three theorems (18, 17, 18 modules)
**[measured]**.  So:

> **Proposed edit (NOT made — `UniqueTyping.lean` is not mine, and I was told not to touch it).**
> 1. Move `SortDescend`, `PiDescend`, `TypingStrengthening` and `TypingStrengthening.of` /
>    `.sortDescend` / `.piDescend` out of `Strengthen.lean` into a new module imported *before*
>    `UniqueTyping.lean` (`Theory/Typing/Descend.lean`, say, importing `Strong.lean`).
>    `Strengthen.lean` then imports that module and keeps everything else unchanged.
> 2. In `UniqueTyping.lean`, replace the bodies of the ten gates at `:200–260` with proofs from
>    `TypingStrengthening` — `StrengthenNarrow.lean` §5 and `WeakNProjGate.lean` §1–§2 already
>    contain each of those statements, machine-checked, so this is transcription, not new
>    mathematics.  `IsDefEq.uniqU` is at `:113`, *above* the hole, so the sort-typed gates can
>    still use it in place.
> 3. `IsDefEqU.weakN_iff`'s own `sorry` at `:190` stays; only the gates stop routing through it.

**Marks, honestly**: step 1's feasibility is **[measured]** (import closure, cone modules).
Step 2's is **[read]** — the statements exist and were machine-checked by round 7, and I have not
elaborated them in `UniqueTyping.lean`'s position, so I am not claiming they compile there.
Step 3 is bookkeeping.

### 3.4 The verdict on sites 2–4

**Not worth applying, now or after `PiDescend` lands.**
1. They cannot be landed by a stream owning only `ProjSkip.lean` (§3.1).
2. Their ripple is 189 declarations reaching `Verify.SoundnessAssembly` (§3.2).
3. What they buy is a **cone** improvement, and a cone is blind to hypotheses
   (`docs/vacuity-ledger.md` §0, third row: "a cone walks `deps`, and a hypothesis is not a
   dependency").  Applying them without discharging `PiDescend` would move the corner's count
   from 31 to 3 while discharging **nothing** — which is exactly the overstatement mode that
   ledger row exists to prevent.
4. After `PiDescend` lands, §3.3's edit is strictly better: same effect, zero call sites, and it
   frees 59 users globally instead of the corner alone.

So the brief's plan — "if `PiDescend` lands, apply sites 2–4" — should be replaced by "if
`PiDescend` lands, do §3.3".  Site 1 was worth applying on its own terms (it removes a spurious
edge and `sorryAx` from a declaration, at no cost); sites 2–4 are not the same kind of edit and
should not be inherited from the same paragraph.

---

## 4. Where the brief and its input are wrong

1. **"29 are freed by cutting the typing gates" placed beside "site 1 is spurious"** invites
   reading site 1 as buying most of the 29.  It buys **1 of 32** (§1.3).  Ledger row 180 has the
   same juxtaposition.
2. **`docs/handoff-weakn.md` §A.6(4) prices `PiDescend`'s second conjunct as
   `TransStrengthening`.**  It is `SortConvStrengthening`, which is a *consequence* of the typing
   half — so the second conjunct is not an extra unknown at all (§2.2, machine-checked).
3. **§7.4 undersells sites 2–4 by a factor of ~38** (5 named callers vs. 189 transitive users),
   and does not carry §6.5's own "flag day" warning (§3.2).
4. **The brief's "If it lands, apply §7.4 sites 2–4"** is the wrong follow-up even in the success
   case: §3.3's gate-body replacement dominates it on every axis, and the import-order objection
   to it is measurably false.
5. **"`PiDescend` frees the corner — but only after §7.4's edit … The two must be scheduled
   together, which is why they are one task here."**  The *dependency* claim is right; the
   *scheduling* conclusion is not, because §7.4's edit is not schedulable inside one stream's
   file ownership.  Pairing them in one task guaranteed that at most one half could be done.
6. **The brief says `SortDescend` is not a cheaper substitute "because it presupposes
   `VExpr.WF Γ e` while `IsType.weakN_iff` must produce typeability".**  Correct, and I did not
   re-derive it — but the same asymmetry bit me in a place the brief did not mention:
   `SortConvStrengthening`'s converse (§2.1's `SortConvStrengtheningWF.of_argPin`) needs
   `IsType Γ e1` and `IsType Γ e2`, which `SortConvStrengthening` does not carry.  That is why
   `SortConvStrengtheningWF` exists as a separate `def`.  Both call sites in §2 have those
   premises for free, so nothing is lost — but anyone restating §2.1's `iff` at the unrestricted
   `SortConvStrengthening` will find the `←` direction unprovable, and it is not obvious from
   the names.

---

## 5. Verification

* **`lake build`: green, 1549 jobs [measured].**  (At the start of the round it *failed* — three
  modules under `Theory/Inductive/` were broken by the nested-inductives stream's in-flight
  `Built.occurs : Occurs → OccursN` change.  That was committed and fixed while I worked; none of
  it was mine, and I verified it by reading the diff to `NestedBuild.lean` before touching
  anything.)
* **Guards unchanged [measured]:**
  ```
  guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
  guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
  guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
  ```
* **`scripts/sorry-census.lean`: TOTAL 13 [measured]** at the end.  I closed nothing, so this
  must equal the value at the start; I did not run it at the start (HEAD moved under me), so I
  report it as the current-tree value rather than as a before/after.  What *is* measured: neither
  file I touched contains the token `sorry` outside prose (`grep -n sorry` → three docstring
  mentions, zero tactic uses).
* **`scripts/dup-names.lean`: no duplicates** [measured], default run **and** a dedicated run
  adding `Theory.Typing.PiDescendSplit` + `Verify.Typing.ProjSkip` to the joined cone.
* **Layering**: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is empty [measured].
* **Frozen files untouched**: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`
  are not in my diff.  §3.3 states an edit to `UniqueTyping.lean` and does not make it.
* **Files changed**: `Lean4Lean/Verify/Typing/ProjSkip.lean` (site 1, 15 insertions / 5
  deletions), `Lean4Lean/Theory/Typing/PiDescendSplit.lean` (new), `docs/handoff-pidescend.md`
  (this file).  Nothing else.

---

## 6. What to pick up first

1. **`PiDescendFst` is the whole residual of `PiDescend`** (§2.1).  Attack *it*, not `PiDescend`,
   and do not spend anything on the second conjunct — it is free (§2.2).
2. **Its `.const` case is the sharpest target and nobody has looked at it.**  For
   `f = .const c ls` the downstairs type is `(env.constants c).type.instL ls`, which is
   **closed**, so `T.liftN n k = T` and the conversion `Γ' ⊢ T ≡ .forallE A B` lives entirely in
   the larger context with a lift-invariant left endpoint.  If Π-shape descent fails anywhere it
   fails there, and if it holds there the argument may generalise by the `Ordered`
   closed-declared-types hypothesis that killed §2's open-constant witness.  **[analysis]**
3. **Do §3.3, not sites 2–4**, and do it only once `PiDescend` is a theorem.  Step 1's import
   move is measured feasible; step 2 is transcription from `StrengthenNarrow.lean` §5 and
   `WeakNProjGate.lean` §1–§2.
4. **Do not** re-attempt: the ascription-redex route to type pinning (`argPin_ascription_circle`
   is the circle); `PiDescend → PiTypeDescend` (`A` need not be inhabited); a `PiDescendFst`
   without the argument premise (that *is* `PiTypeDescend`, and is possibly strictly stronger);
   anything in `docs/handoff-weakn.md` §6.6 / §8's do-not lists.
5. **Instrument hygiene**: rebuild before scanning and put a positive control in every scan
   (§1.5).  I lost one measurement to a stale `.olean` this round.

---

## 7. Verdict

* **Site 1: landed.**  `ProjSkip.OnCtx.of_appendTele` no longer calls a `sorryAx`-carrying gate;
  its axiom set went from `[propext, sorryAx, Classical.choice, Quot.sound]` to `[propext]`.  The
  corner's hole-reaching count moved **32 → 31** and its gate call sites **4 → 3** in
  `ProjSkip.lean` (5 → 4 overall).  Every consumer builds with no proof change.
* **`PiDescend`: not proved, not refuted — priced.**  `PiDescend ↔ PiDescendFst ∧
  SortConvStrengthening`, machine-checked, with the second conjunct a known consequence of the
  whole; so the residual is Π-shape recovery alone, and the obstruction is that Π-shape recovery
  is existential where type pinning is not (§2.3).
* **Sites 2–4: refused, with the number.**  189 transitive users across ~25 modules, 2 of the 8
  direct callers outside my ownership, and a better edit available (§3.3).
* **Where I failed, and at which step**: I did not prove `PiDescendFst`.  The attempt died at the
  syntactic case split on `f`, at the three cases `.bvar` / `.const` / `.app`, where the
  downstairs type is an arbitrary context entry, a closed term, and a recursive instance
  respectively — the `.lam` case is free and the `.sort` / `.forallE` cases need
  `IsDefEqU.sort_forallE_inv`, which is `sorryAx` (§2.5).  That case split is **[analysis]**, not
  machine-checked; I did not have the budget to formalise it, and formalising it is a cheap and
  worthwhile next step because it would turn §6(2) into a theorem-shaped target.
* **Measured vs. read off**: measured — the corner counts and both controls, all cones and axiom
  sets, the 189-user ripple, the 1549-job build, the three guards, census 13, dup-names, the
  layering grep, and the import closure of §3.3 step 1.  Read off source — the ten gates' bodies
  in `UniqueTyping.lean:200–260`, §3.3 step 2's reprovability, `StrengthenInhabGate.lean` §5's
  two call sites, and §A.2's 31-instrument census, which I relied on for the missing `⊬` control.

---

## 8. The instrument

Identical to `docs/handoff-weakn.md` §7.9's walker plus the two disclosures the standing rule
demands, and a positive control.  Scripts kept at `/tmp/pidescend/{scan,scan2,ripple,holes,movecheck}.lean`.

```lean
-- INSTRUMENT DISCLOSURES (both required by docs/vacuity-ledger.md row 180d):
--  * VALUES ARE READ: `.thmInfo` constants are read via `v.value` directly; everything else via
--    `ci.value? (allowOpaque := true)`.  Types are always read.
--  * INTERNAL NAMES ARE KEPT as graph nodes and are never skipped while traversing; they are
--    filtered only when a *seed list* is reported.  Skipping them undercounted 6 against a
--    true 8 in the round that produced this one, and 131 against 293 two rounds before.
private def depsOf (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | none => {}
  | some ci =>
    let cs := ci.type.getUsedConstantsAsSet
    match ci with
    | .thmInfo v => cs.union v.value.getUsedConstantsAsSet
    | _ => match ci.value? (allowOpaque := true) with
           | some v => cs.union v.getUsedConstantsAsSet
           | none => cs

/-- forward cone of `seed`, not traversing *through* members of `cut`. -/
partial def coneCut (env : Environment) (cut : NameSet) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then coneCut env cut rest seen else
    let seen := seen.insert n
    if cut.contains n then coneCut env cut rest seen else
    coneCut env cut ((depsOf env n).toList ++ rest) seen
```

Import closure for every corner measurement: `Verify.Guard`, `Experimental.ConeJoin`,
`Theory.Typing.StrengthenNarrow`, `Theory.Typing.PiDescendSplit`, `Verify.Typing.ProjGenTerm`,
`Verify.TypeChecker.ProjGenTermWitness`, `Verify.Typing.ProjWeakInvSplit`.  Gate set = the ten
`typingGates` of `scripts/weakn-gate-split.lean`.  Every name is checked with `env.find?` and an
unresolved one is `logError`, never a silent zero.

### 8.3 The corner's 31 hole-reaching seeds, by name (after site 1) [measured]

`projTerm_hasType_of_G`, `TrProj.weakFV'_inv_of_strengthen`, `barField1_hasType_swapped`,
`VIndCtor.swapData`, `VIndCtor.swapDataG`, `OnCtx.swapCtx`, `ftype_hasType_swappedG`,
`bar_swapTele`, `VEnv.HasType.swapSkipped_one`, `ftype_hasType_swapped_exists`,
`projTermG_hasType_of_hreal`, `projGen_iota_step`, `projMotiveTerm_hasType_swapped`,
`constAppDefeqStrengthenRF_of_constRigid`, `ftype_hasType_swapped`,
`TrProj.weak'_inv_of_strengthen`, `projMotiveBody_hasType_guarded`,
`MutField.projTermG_hasType_at_mutual`, `projMotiveTermG_hasType_swapped`,
`VEnv.HasType.swapTele`, `VEnv.IsStructureG.projTermG_hasType`, `bar_swapCtx`,
`projGen_hiota`, `VEnv.IsStructureG.projMotiveTermG_hasType_swapped`,
`TrProj.weak'_inv_of_constRigid`, `VEnv.HasType.swapSkipped`, `projTermG_hasType_aux`,
`VEnv.HasType.swapCtx`, `projMotiveBodyG_hasType_guarded`,
`constAppDefeqStrengthenInh_of_constRigid`, `TrProj.wf`.

`Lean4Lean.OnCtx.of_appendTele` is **absent**; it was present before site 1.
