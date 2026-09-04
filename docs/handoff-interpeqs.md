# handoff-interpeqs — a general `interp (mkPi …)` equation

Round scope: I own exactly `Lean4Lean/Theory/SetModel/InterpMkPi.lean` (new) and this file.
Everything else read-only. Target: the four `interp`-equation hypotheses of
`Lean4Lean.SetModel.eq_singleton_of_mem_interp_mkPi3` (`Theory/SetModel/RecTypePeel.lean`,
arity 27, cone 6316) that the `TeleWF` bridge does **not** discharge: `hmot`, `hmin`, `hmaj`,
`hbody`.

## PRIORS (written before the first measurement)

Numbered so I can score them at round close. These are guesses, not results.

P1. **The absence is real.** I expect `shape.lean` on `interp` + `mkPi` to confirm no general
    equation. My prior on this is high (0.85) *because the orchestrator says it re-ran it
    itself*, and the calibration note says cone/shape figures have been exact all session.
    The residual 0.15 is the "spelled differently" failure: `interp` of a *telescope* may live
    under a name built from `mkForallE`/`foldr`/`VExpr.mkForall` rather than `mkPi`, and a
    shape query keyed on `mkPi` would miss it. **I will search the shape of the CONCLUSION
    (`interp`, `Set.pi`/`^`/`funs`), not the shape of the argument.**

P2. **The general equation will need an induction on the telescope, not a peel count.** The
    three existing instances hardcode 6, 6, 5 layers. I expect the general statement to be
    over a `List VExpr` (or a telescope structure) with `interp (mkPi Δ b) = <dependent
    function space over Δ> `, proved by `List.rec`. Confidence 0.7.

P3. **The `forallE` branch-on-codomain trap will bite and is the crux.** `interp`'s
    `forallE` clause branches on whether the codomain is propositional. So a general equation
    cannot be a single clean `=`; it will either (a) be stated with a hypothesis that pins the
    branch for every layer, or (b) split into two equations. I predict the honest general form
    needs a *per-layer* branch premise, and that the cheapest sufficient premise is a single
    fact about the FINAL codomain plus the observation that the branch is determined by it
    (because the propositional branch is inherited outward). Confidence 0.55 — this is the
    part I most expect to be wrong about.

P4. **`hmin` will need the oracle.** The orchestrator flagged it, and its reason is structural,
    not a guess: `hmin` ties a value to the *constructor's denotation*. A `mkPi` equation is
    about the shape of a Pi type; it says nothing about what a constructor denotes. I expect to
    discharge `hmot`, `hmaj`, `hbody` and NOT `hmin`. Confidence 0.75 that `hmin` survives.
    If so the model side has **two** items, not one, and I will say so plainly.

P5. **Instantiation at the three existing declarations will work for at least one, and
    `ntreeAux` will NOT reach.** `ntreeAux` is a nested inductive; its motive telescope is
    likely not a literal `mkPi` of a known list at the point where my equation would fire.
    Confidence 0.6 that ntreeAux fails, and I expect the reason to be about the nested
    prefix rather than about the equation.

P6. **Layer rule.** My file must not reach `Lean4Lean.Verify.*`. `interp` is model-side so I
    expect this to be free, but `RecTypePeel.lean`'s peels may use a `Verify`-side telescope
    helper, in which case *reproducing* the hand peel could pull me over the line. Confidence
    0.2 that this bites; if it does it is a finding, not an import.

## MEASUREMENTS (appended one line per instrument call, as made)

M1. `grep -n eq_singleton_of_mem_interp_mkPi3 -r Lean4Lean/` → 7 hits, declaration at
    `Theory/SetModel/RecTypePeel.lean:428`. Read lines 380-680. Confirms the brief's nine
    hypotheses verbatim: `hpm hpp hpx` (IsProp), `hmot hmin hmaj hbody` (interp equations),
    `hmk`, `hf`. Also read the only existing firing,
    `Lean4Lean.SetModel.UnitAudit.unitL_denot_eq_singleton_of_zero` (line ~547), which
    discharges all nine at `unitDeclLE`. **Correction to my own P2 framing:** the four
    equations are NOT of the form `interp (mkPi …) = _ ^ _`. Only `hmot` is
    `interp Am = UProp ^ Sv`, and `Am` there is `motTyU u`, itself a one-binder `mkPi`
    ending in `.sort`. `hmin`/`hmaj`/`hbody` are equations about *non-Pi* expressions
    (`minTy`, a `.const`, and an application `.app (.bvar 2) (.bvar 0)`). So the general
    equation the brief asks for is about `hmot` shape only; the other three are different
    shapes and I must classify them separately before claiming any discharge.
M2. Read all three named instances.
    - `Lean4Lean.SetModel.UnitAudit.interpL_motTyU` (`UnitOracleLarge.lean:633`): telescope
      `[.const `Unit1 []]`, **1** binder, RHS `U κ (u.eval ls) ^ ({pt} : V)`. Proof =
      `interp_forallE_type` + `mkForallType_singleton_const` + `interp_sort`.
    - `Lean4Lean.SetModel.EqLargeAudit.motSet_eq_interp_motTyE` (`EqRecLarge.lean:131`):
      telescope `[.bvar 1, eqAp v (.bvar 2) (.bvar 1) (.bvar 0)]`, **2** binders, RHS
      `motSet κ …`. Proof = `interp_forallE_type` + `mkForallType_ext`, **twice**, then
      `interp_sort`.
    - `Lean4Lean.SetModel.IffLargeAudit.motSetI_eq_interp_motTyI` (`IffRecLarge.lean:378`):
      telescope `[iffAp (.bvar 1) (.bvar 0)]`, **1** binder, RHS `motSetI κ …`. Proof =
      `interp_forallE_type` + `EqLargeAudit.mkForallType_ext` + `interp_sort`.
    **CORRECTION to the brief, and it changes the target.** The brief says these have
    "hardcoded peel layers (6, 6, 5)". The 6/6/5 are the layer counts of the *big slice
    theorems* in those files (`rw [interp_forallE_type …]` once per recursor binder, comments
    `-- layer 3 … layer 6`). The three named `interp (mkPi …) = _` equations themselves have
    **1, 2, and 1** binder. So the general equation is not fighting a 6-deep hardcode; it is
    fighting that each is written for a *literal* `.forallE` nest with a *specific* RHS
    spelling. The common shape is exactly:
      `interp M L Γ (mkPi Δ (.sort u)) = <iterated mkForallType over ⟦Δ⟧>` (the TYPE branch),
    and `motSet`/`motSetI`/`_ ^ {pt}` are three different hand-spellings of that iterate.
    Block-specific in each: (i) the RHS name (`U _ ^ _`, `motSet`, `motSetI`), (ii) the
    `¬IsProp` side condition supplied per binder from a per-block lemma
    (`not_isPropL_sortU`, `not_isProp_motInner`/`not_isProp_sortu`, `not_isProp_sortuI`),
    (iii) the domain-identification step (`interpL_Unit1`, `hspec`+`eqFn_value`,
    `hspec`+`iffFn_value`) — that last one is oracle data, NOT typing data.
M3. **(a) ABSENCE VERIFIED BY SHAPE, five queries, all against the compiled environment
    (population: 450 built modules each time).**
    - `HEADS="Lean4Lean.SetModel.interp Lean4Lean.VExpr.mkPi"` → **17** constants, 0 fields.
      Reproduces the brief's 17 exactly. Content: `mem_interp_of_peelP`,
      `appAll_mem_interp_of_peel`, the 12 auto-generated `PeelArgs*`/`PeelArgsP*`
      recursors/constructors/`below`s, and `eq_singleton_of_mem_interp_mkPi3` itself.
      **None is an equation** — the two real ones are `∈`-implications.
    - `HEADS="Lean4Lean.SetModel.interp Lean4Lean.SetModel.mkForallType"` → **3**:
      `interp.eq_def`, `interp.eq_6`, `interp_forallE_type`. All three are the *one-step*
      defining equation. No iterate.
    - `HEADS="Lean4Lean.SetModel.interp Lean4Lean.SetModel.mkForallProp"` → **3**:
      `interp.eq_def`, `interp.eq_6`, `interp_forallE_prop`. Same, other branch.
    - `HEADS="Lean4Lean.SetModel.interp HPow.hPow"` → **4**: `fldDom.eq_1`,
      `UnitAudit.interpL_motTyU`, `UnitAudit.interpL_lhsBody`,
      `eq_singleton_of_mem_interp_mkPi3`. (I had to route through `HPow.hPow`:
      `HEADS="… LO.FirstOrder.SetTheory.function"` returns **0** because `^` is the
      `Pow V V` instance from `Foundation/FirstOrder/SetTheory/Function.lean:114` and the
      *instance* rather than `function` is what appears in types. Recording that so the next
      round does not read that 0 as an absence.)
    - `HEADS="Lean4Lean.SetModel.interp Lean4Lean.SetModel.piProp"` → **0**, heads resolved.
    **Conclusion: the absence is real and is stronger than stated. There is no iterated
    `interp` equation over a telescope in EITHER branch; the only `interp`/`mkForall*`
    equations in the tree are the two single-binder defining lemmas
    `Lean4Lean.SetModel.interp_forallE_type` and `Lean4Lean.SetModel.interp_forallE_prop`
    (`Theory/SetModel/Interp.lean:579` and `:572`).** P1 scored CORRECT.
M4. `lake build Lean4Lean.Theory.SetModel.InterpMkPi` → **GREEN** with §1 in place.
    Proved `Lean4Lean.SetModel.mkForallType_const_cod`:
      `(∀ v ∈ G ρ, F ρ v = Y) → mkForallType G hG F hF ρ = (Y ^ G ρ : V)`
    — i.e. `UnitAudit.mkForallType_singleton_const` with its `G ρ = ({a} : V)` premise
    **deleted**. The singleton premise was doing nothing: the empty-domain case, where
    `mkFamUnion … ρ = ∅ ≠ Y`, still has both sides equal to `{∅}`, and a proof routed through
    `mem_function_iff`/`mem_prod_iff` rather than through `mkFamUnion`'s value never has to
    split on it. Also proved `Lean4Lean.SetModel.mkForallType_singleton_const'` — the
    singleton lemma re-derived as the `G ρ = {a}` corollary, in one line. First half of test
    (d): §1 generalises rather than parallels.
M5. §2 + §3 GREEN. Names, fully qualified:
    - `Lean4Lean.SetModel.not_isProp_sort` — `OnCtx Γ (envF.IsType nv) → v.WF nv →
      ¬ L.IsProp M Γ (.sort v)`, general in `v`. The `v = .zero` case is the tree's existing
      `Lean4Lean.SetModel.not_isProp_sort_zero` (`FalseProp.lean:146`), which I found by shape
      (`HEADS="Lean4Lean.SetModel.PropSplit.IsProp Lean4Lean.VExpr.sort"` → 15 hits, and this
      was the cheapest non-`falseProp` one at arity 9). 4-line proof, same skeleton.
    - `Lean4Lean.SetModel.not_isProp_mkPi_sort` — `¬ L.IsProp M Γ (VExpr.mkPi Δ (.sort v))`
      for a telescope of **any** length, from `isProp_mkPi_iff` + the above.
    - `Lean4Lean.SetModel.interp_forallE_sort` — **the closed-form general equation**:
      `(interp M L Γ (.forallE A (.sort v))).toFun ρ = ((U M.κ (v.eval M.ls)) ^ (interp M L Γ A).toFun ρ : V)`
      Hypotheses: `OnCtx (A :: Γ) (envF.IsType nv)` and `v.WF nv`. **Nothing else** — no branch
      hypothesis, no condition on the domain.
    - `Lean4Lean.SetModel.interp_mkPi_sort_one` — the same, spelled `VExpr.mkPi [A] (.sort v)`.
    - `Lean4Lean.SetModel.interp_mkPi_sort_cons` — the general-`Δ` equation, one layer,
      with the `¬IsProp` side condition **discharged** rather than hypothesised.
    **THE TRAP DOES NOT BITE, and this is a correction to the brief.** The brief warns that
    `interp`'s `forallE` clause branches on the codomain so "both branches must be handled".
    For a **sort-ended** telescope there is only one branch, provably: the level of `.sort v`
    is `.succ v`, and `(.succ v).eval ls = v.eval ls + 1` is never `0`, so `IsProp` is false at
    every layer regardless of `v` — `elimLvl = .zero` included. The prop branch
    (`mkForallProp`) is the right branch for the recursor type's OWN binders (`hpm hpp hpx`,
    which the `TeleWF` bridge already discharges), not for the motive's type. So the
    two-branch requirement was real for the *peel* (`RecTypePeel.lean` §7 vs §4) and is
    **vacuous for the four `interp` equations**. Scored: P3 WRONG — I predicted a per-layer
    branch premise would be needed; the correct answer is that no branch premise exists to
    need.
M6. §4 GREEN — reproduction test (d), first target. `Lean4Lean.SetModel.UnitAudit.interpL_motTyU'`
    re-proves `UnitOracleLarge.interpL_motTyU`'s statement from `interp_forallE_sort` in **three
    rewrites**, none of which mentions `interp_forallE_type`, `mkForallType`, or the branch:
      `rw [show motTyU u = …, interp_forallE_sort (onCtxF hle (onCtxL_unitTy hΓ)) hu,
          interpL_Unit1 L κ ls Γ ρ, unitML_kappa, unitML_ls]`
    and `Lean4Lean.SetModel.UnitAudit.interpL_motTyU_reproduced` proves
      `interpL_motTyU' L κ ls hu hle Γ hΓ ρ = interpL_motTyU L κ ls hu hle Γ hΓ ρ := rfl`
    — `rfl` is typeable only if the two theorems have literally the same type, so this is a
    reproduction and not a restatement. The per-block residue is exactly two things:
    `interpL_Unit1` (the oracle's value at the type constant) and `unitML_kappa`/`unitML_ls`
    (projections of the model data). GREEN.

M7. §5 GREEN — **all four `interp` equations discharged, and NONE of them needs the oracle.**
    `Lean4Lean.SetModel.cnst_eq_singleton_of_mem_interp_recTyG`, conclusion
      `M.cnst tc tus = ({M.cnst cc cus} : V)`
    i.e. the type constant's denotation is the singleton of the constructor's — surjective
    pairing/structure eta, from the recursor's type obligation. Shape (new abbrevs in my file):
      `motTyG tc tus w = .forallE (.const tc tus) (.sort w)`   (motive : T → Sort w)
      `minTyG cc cus  = .app (.bvar 0) (.const cc cus)`        (motive mk)
      `recBodyG       = .app (.bvar 2) (.bvar 0)`              (motive x)
      `recTyG tc cc tus cus w = VExpr.mkPi [motTyG …, minTyG …, .const tc tus] recBodyG`
    General in `tc cc tus cus w v0 Γ ρ f envF env₀ nv M L`. How each of the four goes:
      `hmot`  ← `interp_forallE_sort` + `h0 : w.eval M.ls = 0` + `U_zero` + `interp_const`.
      `hmin`  ← `interp_app_type` (side condition `¬IsProof (motTyG::Γ) (.bvar 0)`, which is
                `not_isProof_bvar_of_typeFormer`) + `interp_bvar` + `snoc_value_at_len`
                + `interp_const`.
      `hmaj`  ← `interp_const`, one step. (`Ax` and the motive's domain are the same closed
                constant, so no weakening is needed at a parameter-free block.)
      `hbody` ← `interp_app_type` (side condition `¬IsProof (const::minTyG::motTyG::Γ) (.bvar 2)`,
                same lemma) + `interp_bvar` twice + `snoc_value_of_lt` twice
                + `snoc_value_at_len` twice, the two extended valuations built by
                `mem_interpCtx_cons` from `hmot`/`hmin`.
    Remaining hypotheses: `hle`, `hΓ`, **`hρ : ρ ∈ interpCtx M L Γ`**, `hw`, `hv0`, `h0`,
    `hT`/`hC` (typings of the type and constructor constants, context-polymorphic — free from
    the `constDF` rule), `hpm`/`hpp`/`hpx` (the bridge's three), `hmk`, `hf`.
M8. §6 GREEN — test (d), second target, `ntreeAux`.
    `Lean4Lean.SetModel.InductiveDeclExamples.interp_ntreeAux_motiveType` (all `t`) and
    `…interp_ntreeAux_motiveType_zero`. The **general equation DOES reach** the parameterised
    nested block at the motive binder: `ntreeAux.motiveType t = mkPi [tyApp' t t []] (.sort
    elimLvl)` (`ntreeAux_motiveType_mkPi`, already in `RecTypePeel.lean` §11), so
    `interp_mkPi_sort_one` fires directly, and `ntreeAux.isLE = true` gives
    `elimLvl = .param 0`, WF as soon as `0 < nv` (`ntreeAux.recUvars = 2`). Per-block residue:
    one hypothesis, `OnCtx (ntreeAux.tyApp' t t [] :: Γ) (envF.IsType nv)` — inductive-typing
    layer data (`VInductDecl'.RecCtx.onCtxMotives` family), not something an `interp` lemma can
    supply.
    **What does NOT reach is §5's assembled theorem**, and the reason is the consumer, not the
    equation: `eq_singleton_of_mem_interp_mkPi3` has exactly **three** binders while
    `ntreeAux.recPiTele j` has **seven** (`ntreeAux_recPiTele_length` = 7 for j = 0 and j = 1:
    one parameter, two motives, three minors, one major). `ntreeAux` is parameterised, has two
    mutually nested members and three constructors with fields — outside the
    zero-field/one-constructor/index-free/parameter-free shape §8 is about. P5 scored HALF
    RIGHT: I predicted ntreeAux would not reach and gave the right kind of reason (the nested/
    parameterised prefix), but I was wrong that the *equation* would not reach — it does; only
    the three-binder consumer does not.

M9. `exists.lean` on nine new names, population **453 built modules**, watching 6 declarations.
    Every one: `FOUND`, `own value is a hole: false`, `cone reaches sorryAx: false`,
    `watched declarations in cone: none of 6`. Cones:
      `Lean4Lean.SetModel.not_isProp_sort`                          arity 11, cone   707
      `Lean4Lean.SetModel.not_isProp_mkPi_sort`                     arity 15, cone  1180
      `Lean4Lean.SetModel.mkForallType_const_cod`                   arity 11, cone  5777
      `Lean4Lean.SetModel.interp_forallE_sort`                      arity 15, cone  6304
      `Lean4Lean.SetModel.interp_mkPi_sort_one`                     arity 15, cone  6308
      `Lean4Lean.SetModel.InductiveDeclExamples.interp_ntreeAux_motiveType`  arity 14, cone 6370
      `Lean4Lean.SetModel.interp_mkPi_sort_cons`                    arity 19, cone  6378
      `Lean4Lean.SetModel.cnst_eq_singleton_of_mem_interp_recTyG`   arity 32, cone  6487
      `Lean4Lean.SetModel.UnitAudit.interpL_motTyU_reproduced`      arity 16, cone  6559
    Note `interp_forallE_sort`'s cone (6304) is *below* the target's 6316 — the general equation
    is cheaper than the theorem it feeds.

M10. `#print axioms` on all twelve new declarations: `[propext]` for the two `not_isProp_*`,
     `[propext, Classical.choice, Quot.sound]` for the other ten. **No `sorryAx` anywhere.**

M11. **THE ORACLE QUESTION, settled — and it contradicts the brief's prior (my P4 too).**
     None of the four `interp` equations needs the oracle interface. `hmin` is the one the brief
     flagged, and the flag is half-right: `hmin` does tie a value to the constructor's
     denotation, but the tie is an **identity**, not a fact about which set the oracle chose.
     With `mkv` *defined* as `M.cnst cc cus`, `hmin` is `interp_app_type` + `interp_bvar` +
     `snoc_value_at_len` + `interp_const` — four steps, no oracle field read. §5 proves it that
     way and builds green.
     The oracle is needed in exactly two places, **neither of them among the four**:
       (i) `hmk : mkv ∈ Sv`, i.e. `M.cnst cc cus ∈ M.cnst tc tus` — `InductOracleOK`'s
           constructor obligation; there is no route to it from typing;
       (ii) *naming* `M.cnst cc cus` concretely, if a consumer wants `{•}` rather than
           `{M.cnst cc cus}` on the right (as `unitL_denot_eq_singleton_of_zero` does, via
           `unitOracleL_mk`).
     Both were already oracle obligations before this round. **So the model side's remaining
     work after this file is NOT a second `interp`-equation item.** It is `hmk` + `hf`, the two
     `InductOracleOK` obligations, and they are the same two items that were there before.
     P4 scored WRONG (I gave 0.75 to `hmin` surviving as an oracle item).

## ROUND CLOSE (e)

R1. `~/.elan/bin/lake build` (whole tree) → **BUILD-GREEN**, no `error:`, no `✖`.
R2. `lake env lean --run scripts/sorry-census-all.lean` (with `--run`, as instructed) →
      `BUILT: 456; in population but NOT BUILT: 0`
      `HOLES over the WHOLE built population, unioned across both passes: 13`
    **census 13, NOT BUILT 0.** (My module is one of the 54 orphans — in a default target,
    built, imported by nothing. Expected for a new leaf file.)
R3. `lake build Lean4Lean.Verify.Guard` → all three:
      guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓
      guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
      guard 3: checker cone implementation gaps within frozen list (2/2 remaining) ✓
R4. In-repo section-variable warnings: `grep -c "warning: Lean4Lean/.*automatically included
    section variable"` over a full build → **0**. (There is one such warning in the build log
    but it is Foundation's, `Foundation/FirstOrder/SetTheory/Z.lean:35`, not in-repo.)
R5. `python3 scripts/layer-check.py` → **exit 0**.
      `HARD RULE: no Theory/SetModel/ module may reach Lean4Lean.Verify.*`
      `ok - 65 module(s) checked, none reaches Verify/`
    My module is one of the 65. P6 scored CORRECT-and-unbitten: nothing in `RecTypePeel.lean`'s
    peel machinery pulled me toward `Verify/`; reproducing the hand peel needed only
    `UnitOracleLarge`'s own `UnitAudit.*`, which is already Theory-side.
R6. No frozen file touched. No state-changing git. `docs/vacuity-ledger.md` untouched.
    Files written this round: `Lean4Lean/Theory/SetModel/InterpMkPi.lean` (new) and this file.

## PRIOR SCORES

P1 CORRECT (absence real, and stronger than stated). P2 WRONG in its framing — I predicted an
induction over a telescope; the truth is that no closed form over a general telescope exists,
and the arity that matters is 1. P3 WRONG — I predicted a per-layer branch premise; there is no
branch premise, `not_isProp_sort` deletes it. P4 WRONG — `hmin` does not need the oracle;
`hmk` does, and `hmk` is not one of the four. P5 HALF — ntreeAux: right that the assembled
theorem does not reach and roughly right about why, wrong that the *equation* would not reach.
P6 CORRECT (and did not bite).
Net: 2 of 6 clean. The three wrong ones were all wrong in the same direction — I expected the
remaining distance to be larger than it is.

## LATE ADDITION — non-vacuity, and a trap I walked into

M12. `Lean4Lean.SetModel.UnitAudit.recTyG_eq_unitDeclLE_recType` (arity 1, cone 699, hole
     false, sorryAx false, none of 6 watched):
       `recTyG `Unit1 `Unit1.mk [] [] u = (unitDeclLE.recType 0).instL [u]`
     proved as `(unitDeclLE_recType_instL_mkPi u).symm`, axioms `[propext]` only. §5's shape is
     `unitDeclLE`'s recursor type **on the nose** — `motTyG `Unit1 [] u = motTyU u`,
     `minTyG `Unit1.mk [] = minTy` (`UnitOracleWitness.lean:103`), `recBodyG = .app (.bvar 2)
     (.bvar 0)`. So `cnst_eq_singleton_of_mem_interp_recTyG` is not vacuous: its hypotheses
     are instantiable at a declaration whose `InductOracleOK` witness the tree already has
     (`UnitAudit.inductOracleOKL`).

M13. **Process trap, recording it because it nearly cost me a silent hole.** I first wrote that
     witness *before* the section that defines `recTyG`. `autoImplicit` is on in this repo, so
     `recTyG` was silently bound as an implicit variable of unknown type and the declaration
     elaborated to a **hole**: `depends on axioms: [propext, sorryAx]`. The whole-file build was
     RED only because of a downstream "Function expected" error; had the application happened to
     typecheck, I would have had a green `sorryAx` declaration in a file whose census line reads
     13. The `#print axioms` block at the bottom of the file is what surfaced it. Keep that
     block; a file without one can hide this.

## FINAL ROUND-CLOSE NUMBERS (re-run after M12)

  whole-tree `lake build`                        BUILD-GREEN
  `scripts/sorry-census-all.lean --run`          BUILT 456, NOT BUILT 0, HOLES 13
  guard 1 (24 frozen axioms)                     ✓
  guard 2 (kernel_sound within whitelist)        ✓ (proof INCOMPLETE: sorryAx present)
  guard 3 (impl gaps, 2/2 remaining)             ✓
  in-repo section-variable warnings              0
  `scripts/layer-check.py`                       exit 0, 65 SetModel modules, none reaches Verify/
