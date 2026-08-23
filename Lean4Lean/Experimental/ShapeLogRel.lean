/-
================================================================================
MIGRATION WIP -- HANDOFF NOTE.  READ ALL OF THIS BEFORE TOUCHING EITHER FILE.
================================================================================

!! NAME PREFIX: `namespace SExpr` opens at :856 and IS NEVER CLOSED.  Every declaration in
!! this file is `Lean4Lean.SExpr.<name>`, NOT `Lean4Lean.<name>`.  `#print axioms
!! Lean4Lean.LE_Interp.join'` answers "unknown constant" -- which reads as "declaration
!! missing" and is not.  Use the short name (namespaces are open at EOF) or the real prefix.
!! Do NOT probe near :6152 -- that bare `end` closes a `mutual`, not a namespace.

!! LINE NUMBERS GO STALE THE MOMENT THIS BANNER IS EDITED.  An error-position -> declaration
!! mapping computed against an older copy yields a PLAUSIBLE WRONG ANSWER, not an error --
!! same class as the primed-name regex below.  Re-derive positions from the same build.

!! 49 OF 653 DECLARATIONS IN THIS FILE ARE `sorryAx`-BACKED BY ERROR RECOVERY.  They read in
!! source exactly like proofs.  DO NOT infer proof status from source text; run `#print
!! axioms`.  Full list: banner section 14.

## 0. The two-file rule (breaks the tree if ignored)

These two files must be restored TOGETHER:
    scratchpad/SExpr.indTy-wip29.lean       -> Lean4Lean/Experimental/SExpr.lean
    scratchpad/ShapeLogRel.indTy-wip29.lean -> Lean4Lean/Experimental/ShapeLogRel.lean

`Classification.indTy` carries a `rel : Bool` and `CtorBundle` carries `hrel` instead of
`hu0` in SExpr.lean; the pristine ShapeLogRel.lean calls `.indTy` with one argument and reads
`hu0`.  Restoring one alone does not compile.  After restoring SExpr.lean you MUST
`lake build Lean4Lean.Experimental.SExpr` before measuring ShapeLogRel.lean, or you are
measuring against a stale `.olean`.  (The "144 instances / 105 lines" recorded at an earlier
handoff was exactly that mistake: the byte-identical file measures 181/132 on a fresh build.)

State: **12 error instances at 12 distinct lines.**  NOT green.  Measure with
    lake env lean -DmaxErrors=600 Lean4Lean/Experimental/ShapeLogRel.lean
`set_option maxErrors` does NOT take in-file, so a raw `lake build` count is a FLOOR.
Do not use the FRONT line number as a metric while the banner is being edited.

## 0a. WHAT THE 12 ERRORS ARE

  (A) THE JOIN FAMILY -- 8 instances: `WShape.HasType.join`'s `go_dom` and `go_pi`,
      `WShape.HasDom.join`, `LE_Interp.compat_join`, `LE_Interp.sound_lam` (x2),
      `LRS.PiDefEq.join` (x2).
      **The approved `LE_Interp`-relative repair is REFUTED.  See section 4.**

  (B) SECTION 7's RESIDUE -- 1 instance, in `LE_Interp.build_spine`'s `.ctor'` branch.
      Section 7 has LANDED in part: `WShape.HasType.proofIrrel` is now TRUE and PROVED.
      What is left is that a `Prop`-valued inductive's constructor application must carry
      shape `.bot`, and `WShape.ctor'` cannot see `Prop`-ness yet.  See section 7.

  (C) THE `extra_pat` PEEL -- 2 instances, in `LE_Interp.strongSoundS`'s `extra` case.
      The price of removing a VACUITY, not a regression.  See section 9.

  (D) PER-LEAF LEVEL LISTS -- 1 instance, in `LE_Interp.Const.compat_join`'s `pat`/`pat` case.
      Removes the SECOND `ParamsExtra` vacuity; one obligation left.  See section 11.

## 1. What this migration is for -- AND WHAT HAS LANDED

`CtorBundle.hu0 : u <> .zero` was FALSE (`CtorBundle Eq.refl` uninhabited: `Eq.refl`'s sort is
`imax (u+1) (imax u 0) = 0`).  **REPAIRED; `LE_Interp.build_spine`'s `hu0` use is green.**
`hu0` is replaced by

    hrel : rel = true <-> u <> .zero

which is not an invented hypothesis: it is `ParamsExtra.ctor_ty`'s existing
`(rel = true <-> D.lvl <> .zero)`, now readable off the head constant because
`Classification.indTy` carries the boolean.  `build_spine`'s telescope helper was strengthened
from "propagates `<> .zero` downwards" to the full equivalence (`SLevel.imax_eq_zero` was
already an iff), and the head's type-shape is `.sort rel` with `decide (u_body <> .zero) = rel`
discharged from `hrel`.

The `.type`-as-universe -> `IsType` migration is COMPLETE across the file.  Helpers added:
`WShape.HasType.toIsType` (replaces `toType`), `WShape.HasType.bot_bot` /
`TShape.HasType.bot_bot`, `WShape.IsType.not_lam` / `.not_ctor`, `WShape.indTy_join_indTy`,
`WShape.IsType.common_of_le`, `Shape.HasType.indTy_false_bot` /
`WShape.HasType.indTy_false_bot`.

## 2. SIX REFUTED STATEMENTS -- do not re-propose these

Witnesses are in `section CounterexampleProbe` (and, for (f), just after
`LE_Interp.compat`).  `cx_refutes`, `j_refutes`, `le_interp_common_fails` are full
`not-forall` proofs; `lam_join_fails`, `hasDom_escape_fails` are `rfl`-checked computations.

  (a) `WShape.IsType.common` : Compat a a' -> a.IsType -> a'.IsType ->
                               exists r, a.HasType (.sort r) /\ a'.HasType (.sort r)
      FALSE.  Witness `cxA`/`cxA'`.  Mechanism: `ShapeFun.Compat`'s obligation on VALUES is
      guarded by the KEYS, so the pair that would force `false = true` has incompatible keys
      and never fires.  Join-closure and monotonicity of `ShapeFun.WF` were BOTH checked and
      are SATISFIED -- `WF` is not where a proof attempt dies.  The declaration is DELETED
      (it had zero consumers); `WShape.IsType.common_of_le` is its true form (section 4).

  (b) `WShape.HasType.join`     -- FALSE (`j_refutes`).  Already shares `a`, so "restrict to
                                   equal domains" is NOT a repair.
  (c) `WShape.HasDom.join`      -- FALSE (`hasDom_escape_fails`).
  (d) `WShape.HasTypeLam.join`  -- FALSE (`lam_join_fails`), so `go_lam` dies too.
  (e) `WShape.HasType.proofIrrel` under the *un-gated* `ctor` rule -- FALSE.  **This one is
      now FIXED rather than merely recorded**; see section 7.  `proofIrrel_gated` is the
      regression test.
  (f) **NEW AND IMPORTANT.**  The `LE_Interp`-relative repair of the join family:

          LE_Interp rho a.T A -> LE_Interp rho a'.T A -> a.IsType -> a'.IsType ->
            exists r, a.HasType (.sort r) /\ a'.HasType (.sort r)

      is FALSE (`le_interp_common_fails`).  See section 4.

## 3. THE THREE DIAGNOSIS SENTENCES

  * A Pi-shape's shared codomain sort constrains the family's VALUES, never its DOMAINS.
  * The `<=` relaxation is on the KEY, never on the TYPE.
  * `Shape.join` is not a join in the typed sense.  It joins SHAPES; `hasType` is not closed
    under it.  Any lemma asserting that joining preserves typing is asking `Shape.join` to be
    something it isn't.

## 4. THE JOIN FAMILY: THE APPROVED REPAIR IS REFUTED, AND WHAT IS TRUE INSTEAD

The approved plan was: all seven consumers sit under `LE_Interp.compat_join` at the SAME `M`,
so "both shapes realize the same term" is an invariant already in scope, and adding it to the
join lemmas records a fact the callers hold.  The premise of the supporting argument -- that
`LE_Interp.Const.indTy`'s boolean is a function of the head constant -- is now
machine-checked (`Const.compat_join`'s `indTy`/`indTy` case discharges by `injection` on
`classify c`).

**The conclusion still does not follow.**  `le_interp_common_fails` is a sorry-free
`not-forall` proof.  The escape is

    LE_Interp.bvar : m <= rho i -> LE_Interp rho m (.bvar i)

which puts NO condition on `rho`.  `cxA.Compat cxA'` holds, so `WShape.Compat.iff` hands us an
upper bound -- their join -- and setting `rho i` to it makes BOTH realize `.bvar i` under the
SAME valuation.  The join is classified by no sort, so no common sort exists.  The
`Const.indTy` argument is correct *for `.indTy` shapes reached through `Const`*; it does not
reach `bvar`, where the shape comes from the valuation and nothing forces it through `Const`.

    THE DEFECT IS THAT `compat_join` QUANTIFIES OVER AN ARBITRARY `rho` WITH NO
    WELL-FORMEDNESS HYPOTHESIS.

That is the same shape of defect as `SExpr.IsDefEq.strong`'s missing `Ctx.WF` and
`VEnv.Params.pat_wf`'s missing `OnCtx`, now on VALUATIONS rather than contexts.  PLAN.md
already records the rule: *a statement about an arbitrary context with no well-formedness
hypothesis should be treated as suspect by default on this project.*  Valuations are the
third instance.  `rho i := cxA.join cxA'` is a shape that has NO TYPE AT ALL; `Valuation.Fits`
never produces one, but `compat_join` does not ask for `Fits`.

**WHAT IS TRUE** (`WShape.IsType.common_of_le`, proved, three lines of `HasType.retype`):

    a <= z -> a' <= z -> z.IsType -> a.IsType -> a'.IsType ->
      exists r, a.HasType (.sort r) /\ a'.HasType (.sort r)

`Compat a a'` says *some* upper bound exists; what is needed is a **classified** one.  So the
question for whoever takes this next is not "is co-realizability enough" (it is not) but:

    CAN EACH CALL SITE PRODUCE A CLASSIFIED UPPER BOUND, AND IF SO, FROM WHERE?

The obvious candidate `a.join a'` is circular -- its classification is what is being proved.

### COSTED: threading `Fits` DOES NOT REACH THE CALL SITES.  Scoped before writing any lines.

Of the 8 join-family error sites, **5 have no valuation in scope at all** -- not "no `Fits`",
no `rho`:

  | site                                   | enclosing declaration      | rho? | Fits? |
  |----------------------------------------|----------------------------|------|-------|
  | `go_dom`, `go_pi`               (2)    | `WShape.HasType.join`      | NO   | no    |
  | `WShape.HasDom.join`            (1)    | (derived from `go_dom`)    | NO   | no    |
  | `h4.isType.join ac a4.isType`   (1)    | `LE_Interp.compat_join`    | yes  | NO    |
  | `(hi3 x h).isType`, `hT1.isType.join'` (2) | `LE_Interp.sound_lam`  | yes  | NO*   |
  | `htB1.join hC_b htB2`, unsolved (2)    | `LRS.PiDefEq.join`         | NO   | no    |

  (*) `sound_lam`'s single caller, `strongSoundS:5770`, does have `W : Fits`, so `sound_lam`
  and `sound_forallE` COULD take one.  Nothing else can.

`WShape.HasType.join` and `WShape.HasDom.join` are shape-lattice lemmas: there is no `rho`
anywhere in their statements.  `LRS.PiDefEq.join`'s consumer is `LogRel.join_ty`, a FIELD of
the abstract `LogRel` structure --

    join_ty : m1.Compat m2 -> m1.IsType -> m2.IsType ->
              TyDefEq A B m1 -> TyDefEq A B m2 -> TyDefEq A B (m1.join m2)

-- which is parameterised by `Gamma` and `n` only.  There is no valuation to thread, ever.

Adding `Fits` to `compat_join` would also push into `LE_Interp.compat` / `.join'` and thence
into `LE_Interp.subst` and `LE_Interp.inst`, which are iff-statements about substitution with
no `Fits` and no caller that has one.

### SO THE HYPOTHESIS HAS TO BE THE CLASSIFIED UPPER BOUND ITSELF, CARRIED AS AN ARGUMENT

The one encouraging structural fact, checked against the definitions but NOT machine-checked:
a classified upper bound PROPAGATES DOWNWARDS through the recursion.  If `z.IsType` and
`m1 <= z`, `m2 <= z` with `m1 = .forallE a b`, `m2 = .forallE a' b'`, then `forallE_le` gives
`z = .forallE za zf` with `a <= za` and `a' <= za`, and `z.IsType` unfolds to
`HasTypePi zf za r`, whose `HasDom zf za` gives `za.IsType` by `HasDom.isType`.  So `za` is a
classified upper bound for the DOMAINS -- exactly what `go_dom` needs -- and `zf`'s values
serve one level further down.  A single `exists z, m1 <= z /\ m2 <= z /\ z.IsType` at the top
may therefore be enough for the whole family.

### COSTED AT `Adequacy:89`.  IT CLEARS -- BUT NOT BY AN UPPER BOUND.

A common CLASSIFIED UPPER BOUND is NOT producible there.  `InterpTyped.hsort` /
`InterpTyped.hsort'` yield a bound PER SHAPE, and joining the two to get a single one needs
`LE_Interp.join'`, which is `compat_join.2` -- one of the eight broken sites.  Circular.

**But a common SORT is producible, and by a better route.**  `InterpTyped.hsort'` gives, for
each shape realizing `A`, an upper bound classified at `.sort (U <> .zero)` -- and that
boolean is a function of `U`, THE UNIVERSE `A` LIVES AT, not of the shape.  So the two bounds
carry the SAME sort, and `HasType.retype` pulls the classification back down each of them
separately.  No join, no circularity.  That is `LE_Interp.common_sort`, PROVED (search for it
next to `InterpTyped.hsort`):

    (H : forall {b}, LE_Interp rho b A -> InterpTyped rho b A (.sort U)) ->
    LE_Interp rho a.T A -> LE_Interp rho a'.T A -> a.IsType -> a'.IsType ->
      exists r, a.HasType (.sort r) /\ a'.HasType (.sort r)

`Adequacy:89` has every hypothesis: `HA : IsDefEqStrong Gamma A A' (.sort u)` fixes `u`,
`(LE_Interp.soundS HA W.fits).2` IS the `H` (it is already used three times in the same
proof), `hA1` and `ha'` realize the same `A`, and `hp.isType` / `ht.isType` are the two
`IsType`s.  So if `LogRel.join_ty`'s two `IsType` hypotheses become
`m1.HasType (.sort r) -> m2.HasType (.sort r)` at a SHARED `r`, `Adequacy:89` discharges it.
That is "strengthen a hypothesis the caller already has", the sanctioned shape.

    SO THE CHAIN IS NOT DEAD.  BUT THE `exists z` FRAMING IS THE WRONG ONE, AND SO IS MINE
    FROM THE PREVIOUS HANDOFF: THE COMMON SORT COMES FROM THE TERM'S UNIVERSE, NOT FROM THE
    SHAPES AND NOT FROM AN UPPER BOUND.

### WHAT IS STILL OPEN, AND IT IS NOT AT `Adequacy`

A shared sort AT THE TOP does not reach `go_dom`.  That is diagnosis sentence 1: a Pi-shape's
shared codomain sort constrains the family's VALUES, never its DOMAINS.  `go_dom` needs the
two DOMAINS to share a sort, and the domains correspond to the DOMAIN TERM `B1`, whose own
universe is what fixes their boolean.  So the fact has to be re-supplied at every level from
the accompanying term, not propagated from the level above.

`join_ty`'s other consumer, `LRS.PiDefEq.join`, sits at the `LogRel` layer, where the
shape/term link is `TyDefEq`, not `LE_Interp` -- so `common_sort` is not applicable there.
`ValTyPi2` DOES carry the domain term and its universe (`Gamma |- B1 == B2 : .sort u`), so the
information is present; what is missing is a `LogRel` field connecting a validated type's
shape to that universe, something like

    ty_sort : TyDefEq A B m -> m.IsType -> Gamma |- A == B : .sort u ->
              m.HasType (.sort (u <> .zero))

### COSTED.  NOT CIRCULAR WITH `sort_inv`, AND IT DOES NOT NEED THE UNIVERSE AT ALL.

**Circularity check first, and it comes out negative.**  I called `ty_sort` "essentially the
substance of `sort_inv`"; that was too pessimistic.  `sort_inv` needs the LEVEL (`u ~~ v`);
the shape model needs only the BOOLEAN `decide (u <> .zero)`, and the boolean is recoverable
from a `SoundEq` between sorts by `LE_Interp.le_sort`, whose entire proof is a two-case
induction on `LE_Interp` (`bot`, `sort`) and touches nothing.  The technique is already used
in `build_spine`'s `imax` argument (`... .le_sort'` then `WShape.sort_le.1` then `injection`).
So there is no circularity here, unlike the three earlier cases.

**And the universe is not needed either.**  Stating the field with `u` in it forces the caller
to reconcile two universes; `LRS`'s `join_ty` `forallE` case has `hBB : ... : .sort u` from
`h1` and `hBB' : ... : .sort u'` from `h2`, over the SAME `B1 B2` (after the two `determ`s).
Applying a universe-carrying `ty_sort` twice would leave `decide (u <> 0)` against
`decide (u' <> 0)`.  Dropping the universe removes the problem:

    join_sort : m1.Compat m2 -> TyDefEq A B m1 -> TyDefEq A B m2 ->
                m1.IsType -> m2.IsType ->
                exists r, m1.HasType (.sort r) /\ m2.HasType (.sort r)

-- i.e. `IsType.common` relativised to `TyDefEq` at a common `A B`, the same move `common_sort`
makes one layer down.  `join_ty` ALREADY has `hC : m1.Compat m2`, so the caller supplies
nothing new.

**Why it should be provable, case by case.**  `Shape.IsType.common_of_not_forallE` (PROVED,
just above `WShape.IsType.common_of_le`) says `Compat` alone pins the sort in THIRTY-FIVE of
the thirty-six constructor pairs; `cx_refutes`'s counterexample is confined to
`forallE`/`forallE`.  Concretely `Compat` kills every cross-constructor pair, `.bot` is
classified at every sort, `.sort`/`.sort` are both classified only at `.sort true`,
`.indTy`/`.indTy` have equal booleans by `Compat`, and `.lam`/`.ctor` are excluded by
`IsType`.  At `forallE`/`forallE`, `ValTyPi2` supplies what `Compat` cannot: both
`PiDefEq`s carry `IH.TyDefEq (F1.inst a) (F2.inst a) (f_i.app p)` over the SAME `F1 F2`, so
the recursion at `n` applies to corresponding codomain values -- take the bot-keyed element
that `ShapeFun.WF` guarantees (`WShapeFun.bot_mem`).  Two sub-cases: if some value is not
`.bot` its sort is unique and pins `r_i`; if every value is `.bot` then `HasTypePi f_i b_i r`
holds for EVERY `r` and either choice works.

ESTIMATE: one recursion on `n`, thirty-six cases of which thirty-five are `Compat`-closed,
plus the two-sub-case argument at `forallE`.  Call it 40-80 lines.  NOT machine-checked as a
whole -- what IS machine-checked is `common_of_not_forallE`, which is the half where
`cx_refutes` bites.

## 5. `PUnit.{u}` -- `.indTy` cannot carry a CONSTANT-level boolean by `decide`

`PUnit.{u} : Sort u` is `Prop`-valued at `u = 0` and `Type`-valued at `u > 0`, and
`PUnit.unit` must be classified as a constructor.  So no single boolean is correct for a
constant computed syntactically; `IsNeverZero` is wrong for `PUnit.{1}` and `not (. ~~ .zero)`
is wrong for `PUnit.{0}`.  The boolean is therefore bound EXISTENTIALLY in
`ParamsExtra.ctor_ty` and tied propositionally, NOT by `decide`.  `CtorBundle.hrel` is the
same tie one layer down; `build_spine` converts it to `decide (u_body <> .zero) = rel` only
AFTER `u_body` is a concrete term.

## 6. THE THREE-WAY TENSION, AND HOW IT WAS RESOLVED

    (i)   `Eq.refl` is classified as a constructor (its iota-rule needs a `.ctor` leaf),
          so it gets a `.ctor` shape;
    (ii)  `Eq` is `Prop`-valued;
    (iii) `proofIrrel` says everything at a `Prop` has shape `.bot`.

These three cannot all hold.  THREE resolutions were refuted, each machine-checked:
  - `hu0` asserted (ii) never happens for classified constructors -- `Eq.refl` refutes it;
  - the sort-polymorphic `.indTy` rule dropped the distinction -- `proofIrrel` refutes it;
  - the parameterisation RECORDED the distinction without ACTING on it in `HasTypeU.ctor`
    -- the witness now kept as `proofIrrel_gated`'s history refutes it.
The fourth, denying (i), is section 7 and is the one that works.

## 7. SECTION 7 HAS LANDED IN PART.  `proofIrrel` IS PROVED.

What was done (three edits, and it is the whole of the shape layer's side):

  * `Shape.hasType`'s clause `| _+1, .ctor _ _, .indTy _ => true` became
    `| _+1, .ctor _ _, .indTy r => r`;
  * `Shape.HasTypeU.ctor` and `WShape.HasTypeU.ctor` were gated to `.indTy true`;
  * `Shape.HasType.indTy_false_bot` / `WShape.HasType.indTy_false_bot` are the new fact --
    `.indTy false` classifies only `.bot` -- and `WShape.HasType.proofIrrel`'s new `indTy`
    case is one line of it.

`proofIrrel_gated` is the regression test.  Nothing else in the file broke.

WHAT IS LEFT, AND ITS MEASURED COST.  `LE_Interp.build_spine` builds the shape of a
constructor application as `WShape.ctor' c rargs.reverse`, pinned by `LE_Interp.Matches.app`.
For a `Prop`-valued inductive that shape must be `.bot` -- the application is a proof.
`WShape.ctor'`'s existing `.bot` fallback is guarded by `IsStruct c` (i.e. `classify c` is
`.etaCtor`), not by `Prop`-ness, and `Classification.ctor` does not carry the boolean, so the
guard cannot be written.  So the remaining change is:

    Classification.ctor (arity) (rel) and .etaCtor (params args) (rel),
    then `WShape.ctor'`'s `dif` gains the `Prop`-ness disjunct.

### TWO CHEAPER ROUTES WERE CHECKED FIRST.  BOTH ARE CLOSED.

**(i) Get `rel` from `CtorBundle.hclI` instead of from `Classification.ctor`.**  NO.  `rel`
IS in scope at `build_spine`'s failing site -- the bundle is right there.  But the boolean is
needed at a COMPUTATION, not at a proof obligation: the shape is
`WShape.ctor' c_a rargs_a.reverse`, pinned by `Matches.app`'s index, and `ctor'` is a `def`
whose `dif` guard must be decidable from `c` alone.  A `CtorBundle` exists only as a
hypothesis inside `IsDefEqStrong.const` / `StrongSoundCore.const`; `Matches` and `ctor'` are
elaborated with `[Params]` only.  No fact can make a computed term `.bot`.
Nor can the site dodge by choosing a different type-shape `a` for `apps_realize`: `a` must
satisfy BOTH `(.ctor' c l).HasType a` (which, after section 7's gating and
`WShape.indTy_le`, forces `a = .indTy true`) and `LE_Interp rho a.T T` (which the
`Const.indTy` chain gives only at `.indTy rel`).

**(ii) Relax `Matches.app`'s index from `= .ctor' c' rargs'.reverse` to `<=`, so the
`Prop`-valued case can pick `.bot` without any datatype change.**  NO -- this refutes
`LE_Interp.Matches.unique`.  `unique` recovers `c'` and `rargs'` FROM the index shape (see its
proof: `head_wf` gives `classify c'` is a `.ctor`, hence `IsStruct c' = false`, hence `ctor'`
takes its `.ctor` branch, hence the shape is injective in `rargs'`).  Under `<=`, two
derivations with different `rargs'` share the index `.bot :: rargs` and produce different
path-maps.  Analysed, not machine-checked -- stating it needs the datatype change first.

### AND THE SAME MECHANISM IS WHY THE `dif` DISJUNCT IS NOT "ONE MORE DISJUNCT"

    The existing `.bot` fallback is INFORMATION-PRESERVING.  A `Prop`-ness fallback would be
    INFORMATION-DESTROYING.

`WShape.ctor'`'s `.bot` branch fires exactly when `IsStruct c /\ not (ListNonZero l)`, and
`ListNonZero l` is `exists x in l, not (x <= .bot)` -- so the branch fires ONLY WHEN EVERY
ARGUMENT IS ALREADY `<= .bot`.  Nothing is lost: `rargs'` is still recoverable (it is all
`.bot`), which is why `matches_inter`, `Const.compat_join` and `unique` survive today.  A
disjunct keyed on `Prop`-ness fires with ARBITRARY arguments, and those three lose the
recovery.  They do not merely "stop working"; `unique` looks FALSE.

So section 7's residue is a genuine fork:

  (alpha) `ctor'` falls back to `.bot` for `Prop`-valued inductives
          => `Matches.unique` (and probably `matches_inter`) must be restated or is false.
          Cost: 107 instances PLUS that.

  (beta)  `Pattern.WF` requires `rel = true` at constructor leaves, so a `Prop`-valued
          inductive's iota-rule is simply not a `Pattern`.
          **REFUTED -- see `eq_large_eliminates` in `section CounterexampleProbe`.**
          The premise was PLAN.md's small-elimination fact: the major premise is a proof, so
          the whole redex is a proof and has shape `.bot`.  `Eq` is a `Prop` that LARGE-
          eliminates -- `@Eq.rec`'s motive is `Sort u_1` -- so `Eq.rec ... (Eq.refl a)` at a
          `Type`-valued motive is a `Nat`, not a proof.  Small elimination covers `Acc.rec`
          and `Quot.lift`-over-a-`Prop`; it does not cover the subsingleton eliminators, and
          `Eq` is the one that started this.
          Consequence: `Params.pat_wf` + `ParamsExtra.extra_pat` would make `ParamsExtra`
          UNSATISFIABLE for any environment containing `Eq` -- every real one.  Nothing in the
          tree would notice, because there is no `ParamsExtra` instance; every downstream
          result would go silently vacuous.  `ParamsExtra`'s docstring records that this
          project has already been burned by exactly that once.

  (gamma) Decouple at `LE_Interp.const`'s `HasType` premise, so `Eq.refl` keeps its `.ctor`
          shape without being classified by a `Prop`-valued inductive.
          **REFUTED -- see `ctor_not_prop_typed` in `section CounterexampleProbe`.**
          Probed by actually removing the premise: 36 errors, all mechanical arity fixes
          EXCEPT one, at `strongSoundS`'s `const` case, which builds
          `InterpTyped ρ m (.const c ls) A` with that premise LITERALLY as the `HasType`
          field (`.mk b3 (.const b1 b2 .rfl b4 b5 b6 b7) b5 b4` -- `b4` twice).  There is
          nothing else to put there.  And the reason is not about where the premise sits:
          `ctor_not_prop_typed` says **no shape both classifies a `.ctor` and is itself
          `Prop`-valued**, so `InterpTyped`'s slot cannot be filled for `Eq.refl` at its
          natural shape wherever the premise lives.

ALL THREE ROUTES ARE CLOSED.  Section 7's residue is a DESIGN PROBLEM, and the sharpest
statement of it is this:

    Section 7 makes `proofIrrel` true by ruling that a `.ctor` shape is never classified by a
    `Prop`-valued inductive.  But `Eq.refl` must HAVE a `.ctor` shape (its iota-rule's pattern
    needs a `.ctor` leaf, and `Eq` LARGE-eliminates so that rule cannot be dropped), and it
    must BE TYPED (`InterpTyped` demands a classifying shape for every realized term).  Those
    two are now inconsistent for one and the same term, and no relocation of a premise
    reconciles them -- the obstruction is `ctor_not_prop_typed`, which mentions neither
    `LE_Interp` nor `Params`.

Anything that resolves it must give up one of: `proofIrrel` at `Prop`-valued inductives; the
`.ctor` leaf in iota-patterns; or `InterpTyped`'s totality on realized terms.

MEASURED, not estimated (probe run and reverted):
  * SExpr.lean side: **2 edits and it compiles clean** -- the inductive plus
    `Classification.arity`, and one restatement of `Pattern.WF`'s `.const` clause from
    `cl c = some (if top then .symb n else .ctor n)` to
    `if top then cl c = some (.symb n) else exists r, cl c = some (.ctor n r)`.
  * ShapeLogRel.lean side: **107 error instances at 60 distinct lines**, BEFORE `ctor'`'s
    guard is touched at all.  Most look mechanical (pattern arity, unpacking the
    existential), and it is the same order as the `IsType` migration that went 181 -> 9.
  * On top of that, `ctor'` has 59 occurrences and the `.bot`-branch discharges in
    `Matches.matches_inter`, `Const.compat_join` and `unique` currently use `head_wf` +
    `IsStruct` and will stop working.  That risk is unmeasured.

The banner's earlier estimate ("one more disjunct in an existing `dif`") was WRONG twice
over: the disjunct is one line, but the boolean it tests costs 107 instances to introduce,
AND the disjunct is not analogous to the one already there -- see the
information-preserving/destroying paragraph above.

## 9. `ParamsExtra.extra_pat` WAS UNSATISFIABLE.  IT IS NOW λ-PEELED.

`SExpr.ParamsExtra.extra_pat` asked for `p.MatchesS (.instL ls (.mk df.lhs))` on the
**unpeeled** left-hand side.  `Pattern.MatchesS` bottoms out at `const` and never accepts a
`lam` (`Pattern.MatchesS.not_lam`, proved in the same file), and both `SExpr.mk` and
`SExpr.instL` are structural on `lam`, so a binder in `df.lhs` survives both.  Every rule
shape in a real environment has binders -- `quotDefEq.lhs` is `fun α r β f c a => ...`, and an
iota-rule's lhs is `mkLams (iotaCtx C) _` with `iotaCtx` never empty.

    => NO `ParamsExtra` INSTANCE EXISTED FOR ANY REAL ENVIRONMENT, and `LE_Interp.strongSoundS`
       carries `[ParamsExtra]`, SO IT AND EVERYTHING DOWNSTREAM OF IT WAS VACUOUS.

This is `PLAN.md`'s original "`extra_pat` is unsatisfiable" finding.  The MAINLINE
`VEnv.Params.extra_pat` was cured by λ-peeling (that is what `Pat.extra` /
`Pat.extra_delta` / `Pat.extra_quot` / `Pat.extra_iota` in `Theory/Typing/PatternRules.lean`
are for); this copy never was.  The field now mirrors the mainline:

    exists Δ L R p r m1 m2 dfs,
      instL ls (mk df.lhs) = SExpr.mkLams Δ L /\ instL ls (mk df.rhs) = SExpr.mkLams Δ R /\
      Pat p r /\ p.MatchesS L m1 m2 /\ ... /\
      (forall a b A, (A,a,b) in dfs -> Δ.reverse ++ Γ |- a == b : A) /\ R = r.1.applyS m1 m2

Two REGRESSION TESTS land with it, in `SExpr.lean` just after the class, stated as
conditionals on a hypothetical unpeeled field so that they cannot rot:
`SExpr.unpeeled_extra_pat_unsatisfiable` (any `lam`-headed lhs gives `False`) and
`SExpr.iota_lhs_lam` (every iota-rule's lhs IS `lam`-headed).  Anyone who un-peels the field
can instantiate the first with it and read off `False`.  Both are
`[propext, Quot.sound]`, no `sorryAx`.

COST, MEASURED: `SExpr.lean` compiles clean (the peel plus a small `SExpr.mkLams`).
`ShapeLogRel.lean` gains exactly **2 errors, both in `strongSoundS`'s `extra` case**, and they
are honest: both sides are now `mkLams Δ _` and the matched redex is the BODY.  Running the
existing argument under `Δ` needs
  (a) a congruence "`LE_Interp` respects the body of a `.lam`" -- a short `cases` on the
      `lam`/`bot` rules, and the binder `A` is shared by both sides; and
  (b) the two IHs and `W` transported under the telescope, which needs `StrongSound`
      inversion through `lam`.
Neither is written.  `iota_lhs_lam` is proved from `Theory/Inductive/Decl.lean` alone, so
this file still does NOT import `Theory/Typing/PatternRules.lean`.

## 10. THE THREE SECTION-7 EXITS, COSTED.  THE CHOICE IS BINARY.

Measured by probe (each applied, counted, reverted).  Baseline is 11.

### Exit 1 -- give up `proofIrrel` at `Prop`-valued inductives.  **1 case.  FALSE, not vacuous.**

Deleting `WShape.HasType.proofIrrel` / `TShape.HasType.proofIrrel` costs exactly **one new
error**, in `strongSoundS`'s `proofIrrel` case, plus one use at `ShapeLogRelAdequacy:428`.
Nothing else in either file touches it.

But the case does not merely become unproved -- it becomes FALSE.  It has to show
`forall rho m, LE_Interp rho m h <-> LE_Interp rho m h'` for two UNRELATED proofs of the same
`Prop`.  The only way a bi-implication holds for every `m` is if every shape realizing either
side is `<= .bot`, and `LE_Interp.bot` then gives both directions.  So collapsing proofs to
`.bot` is not *a* route to that case -- it is its entire content.  Concretely: undo section
7's gating and `Eq.refl` gets a `.ctor` shape via `Const.ctor`, so
`LE_Interp rho (.ctor' ..).T (Eq.refl a)` holds while `LE_Interp rho (.ctor' ..).T h'` for an
opaque `h'` needs `.ctor' .. <= rho i` and fails.
(Not machine-checked: exhibiting it needs a `classify` that reports `.ctor`, i.e. a `Params`
instance, so it is a `Params`-relative construction rather than a shape computation.)

`strongSoundS` is the adequacy engine, so this kills the route to `sort_inv`.  It fails LOUD.

### Exit 2 -- give up the `.ctor` leaf in iota-patterns.  **No variant survives.**

Two forms, both closed:
  * (beta) `Pattern.WF` demands `rel = true` at ctor leaves, so a `Prop`-valued inductive's
    iota-rule is not a `Pattern` at all.  REFUTED (`eq_large_eliminates`): `Eq` is a `Prop`
    that LARGE-eliminates, so its rule cannot be dropped; and dropping it makes
    `ParamsExtra` unsatisfiable for every environment containing `Eq`.  Fails VACUOUS -- the
    worst mode, and the one this file was already caught by once (section 9).
  * keep the rule but give the leaf a different SHAPE.  That is exactly (alpha):
    `Classification.ctor`/`.etaCtor` gain the boolean and `WShape.ctor'` gains a `Prop`-ness
    disjunct.  Measured: **2 edits in SExpr.lean (clean) + 107 error instances at 60 lines in
    ShapeLogRel.lean**, before `ctor'`'s guard is touched -- and then `Matches.unique` looks
    FALSE under it, because `unique` recovers `c'`/`rargs'` FROM the leaf shape and a `.bot`
    leaf destroys them.  The relaxation of `Matches.app`'s index to `<=` is the same thing and
    fails the same way.

### Exit 3 -- give up `InterpTyped`'s totality.  **It degenerates to Exit 1.**

Blunt probe (drop the `m'.HasType a` conjunct outright): **32 errors, +21 over baseline**, in
`InterpTyped.bot/mk/out/hsort'`, `sound_app`, `sound_lam`, `sound_forallE`, `apps_realize`
and five places in `strongSoundS`.

The failures name what the field is FOR, and it answers the question directly.  The errors are
`True.bot_r'` and `True.ty_forallE_inv`: **`InterpTyped`'s classification is what lets the
model DESTRUCTURE a shape** -- `sound_app` uses it (through `TShape.HasType.ty_forallE_inv`)
to learn that a function's shape is a `.forallE` before applying it, and `sound_lam` /
`sound_forallE` use it to build their `HasDom` obligations.  So the interpretation does need a
classifying shape, but only for terms it destructures.

Now the targeted form -- exempt only `Prop`-valued types, e.g. weaken the conjunct to
`m'.HasType a \/ a.HasType .prop`.  Every non-`proofIrrel` consumer of the classification sits
at a `.forallE` or `.sort` type-shape (application, lambda, Pi-formation), and a term whose
type is a `Prop`-valued INDUCTIVE is never applied and never a binder's domain.  So the
exemption never fires at those sites, and the ONLY thing it costs is `proofIrrel`'s input.

    => TARGETED EXIT 3 IS EXIT 1.  There are not three exits; there are two.

### The decision, as narrowly as it can be put

    (I)  `proofIrrel` at `Prop`-valued inductives -- 1 case, and it goes FALSE and loud; or
    (II) 107 instances plus restating `Matches.unique`, which looks FALSE under the change.

## 11. PER-LEAF LEVEL LISTS.  THE SECOND `ParamsExtra` VACUITY, AND ITS FIX.

Section 9 peeled `extra_pat`'s λ-telescope.  **That was not enough**: `ParamsExtra` was still
unsatisfiable, so `strongSoundS` was still vacuous.

`Pattern.MatchesS` recorded a SINGLE `List SLevel` for a whole match -- its `app` rule kept the
function side's list and discarded the argument side's -- where the `VExpr`-side `Matches`
records one per leaf.  Its docstring called that deliberate and priced it at one consequence
(`applyS` ignoring an `RHS.fixed`'s `LPath`).  There was a second, and it was fatal:
`Check.defeqsS` also dropped the two `LPath`s of a `Check.level x i y j` clause and read BOTH
indices out of the one list.  On the `VExpr` side that clause relates the RECURSOR leaf's list
to the CONSTRUCTOR leaf's -- which is what makes `iotaLevelPairs`' `(i+1, i)` true, since
`selfLvls` is the block's parameters shifted by one when `isLE` prepends a fresh elimination
universe, so both sides evaluate to `ls.getD (i+1)`.  Read out of one list it degenerated to
`ls.getD (i+1) = ls.getD i`, and `extra_pat` demands that for ARBITRARY `ls`.  False for any
large eliminator with a universe parameter: `List`, `Prod`, `Sum`, `Sigma`.

FIXED.  `MatchesS`, `RHS.applyS` and `Check.defeqsS` now carry `p.LPath → List SLevel`;
`LE_Interp.RHS` gained the `LPath` index; `LE_Interp.Const` dropped its shared `ls` (17 call
sites, mechanical -- Lean drops an unused `variable`, so the arity changes whether you want it
to or not); `Const.pat` binds the map; `build_spine` reads the head leaf with
`Pattern.LPath.head`.

MEASURED, not estimated: `SExpr.lean` **4 edits, compiles clean**.  `ShapeLogRel.lean`
**+1 error over baseline** -- and the intermediate counts are worth knowing, because they are
almost all cascade: 318 at first (one root failure, `LE_Interp` not elaborating), 26 after the
`Const` call sites, 16 after the `pat` binder, 12 after `build_spine`.  Do not read an early
count on this refactor as a cost.

THE ONE OBLIGATION LEFT is in `LE_Interp.Const.compat_join`'s `pat`/`pat` case: `Const.pat`
binds `lsm` existentially (its type depends on `p`, which that rule binds), so `Const` has
nowhere to record the map, and the two `Const`s -- which describe the same term and so do
agree -- cannot be shown to.  Closing it means `LE_Interp.Const` and `LE_Interp.Matches`
indexed by `LPath`.  That, and only that, is the "shape-model-core work" the old docstring
named.

## 12. THE RE-INDEXING, SCOPED.  28 ROWS, AND THE EARLIER ~12-15 WAS AN UNDERCOUNT.

### Row zero: is the statement sufficient?  YES, and it is checked.

"The index carries the matched arguments independently of the leaf shape" is sufficient for
`Matches.unique`.  `ToyMatchesR` + `toy_unique_of_record` (both proved, in `section
ExitProbes`) put the matched datum in the INDEX and leave the shape as `leaf rec`, still free
to collapse; uniqueness then holds **for any `leaf`, injective or not** --
`toy_unique_of_record_bot` instantiates it at the collapsing leaf that `toy_unique_fails`
refutes.  So `unique` stops needing leaf injectivity, which was the obstruction.

### The record type it needs

`MArg n`, level-indexed like `Shape`:  `.shape (x : WShape n) : MArg n`  (a `var` position)
and `.ctor (c : Name) (l : List (MArg n)) : MArg (n+1)`  (an `app` position), with
`MArg.toShape : MArg n -> WShape n` derived.  The record must carry SHAPES, not just
term-level data: `Matches.var`'s index entry is the argument shape and `unique`'s induction
needs it, so a names-only record does not close the induction.

`Const`'s index must move to `List (MArg n)` as well.  Leaving it as shapes and having
`Const.pat` bind the record existentially re-introduces the collapse one level up, at
`Const.compat_join`'s `pat`/`pat` case -- the same gap as the per-leaf `lsm`, and for the same
reason.  That is what makes this one change rather than two, and it is also why the earlier
count was short: it counted `Matches`' consumers and missed that `Const` CONSUMES THE INDEX
and so needs an order, a join and a lift on it.

One refinement worth having before row 3: `Matches.matches_inter` relates matches of two
DIFFERENT patterns `p` and `q`, so `MArg.Compat` must handle the mixed
`.shape` / `.ctor` pair; `Matches.compat_join` relates two matches of the SAME `p`, so
`MArg.join` is only ever applied to pattern-aligned pairs and needs no mixed case.  **Compat
total, join partial.**

### The rows

Arithmetic: `M` mechanical (retype, proof unchanged), `P` positional (binder/index positions
move, structure unchanged), `S` structural (needs a new argument or definition).

    GROUP A -- the record type (new)
     1  S  `MArg` datatype and `MArg.toShape`
     2  M  `MArg.lift` + its `lift_lift`/`lift_self` lemmas
     3  S  `MArg.LE` and its order lemmas (refl, trans, `le_shape`, `le_ctor`)
     4  S  `MArg.Compat` -- TOTAL, incl. the mixed pair (needed by `matches_inter`)
     5  S  `MArg.join` on pattern-aligned pairs + `Join.mk` (join is the lub)
     6  S  `toShape` monotone, and commutes with `lift` and `join`
        Group A is a small lattice, but it is a lattice: compare `Shape`'s own
        LE/Compat/join API in this file, which runs ~200 lines.  `MArg`'s has no
        `forallE`/`lam`/`sort` cases, so ~80-120.

    GROUP B -- `Matches` re-indexed (11 rows)
     7  S  `LE_Interp.Matches` (inductive) -- index becomes `List (MArg n)`
     8  M  `Matches.varN_const_head`
     9  P  `Matches.arity`               (`.length` survives)
    10  P  `Matches.head_wf`
    11  P  `Matches.head_wf_eq`
    12  S  `Matches.mono_l`              (needs `MArg.LE`)
    13  S  `Matches.matches_inter`       (needs total `MArg.Compat`)
    14  S  `Matches.compat_join`         (needs `MArg.join`)
    15  M  `Matches.unique`              -- gets SHORTER: the `ctor'`-injectivity step goes
    16  M  `Matches.lift`                (needs `MArg.lift`)
    17  P  `Matches.of_matchesS`

    GROUP C -- `Const` re-indexed (7 rows)
    18  S  `LE_Interp.Const` (inductive) -- `ctor`/`indTy` read `.length` and `toShape`;
           `lam` injects a bare shape with `MArg.shape`
    19  P  `Const.mono`
    20  S  `Const.mono_l`                (needs `MArg.LE`)
    21  M  `Const.lift`                  (needs `MArg.lift`)
    22  P  `Const.closed`
    23  P  `Const.compat_mismatch`       (`.length` only)
    24  S  `Const.compat_join`           (needs `MArg.join`; this is where the per-leaf
           obligation of section 11 closes, since `Const` now records what it needs)

    GROUP D -- consumers (4 rows)
    25  P  `LE_Interp.const` (the rule) and the `LE_Interp` lemmas that case on it
    26  P  `LE_Interp.apps_realize` / `apps_realize_inv`
    27  S  `LE_Interp.build_spine`       -- builds the record from the `MatchesS`
    28  P  `strongSoundS`'s `pat` and `extra` cases

    28 rows: 9 structural, 8 positional, 6 mechanical, 5 in group A that are a small lattice.

### GROUP A IS BUILT.  Rows 1-6, green, ZERO new errors.

`MArg` and its lattice are in the file, just above `LE_Interp.Matches`: **16 declarations,
145 lines (~118 of code)** -- inside the 80-120 estimate.  Rows 1-5 (`MArg`, `shape`, `ctor`,
`toShape`, `lift`, `ble`/`LE`, `Compat`, `join`) compiled with no repairs at all; row 6 is the
four homomorphism lemmas `toShape_lift` / `toShape_mono` / `toShape_compat` / `toShape_join`,
which are what the consumer rows actually consume and nothing more.

Two things the build settled that the scope only guessed:

  * `toShape_lift` needs `n <= m`.  `WShape.lift` truncates downwards, so the equation is
    false without it.  Harmless -- `Matches.lift` and `Const.lift` are upward-only -- but it
    means row 16 and row 21 inherit the hypothesis.
  * `join`'s fallback should be `.shape (toShape x |>.join (toShape y))`, not `.shape .bot`.
    With `.bot` the join equation needs an alignment side-condition; with the fallback it
    holds under `Compat` alone, in every case.  That is why row 6 came out at four lemmas
    rather than four plus an `Aligned` predicate.

### What it buys, and what it does not

Buys: section 7's `.ctor`-leaf obstruction (the leaf may collapse to `.bot` for a
`Prop`-valued head without `unique` noticing) AND section 11's open obligation (row 24).
Still needed on top, for section 7: `Classification.ctor`/`.etaCtor` gain the boolean --
separately measured at 2 edits in `SExpr.lean` and **107 instances at 60 lines** here.

Does not touch: the join family (groups A of section 0a), whose obstruction is about Pi-shape
DOMAINS; or the lambda-peel (group C), which lives on `MatchesS`.  Both survive unchanged.

## 13. THE `bvar` TEST.  POSITIVE, AND PARTIAL -- READ BOTH HALVES.

### The positive half, proved: the refuting witness cannot be planted in a typed valuation

`jM_no_typed_bound` (next to `IsType.common_of_le`).  Every shape-level relativisation died to
the same trick: `Compat` guarantees an upper bound, so put it in `rho i` and let
`LE_Interp.bvar` read the bad pair straight off the valuation.  That trick **requires an
untyped valuation entry**:

    z above both is `.forallE z1 z2` whose domain z1 is above BOTH `cxA` and `cxA'`
    (`forallE_le`); `z.IsType` unfolds through `HasTypePi z2 z1 r` to `HasDom z2 z1`, which
    gives `z1.IsType` by `HasDom.isType`; and `IsType.common_of_le` then hands `cxA`/`cxA'`
    a common sort, which `cx_refutes` says they do not have.

So `j_refutes`'s and `le_interp_common_fails`'s witnesses have NO typed common upper bound, and
`Valuation.Fits` never produces one.  The earlier measurement -- "threading `Fits` does not
reach 5 of 8 sites" -- indeed no longer binds: 4 of those 5 are the shape-layer lemmas this
plan RETIRES rather than proves.

### The partial half, and it changes the shape of the work

The `bvar` case still does not close on that alone.  Proving
`(m1.join m2).HasType (a1.join a2)` there needs `(a1.join a2).IsType` first, to `mono_r` both
sides up to the joined type.  `common_sort` gives `a1` and `a2` a SHARED SORT -- but
`j_refutes`'s pair shares a sort too (`.sort true`), so a shared sort is not what excludes it;
the absence of a common CLASSIFIED UPPER BOUND is.  And `Valuation.Fits.cons`'s second field
supplies a classified upper bound for each shape realizing `A` SEPARATELY, not one for both.

The only route to a common one is `Fits`'s field applied to `a1.join a2` -- which needs
`LE_Interp rho (a1.join a2) A`, i.e. `compat_join`'s own conclusion.  **Inside the induction
that is available from the IH** (the `const` case already computes it as `ih1 hrho a5`);
outside it, it is circular.

    => `compat_join` must prove `Compat`, `LE_Interp (join)` and the typing fact in ONE
       simultaneous induction, with `Fits` threaded -- not as a lemma applied afterwards.

### ROW ZERO, RUN: `LE_Interp.subst` is CLEAN, and `Fits.join` is not needed

All EIGHT `.compat`/`.join'` uses inside `subst` apply at the **ambient** valuation `rho`
(`app` x2; `lam` cons x2; `forallE` nil x2, cons x2) -- never at the constructed
`rho1.join rho2`.  The construction is the OUTPUT of each step; the two shapes being joined are
already known to realize `sigma i` at `rho`.  So the coordinator's transport heuristic applies
in its strongest form: there is no fact to prove about a constructed valuation.

`Fits.join` DOES NOT NEED TO EXIST.

### And the strengthening does not touch `compat_join` at all

`subst` consumes only `LE_Interp.compat` and `LE_Interp.join'`, i.e. components .1 and .2 of the
EXISTING `compat_join`, which stay exactly as they are.  The typing fact goes in a SEPARATE
theorem carrying `Fits`.  So:

  - `LE_Interp.subst`   -- untouched, 8 sites untouched
  - `LE_Interp.inst`    -- untouched (only consumer of `subst`, at :5686 / :5689)
  - `compat_join`       -- untouched
  - `compat` / `join'`  -- untouched

### CORRECTION to the previous entry: the simultaneity argument was too strong

Last turn I wrote that the typing fact "is circular outside the induction", because getting
`LE_Interp rho (a1.join a2) A` needs `compat_join`'s own conclusion, available only from the IH.
**That is wrong, and the error is one step earlier than the one I caught.**
`LE_Interp.join'` is a STANDING THEOREM taking two `LE_Interp`s and no `Fits`:

    join' : LE_Interp rho m1 M -> LE_Interp rho m2 M -> LE_Interp rho (m1.join m2) M

so the realization half is available by direct application, with no induction hypothesis and no
circularity.  What remains for the typed lemma's `bvar` case is then:

    Fits.cons field 2 applied to (a1.join a2)  =>  a classified z >= a1.join a2 realizing A
    mono_r twice                               =>  m1 and m2 both typed at the SAME z

-- and joining at a common type is the step `j_refutes` refutes in general and
`jM_no_typed_bound` rules out HERE, since m1, m2 <= rho j and `Fits.cons` types `rho j`.

The induction may still be convenient, but it is NOT FORCED, and the ruling "build it
simultaneous, do not try to factor the typing fact out" rested on the refuted claim.  Flagging
rather than following it: the reason is gone, so the ruling should be re-taken, not inherited.

### THIRD COLLAPSE, AND THIS TIME THE CONCLUSION DIES TOO.  Machine-checked.

`#print axioms` (via `lake env lean` on the real file, fully qualified -- note the whole file
sits in `Lean4Lean.SExpr`, because `namespace SExpr` at :856 is NEVER CLOSED):

    Lean4Lean.SExpr.LE_Interp.join'       depends on: propext, sorryAx, Classical.choice, Quot.sound
    Lean4Lean.SExpr.LE_Interp.compat      depends on: propext, sorryAx, Classical.choice, Quot.sound
    Lean4Lean.SExpr.LE_Interp.compat_join depends on: propext, sorryAx, Classical.choice, Quot.sound
    Lean4Lean.SExpr.LE_Interp.subst       depends on: propext, sorryAx, Classical.choice, Quot.sound
    Lean4Lean.SExpr.jM_no_typed_bound     depends on: propext, Classical.choice, Quot.sound     -- CLEAN

**`join'` IS NOT STANDING.**  It is `compat_join .rfl H1 H2 |>.2`, and `compat_join` is ONE OF
THE 12 ERRORS -- at :5527, its `const` case:

    have aty := h4.isType.join ac a4.isType          -- `IsType.join`: DELETED, was false
    exact .join hc1 (aty.mono_r b3 h4) (aty.mono_r b4 a4)   -- `HasType.join`: refuted by `j_refutes`

So the two lemmas `compat_join` needs in its `const` case are exactly the two the join family
exists to retire.  `join'` is sorry-backed BECAUSE of the hole this work is meant to fill.

Consequences, in order:

  - The "separate `Fits`-carrying theorem" structure DOES NOT WORK.  Its `bvar` case was to get
    `LE_Interp rho (a1.join a2) A` from `join'` "with no induction hypothesis" -- but `join'` is
    the very thing under repair.  Circular after all.
  - **The circularity claim I withdrew last turn was CORRECT.  The withdrawal was the error.**
  - `LE_Interp.subst`'s own proof is clean (no error in :5578-5948); its `sorryAx` arrives
    ENTIRELY through `compat`/`join'`.  So the eight-sites-at-ambient-rho reading still holds as
    a syntactic fact, but it does not make `subst` untouched: if `compat_join` gains `Fits`,
    every one of the eight sites must supply it, and `subst`'s `lam`/`forallE` cases apply the IH
    at `rho.push x'.T`, needing `Fits.cons` -- whose FIELD 2 (every shape realizing `A` has a
    classified upper bound realizing `A`) is NOT available from `HasDom.iff`.

NOT CHECKED, and NOT PRICED: whether repairing `compat_join`'s `const` case actually requires a
typed hypothesis.  It is strongly suggested -- both lemmas it reaches for are refuted -- but that
is inference, and inference on this route has now failed three times.  No price until it is run.

### What that costs, over the 6-8 already reported

SUPERSEDED by the axiom check above: row zero did NOT come back clean.  The 6-8 figure rested
on `join'` being standing; it is sorry-backed and is itself part of the repair.  There is no
current price for the join family.

## 8. Working notes for editing this file

  * `set_option maxErrors` does not take -- see section 0.
  * A grouped `match` pattern produces ONE GOAL PER ALTERNATIVE.  `split` on `Shape.hasType`
    fans out to twelve, not eight; `split` tags them `h_1 ... h_12`.
  * Inside `first | ... | ...`, a `by` block nested in an `exact` is POSTPONED: every
    alternative must fail SYNCHRONOUSLY -- write `(refine ... ?_; tac)`, never
    `exact ... (by tac)`.
  * Inside `first`, a compound branch `(tac1; tac2)` FAILS when `tac1` closes the goal.
  * Lean reports errors BY LINE, not by declaration name.  Filter by line span.
  * `exacts [...]`, `set`, and `by_contra` are NOT available (no Mathlib).  Use
    `Decidable.byContradiction`, or `Bool.eq_iff_iff` + `of_decide_eq_true`/`decide_eq_true`
    for `decide _ = b` goals -- that is how `build_spine`'s `hdec` is proved.
  * `have <pattern> := e` elaborates through `match` and refuses a motive with metavariables;
    `obtain` does not.  Destructure with `obtain` and EXPLICIT names.
  * `WShape.casesOn'`'s `lam`/`ctor` cases used to be closed by `trivial`, because `trivial`
    tries `contradiction` and `HasType (.lam ..) .type` reduced to `false = true`.  Under
    `IsType` it does not reduce; use
    `absurd (WShape.HasType.isType h) WShape.IsType.not_lam` (resp. `.not_ctor`).
  * `LE_Interp.Const.indTy`'s `cases`-pattern binder order is `{rel} {m} {rargs}` -- the
    `@indTy` pattern is `| @indTy _ _ rargs hct m_le`.  Get it from `#check @...`; auto-bound
    implicit order is not source order.
  * **NEVER write `def SExpr.foo` inside `namespace SExpr`.**  It declares
    `Lean4Lean.SExpr.SExpr.foo` and thereby CREATES the namespace `Lean4Lean.SExpr.SExpr`;
    every later `SExpr.Bar` written inside `namespace Lean4Lean.SExpr`, in this file or in any
    consumer, then resolves there first and fails.  `SExpr.mkLams` did this and broke
    `Experimental/LogRel.lean` with `Unknown constant Lean4Lean.SExpr.SExpr.Subst` -- a file
    this stream does not touch.  It is the namespace trap doubled, and it surfaces at a
    CONSUMER, far from the cause.
  * **Build the whole `Lean4Lean.Experimental` cone, not just your own two files.**
    `lake build Lean4Lean.Experimental.ShapeLogRelAdequacy` succeeds while `LogRel.lean` is
    broken, because `LogRel` is not on that path.  Build every module under
    `Lean4Lean/Experimental/` and read the FIRST failure, which may be in a file you never
    edited.
  * **A deferral must never be stated as "the cost is X".**  State it as "the cost includes
    X; not audited for others."  `MatchesS`'s single level list was deferred with one
    consequence named (`applyS` ignoring an `LPath`) and a second unnamed one that made
    `ParamsExtra` unsatisfiable and `strongSoundS` vacuous.  A stale docstring can be caught
    by checking it against the code; a complete-LOOKING partial deferral gives the reader no
    signal that anything is missing, so it survives every check.  Sibling of the stale-doc
    rule above, and worse.
  * **A scripted block replacement silently ate `private def piX`/`piA` this session and the
    file still elaborated**, because Lean auto-bound the now-undefined names as implicit
    variables and the errors surfaced three components later as bogus type mismatches.  After
    any scripted edit that replaces a *range*, grep that the definitions it spanned are still
    there.

Full background, all witnesses and all prose: docs/design-shape-lattice.md.
Remove this banner when the migration lands.
================================================================================

## 14. AXIOM SWEEP, 2026-08-23.  `#print axioms` over all 653 declarations, one `lake env lean`
pass.  THIS SUPERSEDES EVERY SOURCE-READ CLAIM ABOUT WHAT IS PROVED IN THIS FILE.

653 resolved | 49 sorryAx-backed | 604 clean.

sorryAx-backed (49) -- these READ AS PROOFS IN SOURCE and are not:

  join family, shape layer (8):
    WShape.HasType.join      WShape.HasType.join'     WShape.HasDom.join    WShape.HasDom.join'
    TShape.HasType.join      TShape.HasType.join'     WShape.HasTypePi.join WShape.HasTypeLam.join
  join family, LE_Interp/LRS (6):
    LE_Interp.compat_join    LE_Interp.compat         LE_Interp.join        LE_Interp.join'
    LE_Interp.Const.compat_join                       LRS.PiDefEq.join
  downstream (19):
    LE_Interp.subst          LE_Interp.inst           LE_Interp.apps_realize
    LE_Interp.apps_realize_inv                        LE_Interp.RHS.of_applyS
    LE_Interp.sound_forallE  LE_Interp.sound_lam      LE_Interp.sound_app
    LE_Interp.build_spine    LE_Interp.strongSound    LE_Interp.strongSoundS
    LE_Interp.soundS         LE_Interp.sound          LE_Interp.forallE_inv
    LE_Interp.forallE_inv'   LE_Interp.lam_inv        LE_Interp.lam_inv'
    SoundEq.forallE_inv      SoundEq.inst
  LR/LRS infrastructure (12):
    LR   LRS   LR.Subst1   LR.SubstWF   LR.SubstWF.fits   LR.SubstWF.left   LR.SubstWF.symm
    LR.SubstWF.toSubstEq    LR.DefEq.lift   LR.TyDefEq.lift   LR.lift_succ_aux
    LRS.LamDefEq.lift_aux   LRS.PiDefEq.lift_aux
  other (3):
    StrongSound.uniq         cxValTyPi2               join_sort_fails

CLEAN, and therefore usable (the refutation witnesses and the survivors):
    cx_refutes  j_refutes  jM_no_typed_bound  lam_join_fails  hasDom_escape_fails
    proofIrrel_gated  proofIrrel_witness_wf  eq_large_eliminates  ctor_not_prop_typed
    le_interp_common_fails  piDefEq_cannot_see  exit1_bvar_separates  exit1_witness
    ctor'_inj_of_not_struct  toy_unique_of_inj  toy_unique_fails  toy_unique_of_record
    toy_unique_of_record_bot  Shape.HasType.indTy_false_bot  WShape.IsType.common_of_le
    Shape.IsType.common_of_not_forallE  LE_Interp.common_sort  LE_Interp.soundSS
    WShape.Join.compat  WShape.Join.iff  WShapeFun.Join.compat  WShapeFun.Join.iff

TWO WITNESSES ARE SORRY-BACKED AND MUST NOT BE CITED: `join_sort_fails`, `cxValTyPi2`.


## 15. ROW-ZERO CHECK ON THE BASE OF THE TOWER, 2026-08-23.

Q: can `WShape.HasType.join` be proved with a typedness hypothesis, at the shape layer
alone, independent of `LE_Interp`?

### The 12 errors sit in 8 declarations (measured, current file):

  4257, 4265  WShape.HasType.join        <- THE BASE, and it breaks INSIDE `go_dom`
  4323        WShape.HasDom.join
  5474        LE_Interp.Const.compat_join
  5614        LE_Interp.compat_join
  6036, 6109  LE_Interp.sound_lam
  6643        LE_Interp.build_spine
  6882, 6902  LE_Interp.strongSoundS
  7236, 7238  LRS.PiDefEq.join

### The base breaks at ONE line, and it is the deleted false lemma:

  go_dom:  have ajt := ih ha a2.isType b2.isType        -- line 4265

`ih` wants `a.HasType ?r` and `a'.HasType ?r` -- a COMMON SORT for the two domains.  `.isType`
gives only `∃ r, _.HasType (.sort r)` separately.  This line is where the deleted-as-false
`WShape.IsType.common` used to sit.  Everything else in `go_dom` follows from `ajt`.

### PROVED, and it supplies exactly that (axiom-clean: propext, Classical.choice, Quot.sound):

  WShape.forallE_common_of_typed_bound
    (h1 : (forallE a1 f1).HasType (sort r0)) (h2 : (forallE a2 f2).HasType (sort r0))
    (hz1 : forallE a1 f1 <= z) (hz2 : forallE a2 f2 <= z) (hz : z.IsType) :
    ∃ r, a1.HasType (sort r) ∧ a2.HasType (sort r)

This is `jM_no_typed_bound` GENERALIZED off its witness -- so a typed common upper bound kills
the whole `j_refutes` counterexample FAMILY, not just the one shape, at the shape layer, with
no `LE_Interp` anywhere.  Compiles into the file with zero new errors.

### THE ONE SPOT NOT RESOLVED -- and it is exactly the entangled-or-not question:

`go_dom`'s INNER recursive call
    ih hcx (.mono_r hJa.le.1 ajt a2) (.mono_r hJa.le.2 ajt b2)
is at subjects `x₁, x₂` drawn from `HasDom.iff`'s **universally quantified, untyped `x`**
(`x₁ ≤ x`, `x₂ ≤ x`).  A typed `ih` needs a TYPED common upper bound of `x₁, x₂`, and `x`
carries no typedness.  Sources checked and REJECTED:
  - "both typed at a common type" is NOT sufficient -- `j_refutes` is exactly that shape.
  - `hasDom_escape_fails` does NOT refute this call: its witness (`x₁ = x₂ = .bot`,
    `a = cxA`, `a' = cxA'`) dies one step EARLIER, at `ajt`, because `cxA.join cxA'` is not a
    type.  With `ajt` in hand that witness is out of scope.  So it is neither a refutation
    nor a proof -- the spot is genuinely OPEN.
  - Restricting `HasDom`'s `∀ x` to typed `x` would be WEAKENING A DEFINITION TO MAKE A PROOF
    GO THROUGH.  Not done, not proposed.

### RESOLVED, NEGATIVELY, by `go_dom_inner_fails` (axiom-clean).  See its docstring.

The inner call fails WITH `ajt` in hand, on `j_refutes`'s own witness.  The tower IS entangled
at that spot: a top-level typed-bound hypothesis does not descend through `HasDom.iff`'s
arbitrary `∀ x`.  The base does NOT stand alone.

Repairing it requires `HasDom` to carry typedness -- a DEFINITION change, in the abstract spec,
needing sign-off.  Not attempted.

Note on how this was settled: the enumerator (`Lean4Lean/Experimental/ShapeEnum.lean`) was
built for this question and then NOT NEEDED for it -- an existing hand-built witness already
covered the case once the obligation was stated sharply enough.  Stating the obligation
precisely was the expensive step, not searching for a witness.

-/

import Lean4Lean.Experimental.SExpr

/-
`Shape.plift` and friends below are written in `Option`-monad `do`/`return` notation, and
the proofs about them `simp` through the exact term that notation elaborates to.
leanprover/lean4#13305 made the new `do` elaborator the default in v4.32.0, which reshapes
those terms. Pin the legacy elaborator here until the proofs are migrated
(digama0/lean4lean#31).
-/
set_option backward.do.legacy true

/-
**Working notes for editing this file.** Three things here cost hours before being noticed;
each is invisible until it bites.

1. `set_option maxErrors` **does not take** in this file -- the build caps error reporting at
   100 and silently truncates, so a raw error count read off `lake build` is a *floor*, not a
   measurement. To count properly:
   `lake env lean -DmaxErrors=600 Lean4Lean/Experimental/ShapeLogRel.lean`
   and check that no "maximum number of errors" line appears in the output.

2. A grouped `match` pattern such as `| 0, .bot, _ | _+1, .bot, .bot | _+1, .bot, .sort _`
   produces **one goal per alternative**, not one goal for the group. `split` on
   `Shape.hasType` therefore fans out to twelve goals, not eight. Do not count them by hand:
   `split` tags them `h_1 … h_12` and the tags appear in the error output, so address them by
   `case h_k => ...` and read the mapping off the errors.

3. Inside a `first | ... | ...` chain, a `by` block nested in an `exact` is **postponed**:
   `first` sees the `exact` succeed, commits to that branch, and the inner tactic fails
   afterwards with no backtracking. Every alternative must fail *synchronously* -- write
   `(refine ... ?_; tac)`, never `exact ... (by tac)`.

4. Also inside `first`, a compound branch `(tac1; tac2)` **fails when `tac1` closes the goal**
   -- `tac2` then errors with "no goals" and `first` moves on, silently skipping the branch
   that actually worked. A `simp_all` that closes the goal in some cases and not others needs
   its own bare alternative, placed *before* any compound branch that starts with it.

5. Lean reports errors **by line, not by declaration name**. Grepping the error stream for a
   theorem's name therefore reports "clean" when it is not -- a false-positive generator.
   Filter by the declaration's actual line span instead.

Also: `exacts [...]` is not available here (no Mathlib); use `match` or `<;>` instead.
-/

/-
**What the `ShapeS.indTy` parameterisation exposed.** It did not introduce a problem; it
revealed one that `.type` was masking. `Compat` on `.forallE` shapes does not constrain the
codomains' universe *at all* when the domains disagree -- `ShapeFun.Compat`'s value
obligation is guarded by the keys, so two Pi-shapes can be compatible while one is
`Prop`-valued and the other `Type`-valued. That was invisible while `.type` forced every
classifying shape to `true`, because there was nothing left to disagree about. See
`CounterexampleProbe` below for a machine-checked witness.
-/

namespace Lean4Lean
open Lean4Lean

namespace SExpr
variable [Params]

private noncomputable instance : DecidableEq SLevel := fun a b => Classical.propDecidable (a = b)

@[simp] theorem SLevel.succ_ne_zero {l : SLevel} : l.succ ≠ .zero := by
  intro h
  have := congrArg Subtype.val h
  simp [SLevel.succ, SLevel.zero] at this
  have := congrFun this []
  simp [VLevel.eval] at this

@[simp] theorem SLevel.imax_eq_zero {l l' : SLevel} : l.imax l' = .zero ↔ l' = .zero := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    simp [SLevel.imax, SLevel.zero] at hv
    apply Subtype.ext; funext v
    have := congrFun hv v
    simp [Lean.Nat.imax, VLevel.eval] at this
    exact Decidable.byContradiction fun h => absurd (this h).2 h
  · intro h
    subst h
    apply Subtype.ext; funext v
    simp [SLevel.imax, SLevel.zero, Lean.Nat.imax, VLevel.eval]

inductive Shape0 : Type where
  | bot : Shape0
  | sort (rel : Bool) : Shape0

inductive ShapeS (Shape : Type) : Type where
  | bot : ShapeS Shape
  | sort (rel : Bool) : ShapeS Shape
  | forallE : Shape → List (Shape × Shape) → ShapeS Shape
  | lam : List (Shape × Shape) → ShapeS Shape
  | ctor : Name → List Shape → ShapeS Shape
  | indTy (rel : Bool) : ShapeS Shape

@[implicit_reducible] def Shape : Nat → Type
  | 0 => Shape0
  | n + 1 => ShapeS (Shape n)

abbrev ShapeFun (n) := List (Shape n × Shape n)

@[match_pattern] def Shape.bot : ∀ {n}, Shape n
  | 0 => Shape0.bot
  | _+1 => ShapeS.bot

@[match_pattern] def Shape.sort (rel : Bool) : ∀ {n}, Shape n
  | 0 => Shape0.sort rel
  | _+1 => ShapeS.sort rel

abbrev Shape.prop : ∀ {n}, Shape n := .sort false
abbrev Shape.type : ∀ {n}, Shape n := .sort true

def ShapeFun.bot : ShapeFun n := [(.bot, .bot)]

def ShapeFun.Compat (R : α → β → Bool) (f : List (α × α)) (f' : List (β × β)) : Bool :=
  f.all fun (x, y) => f'.all fun (x', y') => R x x' → R y y'

omit [Params] in
theorem ShapeFun.Compat.def : Compat R f f' ↔ ∀ x ∈ f, ∀ y ∈ f', R x.1 y.1 → R x.2 y.2 := by
  simp [ShapeFun.Compat, -decide_implies]

def Shape.Compat : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | 0, _, .bot | _+1, .bot, _ | _+1, _, .bot => true
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => r = r'
  | _+1, .forallE s f, .forallE s' f' => s.Compat s' && ShapeFun.Compat Compat f f'
  | _+1, .lam f, .lam f' => ShapeFun.Compat Compat f f'
  | _+1, .ctor c l, .ctor c' l' => c = c' && List.Forall₂ (Compat · ·) l l'
  | _+1, .indTy r, .indTy r' => r = r'
  | _, _, _ => false

omit [Params] in
theorem Shape.Compat.comm {n} {s t : Shape n} : s.Compat t = t.Compat s := by
  induction n with | zero => cases s <;> cases t <;> simp [Compat, eq_comm] | succ n ih
  let rec go {f f' : ShapeFun n} : ShapeFun.Compat Compat f f' = ShapeFun.Compat Compat f' f := by
    rw [Bool.eq_iff_iff]; simp [ShapeFun.Compat.def]
    constructor <;> intro H _ _ h1 _ _ h2 h3 <;> exact ih ▸ H _ _ h2 _ _ h1 (ih ▸ h3)
  cases s <;> cases t <;> simp +singlePass [Compat, eq_comm, ih, go]
  · rw [Bool.eq_iff_iff]; simp; intro
    constructor <;> refine fun h => h.flip.imp fun _ _ h => ih ▸ h

omit [Params] in
theorem ShapeFun.Compat.comm {n} {f f' : ShapeFun n} :
    Compat Shape.Compat f f' = Compat Shape.Compat f' f := Shape.Compat.comm.go _ Shape.Compat.comm

omit [Params] in
theorem Shape.Compat.symm {n} {s t : Shape n} : s.Compat t → t.Compat s := (comm ▸ ·)

omit [Params] in
theorem ShapeFun.Compat.symm {n} {f f' : ShapeFun n} :
    Compat Shape.Compat f f' → Compat Shape.Compat f' f := (comm ▸ ·)

omit [Params] in theorem Shape.Compat.bot_l {n} {s : Shape n} : bot.Compat s := by cases n <;> rfl
omit [Params] in theorem Shape.Compat.bot_r {n} {s : Shape n} : s.Compat bot := symm bot_l

omit [Params] in theorem Shape.Compat.sort_sort : Compat (sort r : Shape n) (sort r') ↔ r = r' := by
  cases n <;> simp [Compat]
omit [Params] in theorem Shape.Compat.forallE_forallE {a a' : Shape n} {f f' : ShapeFun n} :
    Compat (n := n+1) (.forallE a f) (.forallE a' f') ↔
    a.Compat a' ∧ ShapeFun.Compat Compat f f' := by simp only [Compat, Bool.and_eq_true]
omit [Params] in theorem Shape.Compat.lam_lam {f f' : ShapeFun n} :
    Compat (n := n+1) (.lam f) (.lam f') ↔ ShapeFun.Compat Compat f f' := by simp only [Compat]
omit [Params] in theorem Shape.Compat.ctor_ctor {l l' : List (Shape n)} :
    Compat (n := n+1) (.ctor c l) (.ctor c' l') ↔ c = c' ∧ l.Forall₂ (Compat · ·) l' := by
  simp [Compat]

def ShapeFun.ble (R : α → α → Bool) (f f' : List (α × α)) : Bool :=
  f.all fun (x, y) => f'.any fun (x', y') => R x' x && R y y'

def Shape.ble : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | _+1, .bot, _ => true
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => r = r'
  | _+1, .forallE s f, .forallE s' f' => s.ble s' && ShapeFun.ble ble f f'
  | _+1, .lam f, .lam f' => ShapeFun.ble ble f f'
  | _+1, .ctor c l, .ctor c' l' => c == c' && l.Forall₂ (Shape.ble · ·) l'
  | _+1, .indTy r, .indTy r' => r = r'
  | _, _, _ => false

def ShapeFun.LE (s s' : ShapeFun n) : Prop := ShapeFun.ble Shape.ble s s'
def Shape.LE (s s' : Shape n) : Prop := s.ble s'
instance : LE (Shape n) := ⟨Shape.LE⟩
instance : DecidableRel (α := Shape n) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (x.ble y))
instance : DecidableRel (ShapeFun.LE (n := n)) :=
  fun x y => inferInstanceAs (Decidable (ShapeFun.ble _ x y))

omit [Params] in
@[simp] theorem Shape.bot_le : Shape.bot ≤ (s : Shape n) := by cases n <;> rfl

omit [Params] in
theorem ShapeFun.LE.def' {f f' : ShapeFun n} : ShapeFun.LE f f' ↔
    ∀ x ∈ f, ∃ x' ∈ f', x'.1 ≤ x.1 ∧ x.2 ≤ x'.2 := by
  simp [LE, ble]; rfl

omit [Params] in
theorem ShapeFun.LE.def {f f' : ShapeFun n} : ShapeFun.LE f f' ↔
    ∀ x y : Shape n, (x, y) ∈ f → ∃ x' y' : Shape n, (x', y') ∈ f' ∧ x' ≤ x ∧ y ≤ y' := by
  simp [LE, ble]; rfl

omit [Params] in
theorem Shape.LE.def {s s' : Shape (n + 1)} : s ≤ s' ↔
    match s, s' with
    | .bot, _ => True
    | .sort r, .sort r' => r = r' --j ≤ i
    | .forallE s f, .forallE s' f' => s ≤ s' ∧ ShapeFun.LE f f'
    | .lam f, .lam f' => ShapeFun.LE f f'
    | .ctor c f, .ctor c' f' => c = c' ∧ f.Forall₂ Shape.LE f'
    | .indTy r, .indTy r' => r = r'
    | _, _ => False := by
  dsimp only [(· ≤ ·), LE, ShapeFun.LE]
  rw [Shape.ble.eq_def]; cases s <;> cases s' <;> simp
  · intro; rfl

omit [Params] in
theorem Shape.LE.rfl {s : Shape n} : s ≤ s := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> simp [ble]
  | succ n ih =>
    have ihf {s : List (Shape n × Shape n)} : ShapeFun.ble ble s s := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      exact fun _ h => ⟨_, h, ih, ih⟩
    cases s <;> simp [ble, ih, ihf]
    · exact .rfl fun _ _ => ih

omit [Params] in
theorem Shape.LE.of_eq {s : Shape n} : s = t → s ≤ t := by rintro ⟨⟩; exact .rfl

omit [Params] in
theorem ShapeFun.LE.rfl {s : ShapeFun n} : s.LE s := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  exact fun _ h => ⟨_, h, Shape.LE.rfl, Shape.LE.rfl⟩

omit [Params] in
theorem Shape.le_bot {s : Shape n} : s ≤ .bot ↔ s = .bot :=
  ⟨(by cases n <;> cases s <;> first | rfl | cases ·), (· ▸ LE.rfl)⟩

omit [Params] in
theorem Shape.le_sort {s : Shape n} : s ≤ .sort r ↔ s = .bot ∨ s = .sort r := by
  cases n <;> simp [sort, bot, (· ≤ ·), Shape.LE] <;> cases s <;>
    simp [ble] <;> exact ⟨fun h => h ▸ rfl, fun h => by injection h⟩

omit [Params] in
theorem Shape.sort_le {s : Shape n} : .sort r ≤ s ↔ .sort r = s := by
  cases n <;> simp [sort, (· ≤ ·), Shape.LE] <;> cases s <;> simp [ble, Shape]

omit [Params] in
theorem Shape.le_indTy {s : Shape (n+1)} : s ≤ .indTy r ↔ s = .bot ∨ s = .indTy r := by
  simp [Shape.bot, (· ≤ ·), Shape.LE]; cases s <;> simp [Shape.ble, eq_comm]
  exact ⟨fun h => h ▸ rfl, fun h => by injection h⟩

omit [Params] in
theorem Shape.indTy_le {s : Shape (n+1)} : .indTy r ≤ s ↔ s = .indTy r := by
  simp [Shape.LE.def]; cases s <;> simp [eq_comm]
  exact ⟨fun h => h ▸ rfl, fun h => by injection h⟩

omit [Params] in
theorem Shape.forallE_le {s : Shape (n+1)} :
    .forallE a b ≤ s ↔ ∃ a' b', a ≤ a' ∧ ShapeFun.LE b b' ∧ .forallE a' b' = s := by
  rw [Shape.LE.def]; cases s <;> simp [Shape]

omit [Params] in
@[simp] theorem Shape.forallE_le_forallE :
    (by exact .forallE a b : Shape (n+1)) ≤ .forallE a' b' ↔ a ≤ a' ∧ ShapeFun.LE b b' := by
  refine Shape.forallE_le.trans ⟨?_, fun ⟨h1, h2⟩ => ⟨_, _, h1, h2, rfl⟩⟩
  rintro ⟨_, _, h1, h2, ⟨⟩⟩; exact ⟨h1, h2⟩

omit [Params] in
theorem Shape.lam_le {s : Shape (n+1)} :
    .lam f ≤ s ↔ ∃ f', ShapeFun.LE f f' ∧ .lam f' = s := by
  rw [Shape.LE.def]; cases s <;> simp [Shape]

omit [Params] in
@[simp] theorem Shape.lam_le_lam :
    (by exact .lam f : Shape (n+1)) ≤ .lam f' ↔ ShapeFun.LE f f' :=
  Shape.lam_le.trans ⟨by rintro ⟨_, h, ⟨⟩⟩; exact h, fun h => ⟨_, h, rfl⟩⟩

omit [Params] in
theorem Shape.LE.trans {s t u : Shape n} : s ≤ t → t ≤ u → s ≤ u := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;>
      (intro h1 h2; exact h1.trans h2)
  | succ n ih =>
    have ihf {s t u : List (Shape n × Shape n)} :
        ShapeFun.ble ble s t → ShapeFun.ble ble t u → ShapeFun.ble ble s u := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
      exact ⟨_, hz, ih y1 x1, ih x2 y2⟩
    cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;> grind [List.Forall₂.trans]

omit [Params] in
theorem ShapeFun.LE.trans {s t u : ShapeFun n} : s.LE t → t.LE u → s.LE u := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
  exact ⟨_, hz, Shape.LE.trans y1 x1, Shape.LE.trans x2 y2⟩

omit [Params] in
theorem Shape.Compat.mono_r {n} {s t t' : Shape n}
    (le : t ≤ t') (H : s.Compat t') : s.Compat t := by
  induction n with
  | zero =>
    cases s <;> [simp [Compat]; skip]
    cases t <;> cases t' <;> simp [Compat, (·≤·), Shape.LE, Shape.ble] at H le ⊢
    exact H.trans le.symm
  | succ n ih
  let rec go {s t t' : ShapeFun n}
      (le : t.LE t') (H : ShapeFun.Compat Compat s t') : ShapeFun.Compat Compat s t := by
    simp [ShapeFun.Compat.def, ShapeFun.LE.def] at H le ⊢
    intro _ _ h1 _ _ h2 h3; have ⟨_, _, a1, a2, a3⟩ := le _ _ h2
    exact ih a3 <| H _ _ h1 _ _ a1 <| ih a2 h3
  (cases s with | bot => rfl | _) <;>
    (cases t' with | bot => cases le_bot.1 le; rfl | _) <;>
    simp [Compat] at H <;> (cases t with | bot => rfl | _) <;>
    simp [Shape.LE.def, Compat] at le ⊢
  · exact H.trans le.symm
  · exact ⟨ih le.1 H.1, go le.2 H.2⟩
  · exact go le H
  · exact ⟨H.1.trans le.1.symm, H.2.trans (fun _ _ _ h1 h2 => by exact ih h2 h1) le.2.flip⟩
  · exact H.trans le.symm

omit [Params] in
theorem ShapeFun.Compat.mono_r {n} {s t t' : ShapeFun n} :
    t.LE t' → Compat Shape.Compat s t' → Compat Shape.Compat s t :=
  Shape.Compat.mono_r.go _ Shape.Compat.mono_r

omit [Params] in
theorem Shape.Compat.mono {n} {s s' t t' : Shape n}
    (le₁ : s ≤ s') (le₂ : t ≤ t') (H : s'.Compat t') : s.Compat t :=
  mono_r le₂ <| symm <| mono_r le₁ <| symm H

def ShapeFun.lift (lift : α → β) (x : List (α × α)) : List (β × β) :=
  x.map fun (a, b) => (lift a, lift b)

def Shape.lift : ∀ {n} m, Shape n → Shape m
  | 0, _, .sort r | _+1, _, .sort r => .sort r
  | 0, _, .bot | _+1, _, .bot | _, 0, _ => .bot
  | _+1, _+1, .forallE s f => .forallE (lift _ s) <| ShapeFun.lift (lift _) f
  | _+1, _+1, .lam f => .lam <| ShapeFun.lift (lift _) f
  | _+1, _+1, .ctor c l => .ctor c <| l.map (lift _)
  | _+1, _+1, .indTy r => .indTy r

omit [Params] in
@[simp] theorem Shape.lift_bot : (.bot : Shape n).lift m = .bot := by
  cases n <;> [rfl; cases m <;> rfl]

omit [Params] in
@[simp] theorem ShapeFun.lift_bot :
    ShapeFun.lift (Shape.lift m) (.bot : ShapeFun n) = ShapeFun.bot := by simp [ShapeFun.lift, bot]

omit [Params] in
@[simp] theorem Shape.lift_sort : (.sort r : Shape n).lift m = .sort r := by
  cases n <;> [rfl; cases m <;> rfl]

omit [Params] in theorem Shape.lift_prop : (.prop : Shape n).lift m = .prop := lift_sort
omit [Params] in theorem Shape.lift_type : (.type : Shape n).lift m = .type := lift_sort

omit [Params] in
theorem Shape.lift_self {s : Shape n} : s.lift n = s := by
  have {α} {lift : α → α} (IH : ∀ {s}, lift s = s) {s} : ShapeFun.lift lift s = s := by
    simp [ShapeFun.lift]; apply List.map_id''; simp [IH]
  unfold lift <;> split <;> (try rfl)
  · cases s <;> [rfl; grind]
  · rw [Shape.lift_self, this Shape.lift_self]
  · rw [this Shape.lift_self]
  · rw [List.map_id'' fun _ => Shape.lift_self]

omit [Params] in
theorem ShapeFun.lift_self {s : ShapeFun n} : lift (Shape.lift n) s = s := by
  simp [ShapeFun.lift]; apply List.map_id''; simp [Shape.lift_self]

omit [Params] in
theorem Shape.lift_lift {s : Shape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift _ := by
  induction n₁ generalizing n₂ n₃ with
  | zero => cases s <;> simp [lift]
  | succ n₁ ih =>
    cases n₃ with
    | zero =>
      cases n₂ with | zero => rw [lift_self] | succ n₃
      cases s <;> simp [lift]
    | succ n₃ =>
      let n₂ + 1 := n₂; simp at le; replace ih {s} := ih (s := s) le
      have ihf {s : ShapeFun n₁} :
          ShapeFun.lift (lift n₃) (ShapeFun.lift (lift n₂) s) = ShapeFun.lift (lift _) s := by
        simp [ShapeFun.lift, ih]
      cases s <;> simp [lift, ih, ihf]
      · congr 2; ext; exact ih

omit [Params] in
theorem ShapeFun.lift_lift {s : ShapeFun n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    lift (Shape.lift n₃) (lift (Shape.lift n₂) s) = lift (Shape.lift _) s := by
  simp [ShapeFun.lift, Shape.lift_lift le]

omit [Params] in
theorem Shape.lift_le_lift {s t : Shape n} (le : n ≤ m) : s.lift m ≤ t.lift m ↔ s ≤ t := by
  dsimp [(· ≤ ·), Shape.LE]; rw [← Bool.eq_iff_iff]
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases s <;> cases t <;> simp [lift, ble]
  | succ n ih =>
    let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {t' s} := @ih m t' s le
    let rec go {s t : ShapeFun n} :
        ShapeFun.ble ble (ShapeFun.lift (lift m) s) (ShapeFun.lift (lift m) t) =
        ShapeFun.ble ble s t := by
      simp only [ShapeFun.ble, ShapeFun.lift, List.all_map, List.any_map, Function.comp_def, ih]
    cases s <;> cases t <;> simp [ble, lift, go, *]

omit [Params] in
theorem ShapeFun.lift_le_lift {s t : ShapeFun n} (le : n ≤ m) :
    ShapeFun.LE (lift (Shape.lift m) s) (lift (Shape.lift m) t) ↔ ShapeFun.LE s t := by
  dsimp [ShapeFun.LE]; rw [← Bool.eq_iff_iff,
    Shape.lift_le_lift.go _ _ (Bool.eq_iff_iff.2 (Shape.lift_le_lift le))]

omit [Params] in
theorem Shape.lift_le_bot {s : Shape n} (h : n ≤ m) : s.lift m ≤ .bot ↔ s = .bot := by
  rw [← le_bot, ← lift_bot, Shape.lift_le_lift h]

omit [Params] in
theorem Shape.lift_eq_bot {s : Shape n} (h : n ≤ m) : s.lift m = .bot ↔ s = .bot := by
  rw [← le_bot, Shape.lift_le_bot h]

omit [Params] in
theorem Shape.lift_mono {s t : Shape n} : s ≤ t → s.lift m ≤ t.lift m := by
  dsimp [(· ≤ ·), Shape.LE]
  cases n with
  | zero =>
    cases s <;> cases t <;> simp [lift, ble] <;>
      first | exact Shape.bot_le | (intro h; subst h; exact Shape.LE.rfl)
  | succ n =>
    cases m with
    | zero => cases s <;> cases t <;> simp [lift, ble]
    | succ m =>
      let rec go {n m} (ih : ∀ {s t : Shape n}, s ≤ t → s.lift m ≤ t.lift m)
          {s t} : ShapeFun.ble ble s t → ShapeFun.ble ble
            (ShapeFun.lift (lift m) s) (ShapeFun.lift (lift m) t) := by
        simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
          ShapeFun.lift, List.any_map, List.all_map, Function.comp_apply]
        exact fun H _ h1 => let ⟨_, h2, h3, h4⟩ := H _ h1; ⟨_, h2, ih h3, ih h4⟩
      have := @Shape.lift_mono n m; dsimp [(· ≤ ·), Shape.LE] at this
      have := @go n m Shape.lift_mono
      cases s <;> cases t <;> simp [ble, lift, *] <;> grind [List.Forall₂.imp]

omit [Params] in
theorem ShapeFun.lift_mono {s t : ShapeFun n} : s.LE t →
    LE (lift (Shape.lift m) s) (lift (Shape.lift _) t) := Shape.lift_mono.go Shape.lift_mono

omit [Params] in
protected theorem Shape.Compat.lift {x y : Shape n} (le : n ≤ m) :
    (x.lift m).Compat (y.lift m) = x.Compat y := by
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases x <;> cases y <;> simp [lift, Compat]
  | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x y} := @ih m x y le
  let rec go {x y : ShapeFun n} :
      ShapeFun.Compat Compat (ShapeFun.lift (lift m) x) (ShapeFun.lift (lift m) y) =
      ShapeFun.Compat Compat x y := by
    rw [Bool.eq_iff_iff]; simp only [ShapeFun.lift, ShapeFun.Compat.def, List.forall_mem_map, ih]
  cases x <;> cases y <;> simp [Compat, lift, go, *]

omit [Params] in
theorem ShapeFun.Compat.lift {x y : ShapeFun n} (le : n ≤ m) :
    Compat Shape.Compat (lift (Shape.lift m) x) (lift (Shape.lift m) y) =
    Compat Shape.Compat x y := Shape.Compat.lift.go _ _ (Shape.Compat.lift le)

def ShapeFun.plift (lift : α → β × Option β) (x : List (α × α)) :
    List (β × β) × Option (List (β × β)) :=
  (x.filterMap fun (a, b) => (lift a).2.map fun a => (a, (lift b).1),
   x.mapM fun (a, b) => (lift b).2.map fun b => ((lift a).1, b))

def Shape.plift : ∀ {n m}, Shape n → Shape m × Option (Shape m)
  | 0, _, .sort r | _+1, _, .sort r => (.sort r, some (.sort r))
  | 0, _, .bot | _+1, _, .bot => (.bot, some .bot)
  | _+1, 0, _ => (.bot, none)
  | _+1, _+1, .forallE s f =>
    let (s₀, s₁) := s.plift
    let (f₀, f₁) := ShapeFun.plift plift f
    (.forallE s₀ f₀, return .forallE (← s₁) (← f₁))
  | _+1, _+1, .lam f =>
    let (f₀, f₁) := ShapeFun.plift plift f
    (.lam f₀, return .lam (← f₁))
  | _+1, _+1, .ctor c l => (.ctor c (l.map (·.plift.1)), return .ctor c (← l.mapM (·.plift.2)))
  | _+1, _+1, .indTy r => (.indTy r, some (.indTy r))

omit [Params] in
theorem Shape.plift_eq_lift (le : n ≤ m) {s : Shape n} :
    s.plift = (s.lift m, some (s.lift m)) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, s.plift = (s.lift m, some (s.lift m)))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.plift plift s = (ShapeFun.lift (lift m) s, some (ShapeFun.lift (lift m) s)) := by
    simp only [ShapeFun.plift, ShapeFun.lift, IH le]; congr 1
    · rw [← List.filterMap_eq_map]; rfl
    · rw [List.mapM_eq_some, List.forall₂_map_right_iff]
      exact .rfl fun _ _ => rfl
  unfold plift; split <;> simp [lift] at le ⊢ <;> simp [plift_eq_lift le, go plift_eq_lift le]
  · exact ⟨_, List.mapM_pure, rfl⟩

omit [Params] in
theorem ShapeFun.plift_eq_lift (le : n ≤ m) {s : ShapeFun n} :
    plift Shape.plift s = (lift (Shape.lift m) s, some (lift (Shape.lift m) s)) :=
  Shape.plift_eq_lift.go Shape.plift_eq_lift le

omit [Params] in
theorem Shape.plift_lift (le : n ≤ m) {s : Shape n} :
    (s.lift m).plift = (s, some s) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, (s.lift m).plift = (s, some s))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.plift plift (ShapeFun.lift (lift m) s) = (s, some s) := by
    simp only [ShapeFun.plift, ShapeFun.lift, List.filterMap_map, List.mapM_map]; congr 1
    · refine .trans ?_ List.filterMap_some; congr 1; funext (a, b); simp [IH le]
    · rw [List.mapM_eq_some]; refine .rfl fun (a, b) _ => by simp [IH le]
  unfold lift; split <;> (try cases m) <;> try simp [plift, sort, bot] at le ⊢
  · cases le; cases s <;> grind
  · simp [plift_lift le, go plift_lift le]
  · simp [go plift_lift le]
  · simp [Function.comp_def, plift_lift le]
    exact ⟨_, List.mapM_pure, List.map_id _ ▸ rfl⟩

omit [Params] in
@[simp] theorem Shape.bot_plift : (bot (n := n)).plift (m := m) = (bot, some bot) := by
  cases n <;> simp [bot, plift]

omit [Params] in
theorem List.mapM_mapM_option (f : α → Option β) (g : β → Option γ) :
    (List.mapM f l).bind (List.mapM g) = List.mapM (f · |>.bind g) l := by
  induction l with simp [Option.bind_assoc] | cons a l ih
  congr 1; ext1; rw [Option.bind_comm]; congr 1; ext1; simp [← ih, Option.bind_assoc]

omit [Params] in
theorem Shape.plift_plift (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) {s : Shape n₁} :
    ((s.plift.1 : Shape n₂).plift.1 : Shape n₃) = s.plift.1 ∧
    (s.plift.2 : Option (Shape n₃)) = (s.plift.2 : Option (Shape n₂)).bind (·.plift.2) := by
  suffices ∀ {n₁ n₂ n₃}, n₂ ≤ n₁ → n₃ ≤ n₂ → ∀ {s : Shape n₁},
      ((s.plift.1 : Shape n₂).plift.1 : Shape n₃) = s.plift.1 ∧
      (s.plift.2 : Option (Shape n₃)) = (s.plift.2 : Option (Shape n₂)).bind (·.plift.2) by
    obtain le | le := le
    · simp [plift_eq_lift le]
      obtain h1 | h1 := Nat.le_total n₂ n₃
      · simp [plift_eq_lift h1, plift_eq_lift (Nat.le_trans le h1), lift_lift (.inl le)]
      obtain h2 | h2 := Nat.le_total n₁ n₃
      · rw [← lift_lift (.inl h2), plift_lift h1, plift_eq_lift h2]; exact ⟨rfl, rfl⟩
      · rw [← (this le h2).1, (this le h2).2, plift_lift le]; exact ⟨rfl, rfl⟩
    · obtain h1 | h1 := Nat.le_total n₂ n₁
      · rw [(this h1 le).1, (this h1 le).2]; exact ⟨rfl, rfl⟩
      simp [plift_eq_lift h1]
      obtain h2 | h2 := Nat.le_total n₁ n₃
      · rw [← lift_lift (.inl h2), plift_lift le, plift_eq_lift h2]; exact ⟨rfl, rfl⟩
      · rw [← (this h1 h2).1, (this h1 h2).2, plift_lift h1]; exact ⟨rfl, rfl⟩
  intro n₁ n₂ n₃ h1 h2 s
  induction n₁ generalizing n₂ n₃ with
  | zero => cases h1; simp [plift_eq_lift (Nat.le_refl _), lift_self] | succ n₁ ih
  cases n₂ with | zero => cases h2; simp [plift_eq_lift (Nat.le_refl _), lift_self] | succ n₂
  cases n₃ with
  | zero =>
    cases s with simp [plift]
    | forallE s f => cases s.plift.2 <;> simp; cases (ShapeFun.plift plift f).2 <;> simp [plift]
    | lam f => cases (ShapeFun.plift plift f).2 <;> simp [plift]
    | ctor _ l => cases eq: l.mapM (·.plift (m := n₂) |>.2) <;> simp [plift]
  | succ n₃
  simp at h1 h2; replace ih {s} := ih (s := s) h1 h2
  let rec go {s : ShapeFun n₁} :
      (ShapeFun.plift (plift (m := n₃)) (ShapeFun.plift (plift (m := n₂)) s).1).1 =
      (ShapeFun.plift plift s).1 ∧
      ((ShapeFun.plift plift s).2 : Option (ShapeFun n₃)) =
      ((ShapeFun.plift plift s).2 : Option (ShapeFun n₂)).bind (ShapeFun.plift plift · |>.2) := by
    simp [ShapeFun.plift]; constructor
    · rw [List.filterMap_filterMap]; congr 1; ext1 ⟨x, y⟩; dsimp
      simp [Option.bind_map, Function.comp_def]
      have := @ih x; revert this
      cases (x.plift.2 : Option (Shape n₂)) <;> simp +contextual [ih.1]
    · rw [List.mapM_mapM_option]; congr 1; ext1
      simp [Option.map_eq_bind, Option.bind_assoc, Function.comp_def, ih]
  cases s with simp [plift, ih, go, Function.comp_def, Option.bind_assoc]
  | forallE => congr 1; ext; rw [Option.bind_comm]
  | ctor _ l =>
    rw [← Option.bind_assoc]; congr 1
    induction l with simp | cons a l ihl
    simp [Option.bind_assoc, ihl]; congr 1; ext1; rw [Option.bind_comm]

omit [Params] in
theorem ShapeFun.plift_plift (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) {s : ShapeFun n₁} :
    (plift (Shape.plift (m := n₃)) (plift (Shape.plift (m := n₂)) s).1).1 =
    (plift Shape.plift s).1 ∧
    ((plift Shape.plift s).2 : Option (ShapeFun n₃)) =
    ((plift Shape.plift s).2 : Option (ShapeFun n₂)).bind (plift Shape.plift · |>.2) :=
  Shape.plift_plift.go _ _ _ (Shape.plift_plift le)

omit [Params] in
theorem Shape.plift_thm (le : n ≤ m) {s : Shape m} {t : Shape n} :
    (t.lift m ≤ s ↔ t ≤ (s.plift (m := n)).1) ∧
    (s ≤ t.lift m ↔ ∃ z, (s.plift (m := n)).2 = some z ∧ z ≤ t) := by
  let rec go {n m}
      (IH : n ≤ m → ∀ {s : Shape m} {t : Shape n},
        (t.lift m ≤ s ↔ t ≤ s.plift.1) ∧ (s ≤ t.lift m ↔ ∃ z, s.plift.2 = some z ∧ z ≤ t))
      (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
      (ShapeFun.LE (ShapeFun.lift (lift _) t) s ↔ ShapeFun.LE t (ShapeFun.plift plift s).1) ∧
      (ShapeFun.LE s (ShapeFun.lift (lift _) t) ↔
        ∃ z, (ShapeFun.plift plift s).2 = some z ∧ ShapeFun.LE z t) := by
    simp [ShapeFun.LE, ShapeFun.ble, ShapeFun.lift, ShapeFun.plift, List.mapM_eq_some,
      -List.any_filterMap, -Prod.forall]
    refine ⟨⟨fun H (a, b) h => ?_, fun H (a, b) h => ?_⟩,
      ⟨fun H => ?_, fun ⟨l, hl, hl2⟩ (a, b) h => ?_⟩⟩
    · obtain ⟨a₁, b₁, h1, h2, h3⟩ := H _ h
      have ⟨z, hz, hz2⟩ := (IH le).2.1 h2
      exact ⟨_, _, ⟨_, _, h1, _, hz, rfl, rfl⟩, hz2, (IH le).1.1 h3⟩
    · obtain ⟨_, _, ⟨_, _, h1, _, h2, rfl, rfl⟩, h3, h4⟩ := H _ h
      exact ⟨_, _, h1, (IH le).2.2 ⟨_, h2, h3⟩, (IH le).1.2 h4⟩
    · induction s with | nil => exact ⟨[], .nil, nofun⟩ | cons p s ih
      simp only [List.mem_cons, or_imp, forall_and, forall_eq] at H
      have ⟨⟨a', b', h1, h2, h3⟩, H⟩ := H
      have ⟨l, hl, hl2⟩ := ih H
      have ⟨z, hz, hz2⟩ := (IH le).2.1 h3
      refine ⟨_::l, .cons ⟨_, hz, rfl⟩ hl, ?_⟩
      exact List.forall_mem_cons.2 ⟨⟨_, _, h1, (IH le).1.1 h2, hz2⟩, hl2⟩
    · obtain ⟨_, h1, _, h2, rfl⟩ := hl.forall_exists_l _ h
      have ⟨_, _, h3, h4, h5⟩ := hl2 _ h1
      exact ⟨_, _, h3, (IH le).1.2 h4, (IH le).2.2 ⟨_, h2, h5⟩⟩
  unfold plift; split
    <;> (try (first | cases Nat.le_zero.1 le | cases n); cases t)
    <;> (try · simp [lift, sort, bot, (· ≤ ·), LE, ble])
    <;> (try · cases t <;> simp [lift, sort, bot, Shape.LE.def])
  · rename_i s _ _; cases s with
    | bot | sort => grind
    | _ => cases t <;> simp [lift, sort, bot, (· ≤ ·), LE, ble]
  all_goals have le := Nat.le_of_succ_le_succ le
  · cases t with simp [lift, sort, bot, Shape.LE.def]
    | forallE => ?_ | _ => intros; subst_vars; simp
    simp [Shape.plift_thm le,
      go Shape.plift_thm le]; grind
  · cases t with simp [lift, sort, bot, Shape.LE.def]
    | lam => ?_ | _ => intros; subst_vars; simp
    simp [go Shape.plift_thm le]; grind
  · cases t with simp [lift, sort, bot, Shape.LE.def, List.mapM_eq_some]
    | ctor => ?_ | _ => intros; subst_vars; simp
    refine ⟨fun _ => ?_, ?_, ?_⟩
    · apply Iff.of_eq; congr; funext a b
      exact propext (Shape.plift_thm le).1
    · rintro ⟨rfl, h⟩; rename_i c l _ l'
      suffices ∃ z, l.Forall₂ (·.plift.2 = some ·) z ∧ z.Forall₂ LE l' from
        have ⟨z, h1, h2⟩ := this; ⟨_, ⟨_, h1, rfl⟩, rfl, h2⟩
      induction h with | nil => exact ⟨_, .nil, .nil⟩ | cons h _ ih
      have ⟨a, a1, a2⟩ := (Shape.plift_thm le).2.1 h; have ⟨z, b1, b2⟩ := ih
      exact ⟨_, .cons a1 b1, .cons a2 b2⟩
    · rintro ⟨z, ⟨a, h1, rfl⟩, h2, h3⟩; refine ⟨h2, h1.trans (fun _ _ _ h1 h3 => ?_) h3⟩
      exact (Shape.plift_thm le).2.2 ⟨_, h1, h3⟩

omit [Params] in
theorem Shape.le_plift (le : n ≤ m) {s : Shape m} {t : Shape n} :
    t ≤ s.plift.1 ↔ t.lift m ≤ s := (Shape.plift_thm le).1.symm

omit [Params] in
theorem Shape.plift_le (le : n ≤ m) {s : Shape m} {t : Shape n} :
    (∃ z, s.plift.2 = some z ∧ z ≤ t) ↔ s ≤ t.lift m := (Shape.plift_thm le).2.symm

omit [Params] in
theorem ShapeFun.le_plift (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    LE t (plift Shape.plift s).1 ↔ LE (lift (Shape.lift m) t) s :=
  (Shape.plift_thm.go Shape.plift_thm le).1.symm

omit [Params] in
theorem ShapeFun.plift_le (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    (∃ z, (plift Shape.plift s).2 = some z ∧ LE z t) ↔ LE s (lift (Shape.lift m) t) :=
  (Shape.plift_thm.go Shape.plift_thm le).2.symm

omit [Params] in
theorem Shape.plift_mono {s t : Shape m} (H : s ≤ t) : (s.plift (m := n)).1 ≤ t.plift.1 := by
  obtain le | le := Nat.le_total m n
  · rw [Shape.plift_eq_lift le, Shape.plift_eq_lift le]; exact Shape.lift_mono H
  · exact (Shape.le_plift le).2 (.trans ((Shape.le_plift le).1 .rfl) H)

omit [Params] in
protected theorem Shape.Compat.plift {x y : Shape n} :
    (x.Compat y → (x.plift.1 : Shape m).Compat y.plift.1) ∧
    ∀ {x' y' : Shape m}, x.plift.2 = some x' → y.plift.2 = some y' → x'.Compat y' → x.Compat y := by
  obtain le | le := Nat.le_total n m
  · simp [plift_eq_lift le, Compat.lift le]
  refine ⟨fun h => ?_, fun h1 h2 h => ?_⟩
  · rw [← Compat.lift le]
    exact Compat.mono ((Shape.le_plift le).1 .rfl) ((Shape.le_plift le).1 .rfl) h
  · apply Compat.mono ((Shape.plift_le le).1 ⟨_, h1, .rfl⟩) ((Shape.plift_le le).1 ⟨_, h2, .rfl⟩)
    rwa [Compat.lift le]

def ShapeFun.olift (lift : α → Option β) (x : List (α × α)) : Option (List (β × β)) :=
  x.mapM fun (a, b) => return (← lift a, ← lift b)

def Shape.olift : ∀ {n m}, Shape n → Option (Shape m)
  | 0, _, .sort r | _+1, _, .sort r => some (.sort r)
  | 0, _, .bot | _+1, _, .bot => some .bot
  | _+1, 0, _ => none
  | _+1, _+1, .forallE s f => return .forallE (← s.olift) (← ShapeFun.olift olift f)
  | _+1, _+1, .lam f => return .lam (← ShapeFun.olift olift f)
  | _+1, _+1, .ctor c l => return .ctor c (← l.mapM (·.olift))
  | _+1, _+1, .indTy r => some (.indTy r)

omit [Params] in
theorem Shape.olift_eq_lift (le : n ≤ m) {s : Shape n} :
    s.olift = some (s.lift m) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, s.olift = some (s.lift m))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.olift olift s = some (ShapeFun.lift (lift m) s) := by
    simp only [ShapeFun.olift, ShapeFun.lift, IH le]
    rw [List.mapM_eq_some, List.forall₂_map_right_iff]
    exact .rfl fun _ _ => rfl
  unfold olift; split <;> simp [lift] at le ⊢ <;> simp [olift_eq_lift le, go olift_eq_lift le]
  · exact ⟨_, List.mapM_pure, rfl⟩

omit [Params] in
theorem ShapeFun.olift_eq_lift (le : n ≤ m) {s : ShapeFun n} :
    olift Shape.olift s = some (lift (Shape.lift m) s) :=
  Shape.olift_eq_lift.go Shape.olift_eq_lift le

omit [Params] in
theorem Shape.olift_thm (le : n ≤ m) {s : Shape m} {t : Shape n} :
    s.olift (m := n) = some t ↔ s = t.lift m := by
  let rec go {n m}
      (IH : n ≤ m → ∀ {s : Shape m} {t : Shape n}, s.olift (m := n) = some t ↔ s = t.lift m)
      (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
      ShapeFun.olift olift s = some t ↔ s = ShapeFun.lift (lift m) t := by
    simp [ShapeFun.lift, ShapeFun.olift, List.mapM_eq_some]
    rw [← List.forall₂_eq, List.forall₂_map_right_iff]
    apply iff_of_eq; congr; ext ⟨a, a'⟩ ⟨b, b'⟩; simp [IH le]
  unfold olift; split
    <;> (try first | cases Nat.le_zero.1 le | cases n)
    <;> cases t <;> simp [lift, bot, sort]
  iterate 4 · grind
  all_goals have le := Nat.le_of_succ_le_succ le
  · simp [olift_thm le, go olift_thm le]; grind
  · simp [go olift_thm le]; grind
  · simp [List.mapM_eq_some, olift_thm le]
    conv => rhs; apply ShapeS.ctor.injEq
    rw [← List.forall₂_eq, List.forall₂_map_right_iff]; grind
  · grind

omit [Params] in
theorem ShapeFun.olift_thm (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    olift Shape.olift s = some t ↔ s = lift (Shape.lift m) t :=
  Shape.olift_thm.go Shape.olift_thm le

omit [Params] in
theorem Shape.lift_inj (le : n ≤ m) {s t : Shape n} : s.lift m = t.lift m ↔ s = t := by
  refine ⟨fun H => ?_, (· ▸ rfl)⟩
  cases ((Shape.olift_thm le).2 H).symm.trans <| (Shape.olift_thm le).2 rfl; rfl

omit [Params] in
theorem ShapeFun.lift_inj (le : n ≤ m) {s t : ShapeFun n} :
    lift (Shape.lift m) s = lift (Shape.lift m) t ↔ s = t := by
  refine ⟨fun H => ?_, (· ▸ rfl)⟩
  cases ((ShapeFun.olift_thm le).2 H).symm.trans <| (ShapeFun.olift_thm le).2 rfl; rfl

omit [Params] in
@[simp] theorem Shape.olift_bot : Shape.olift (n := n) (m := m) .bot = some .bot := by
  cases n <;> cases m <;> rfl

omit [Params] in
@[simp] theorem ShapeFun.olift_bot :
    olift (Shape.olift (n := n) (m := m)) ShapeFun.bot = some ShapeFun.bot := by
  simp [bot, olift]

omit [Params] in
@[simp] theorem Shape.olift_sort : Shape.olift (n := n) (m := m) (.sort r) = some (.sort r) := by
  cases n <;> cases m <;> rfl

def ShapeFun.maxBelow (s : ShapeFun n) : Shape n × Shape n :=
  (s.find? fun (x, _) => s.all fun (x', _) => x' ≤ x).getD (.bot, .bot)

def ShapeFun.trunc (s : ShapeFun n) (a : Shape n) : ShapeFun n := s.filter (·.1 ≤ a)
def ShapeFun.app (s : ShapeFun n) (a : Shape n) : Shape n := maxBelow (s.trunc a) |>.2

omit [Params] in
theorem ShapeFun.lift_trunc (le : n ≤ m) :
    lift (Shape.lift m) (trunc f a : ShapeFun n) = trunc (lift (Shape.lift m) f) (a.lift m) := by
  simp [trunc, lift, List.filter_map]; congr 2; ext x; simp [Shape.lift_le_lift le]

omit [Params] in
theorem ShapeFun.lift_maxBelow {f : ShapeFun n} (le : n ≤ m) :
    (maxBelow f).1.lift m = (maxBelow (lift (Shape.lift m) f)).1 ∧
    (maxBelow f).2.lift m = (maxBelow (lift (Shape.lift m) f)).2 := by
  refine let F x := (x.1.lift m, x.2.lift m)
    have : F (maxBelow f) = maxBelow (lift (Shape.lift m) f) := ?_
    ⟨congrArg (·.1) this, congrArg (·.2) this⟩
  simp [maxBelow, lift]
  generalize eq₁ : List.find? .. = r, eq₂ : List.find? .. = r'
  suffices r = r' by subst this; cases r <;> simp [F]
  subst eq₁ eq₂; congr 1; ext x; simp; congr 1; ext y; simp [Shape.lift_le_lift le]

omit [Params] in
@[simp] theorem ShapeFun.lift_app (le : n ≤ m) :
    (app f a : Shape n).lift m = app (lift (Shape.lift m) f) (a.lift m) := by
  simp [app, lift_trunc le, lift_maxBelow le]

def ShapeFun.join (join : Shape n → Shape n → Shape n) (f f' : ShapeFun n) : ShapeFun n :=
  f.foldl (init := []) fun l x => f'.foldl (init := l) fun l y =>
  if x.1.Compat y.1 then let j := join x.1 y.1; (j, join (f.app j) (f'.app j)) :: l else l

omit [Params] in
theorem ShapeFun.mem_join {join} {f f' : ShapeFun n} {a} :
    a ∈ ShapeFun.join join f f' ↔ ∃ x ∈ f, ∃ y ∈ f', x.1.Compat y.1 ∧
      let j := join x.1 y.1; a = (j, join (f.app j) (f'.app j)) := by
  refine let F x := _; let G x y := _
    (?_ : a ∈ f.foldl (fun l x => f'.foldl (F x) l) [] ↔ (∃ x ∈ f, ∃ y ∈ f', G x y) ∨ a ∈ [])
    |>.trans (or_iff_left (by simp))
  generalize f = f₁, f' = f₂, [] = l
  induction f₁ generalizing l with simp [-Prod.exists, or_assoc, *] | cons _ f₁ ih
  refine .trans (or_congr_right ?_) or_left_comm; clear ih
  induction f₂ generalizing l <;> simp [-Prod.exists, or_assoc, *]
  refine .trans (or_congr_right ?_) or_left_comm
  unfold F G; split <;> rename_i h <;> simp [h]

def Shape.join : ∀ {n}, Shape n → Shape n → Shape n
  | 0, s, .bot | 0, .bot, s | _+1, .bot, s | _+1, s, .bot => s
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => if r = r' then .sort r else .bot
  | _+1, .forallE s f, .forallE s' f' => .forallE (join s s') (ShapeFun.join join f f')
  | _+1, .lam f, .lam f' => .lam (ShapeFun.join join f f')
  | _+1, .ctor c l, .ctor c' l' => if c = c' then .ctor c (l.zipWith join l') else .bot
  | _+1, .indTy r, .indTy r' => if r = r' then .indTy r else .bot
  | _+1, _, _ => .bot

omit [Params] in
theorem Shape.lift_join {x y : Shape n} (le : n ≤ m) :
    (x.join y).lift m = (x.lift m).join (y.lift m) := by
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases x <;> cases y <;> simp [lift, join, sort]; split <;> simp [lift, sort]
  | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x y} := @ih m x y le
  let rec go {x y : ShapeFun n} :
      ShapeFun.lift (lift m) (ShapeFun.join join x y) =
      ShapeFun.join join (ShapeFun.lift (lift m) x) (ShapeFun.lift (lift m) y) := by
    refine
      let G _ := _; let F l x := List.foldl (G x) l y
      let G' _ := _; let F' l x := List.foldl (G' x) l (ShapeFun.lift (lift m) y)
      have (r:_) : ShapeFun.lift (lift m) (x.foldl F r) =
        (ShapeFun.lift (lift m) x).foldl F' (r.map fun x => (lift m x.1, lift m x.2)) := ?_
      this []
    simp [ShapeFun.lift]; generalize x = x'; induction x' generalizing r <;> simp [*]; congr 1
    unfold F F'
    simp [ShapeFun.lift]; generalize y = y'; induction y' generalizing r <;> simp [*]; congr 1
    simp [G, G', Compat.lift le]; split <;> simp [ih, ShapeFun.lift_app le]
  cases x with cases y <;> simp [join, lift, go, sort, ih]
  | sort => split <;> simp [lift, sort]
  | ctor => split <;> simp [lift, ih]
  | indTy => split <;> simp [lift]

omit [Params] in
theorem Shape.bot_join {x : Shape n} : bot.join x = x := by cases n <;> cases x <;> rfl
omit [Params] in
theorem Shape.join_bot {x : Shape n} : x.join bot = x := by cases n <;> cases x <;> rfl
omit [Params] in
@[simp] theorem Shape.sort_join_sort :
    join (.sort r : Shape n) (.sort r') = if r = r' then .sort r else .bot := by cases n <;> rfl

omit [Params] in
theorem ShapeFun.lift_join {x y : ShapeFun n} (le : n ≤ m) :
    lift (Shape.lift m) (join Shape.join x y) =
    join Shape.join (lift (Shape.lift m) x) (lift (Shape.lift m) y) :=
  Shape.lift_join.go _ _ le (Shape.lift_join le)

def Shape.lam' (s : ShapeFun n) : Shape (n + 1) :=
  if s.all (·.2 ≤ .bot) then .bot else .lam s

def IsStruct [Params] (n : Name) : Bool := Params.classify n matches some (.etaCtor ..)

def Shape.ctor' (c : Name) (l : List (Shape n)) : Shape (n + 1) :=
  if IsStruct c ∧ l.all (· ≤ .bot) then .bot else .ctor c l

def Shape.trim : ∀ {n}, Shape n → Shape n
  | 0, s => s
  | _+1, .bot => .bot
  | _+1, .sort r => .sort r
  | _+1, .forallE s f => .forallE s.trim (f.map fun x => (x.1.trim, x.2.trim))
  | _+1, .lam f => .lam' (f.map fun x => (x.1.trim, x.2.trim))
  | _+1, .ctor c l => .ctor' c (l.map trim)
  | _+1, .indTy r => .indTy r

def ShapeFun.WF (WF : Shape n → Prop) (f : ShapeFun n) : Prop :=
  ((∃ y, (.bot, y) ∈ f) ∧ ∀ x ∈ f, ∀ y ∈ f,
    (x.1.Compat y.1 → ∃ z ∈ f, x.1.join y.1 ≤ z.1 ∧ z.1 ≤ x.1.join y.1) ∧
    (x.1 ≤ y.1 → x.2 ≤ y.2)) ∧
  ∀ x ∈ f, WF x.1 ∧ WF x.2

def ShapeFun.NonZero (f : ShapeFun n) := ∃ x ∈ f, ¬x.2 ≤ .bot
def Shape.ListNonZero (l : List (Shape n)) := ∃ x ∈ l, ¬x ≤ .bot

instance {f : ShapeFun n} : Decidable f.NonZero :=
  inferInstanceAs (Decidable (∃ x ∈ f, ¬x.2 ≤ .bot))
instance {l : List (Shape n)} : Decidable (Shape.ListNonZero l) :=
  inferInstanceAs (Decidable (∃ x ∈ l, ¬x ≤ .bot))

omit [Params] in
theorem ShapeFun.NonZero.mono {f f' : ShapeFun n} (le : f.LE f') : NonZero f → NonZero f'
  | ⟨_, h1, h2⟩ => have ⟨_, _, a1, _, a2⟩ := ShapeFun.LE.def.1 le _ _ h1; ⟨_, a1, mt a2.trans h2⟩

omit [Params] in
theorem Shape.ListNonZero.mono {l l' : List (Shape n)}
    (le : l.Forall₂ (· ≤ ·) l') : ListNonZero l → ListNonZero l'
  | ⟨_, h1, h2⟩ => have ⟨_, a1, a2⟩ := le.forall_exists_l _ h1; ⟨_, a1, mt a2.trans h2⟩

def Shape.WF : ∀ {n}, Shape n → Prop
  | 0, _ | _+1, .bot | _+1, .sort .. => True
  | _+1, .forallE s f => s.WF ∧ ShapeFun.WF WF f
  | _+1, .lam f => ShapeFun.WF WF f ∧ ShapeFun.NonZero f
  | _+1, .ctor n l => (∀ x ∈ l, WF x) ∧ (IsStruct n → ListNonZero l)
  | _+1, .indTy _ => True

omit [Params] in
theorem ShapeFun.NonZero.lift_iff {n m} {x : ShapeFun n} (le : n ≤ m) :
    NonZero (lift (Shape.lift m) x) ↔ NonZero (n := n) x := by
  simp [NonZero, lift]
  refine ⟨fun ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, h2⟩ => ?_, fun ⟨_, _, h1, h2⟩ => ?_⟩
  · exact ⟨_, _, h1, mt ((Shape.lift_le_bot le).2 ∘ Shape.le_bot.1) h2⟩
  · exact ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, mt (Shape.le_bot.2 ∘ (Shape.lift_le_bot le).1) h2⟩

omit [Params] in
theorem Shape.ListNonZero.lift_iff {n m} {x : List (Shape n)} (le : n ≤ m) :
    ListNonZero (x.map (lift m)) ↔ ListNonZero (n := n) x := by
  simp [ListNonZero]
  constructor
  · exact fun ⟨_, ⟨_, h1, rfl⟩, h2⟩ => ⟨_, h1, mt ((Shape.lift_le_bot le).2 ∘ Shape.le_bot.1) h2⟩
  · exact fun ⟨_, h1, h2⟩ => ⟨_, ⟨_, h1, rfl⟩, mt (Shape.le_bot.2 ∘ (Shape.lift_le_bot le).1) h2⟩

theorem Shape.WF.lift_iff (le : n ≤ m) : WF (x.lift m) ↔ WF (n := n) x := by
  induction n generalizing m with | zero => cases m <;> cases x <;> trivial | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x} := @ih m x le
  let rec go {x : ShapeFun n} : ShapeFun.WF WF (ShapeFun.lift (lift m) x) ↔ ShapeFun.WF WF x := by
    simp only [ShapeFun.WF, ShapeFun.lift, List.mem_map, Prod.mk.injEq,
      lift_eq_bot le, Prod.exists, exists_and_right, forall_exists_index, and_imp, Prod.forall]
    constructor
    · intro ⟨⟨⟨_, _, _, a1, rfl, rfl⟩, a2⟩, a3⟩; refine ⟨⟨⟨_, a1⟩, ?_⟩, fun _ _ h1 => ?_⟩
      · intro _ _ h1 _ _ h2; have := a2 _ _ _ _ h1 rfl rfl _ _ _ _ h2 rfl rfl
        simp [lift_le_lift le, Compat.lift le, ← lift_join le] at this
        refine ⟨fun h => ?_, this.2⟩
        let ⟨_, ⟨_, _, _, b1, rfl, rfl⟩, b2⟩ := this.1 h
        simp only [lift_le_lift le] at b2; exact ⟨_, ⟨_, b1⟩, b2⟩
      · simpa only [ih] using a3 _ _ _ _ h1 rfl rfl
    · intro ⟨⟨⟨_, a1⟩, a2⟩, a3⟩; refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact ⟨_, _, _, a1, rfl, rfl⟩
      · intro _ _ _ _ h1 rfl rfl _ _ _ _ h2 rfl rfl; have := a2 _ _ h1 _ _ h2
        simp [lift_le_lift le, Compat.lift le, ← lift_join le]
        refine ⟨fun h => ?_, this.2⟩
        let ⟨_, ⟨_, b1⟩, b2⟩ := this.1 h
        refine ⟨_, ⟨_, _, _, b1, rfl, rfl⟩, ?_⟩; simpa only [lift_le_lift le] using b2
      · intro _ _ _ _ h1 rfl rfl; simpa only [ih] using a3 _ _ h1
  cases x with simp [lift, WF, go, *]
  | lam => exact fun _ => ShapeFun.NonZero.lift_iff le
  | ctor => exact fun _ => imp_congr_right fun _ => Shape.ListNonZero.lift_iff le

theorem ShapeFun.WF.lift_iff {x : ShapeFun n} (le : n ≤ m) :
    WF Shape.WF (lift (Shape.lift m) x) ↔ WF Shape.WF x :=
  Shape.WF.lift_iff.go _ _ le (Shape.WF.lift_iff le)

protected theorem Shape.WF.lift (le : n ≤ m) : WF (n := n) x → WF (x.lift m) := (lift_iff le).2

protected theorem ShapeFun.WF.lift {x : ShapeFun n} (le : n ≤ m) : WF Shape.WF x →
    WF Shape.WF (lift (Shape.lift m) x) := (lift_iff le).2

protected theorem Shape.WF.olift {x : Shape n} (H : x.olift (m := m) = some x') :
    WF x ↔ WF x' := by
  obtain le | le := Nat.le_total n m
  · cases olift_eq_lift le ▸ H; rw [WF.lift_iff le]
  · cases (olift_thm le).1 H; rw [WF.lift_iff le]

protected theorem ShapeFun.WF.olift {x : ShapeFun n}
    (H : olift (Shape.olift (m := m)) x = some x') : WF Shape.WF x ↔ WF Shape.WF x' := by
  obtain le | le := Nat.le_total n m
  · cases ShapeFun.olift_eq_lift le ▸ H; rw [WF.lift_iff le]
  · cases (olift_thm le).1 H; rw [WF.lift_iff le]

protected theorem Shape.WF.bot : (Shape.bot (n := n)).WF := by cases n <;> trivial
protected theorem Shape.WF.sort : (Shape.sort (n := n) r).WF := by cases n <;> trivial

protected theorem ShapeFun.WF.bot : (ShapeFun.bot (n := n)).WF Shape.WF := by
  simp [WF, bot, Shape.Compat.bot_l, Shape.bot_join, Shape.WF.bot]

@[implicit_reducible] def WShape (n : Nat) := {s : Shape n // s.WF}
@[implicit_reducible] def WShapeFun (n : Nat) := {s : ShapeFun n // s.WF Shape.WF}

instance : Membership (WShape n × WShape n) (WShapeFun n) := ⟨fun f a => (a.1.1, a.2.1) ∈ f.1⟩

theorem WShapeFun.mem_def {f : WShapeFun n} : a ∈ f ↔ (a.1.1, a.2.1) ∈ f.1 := .rfl

theorem WShapeFun.mem_val {f : WShapeFun n} {s t : Shape n} (h : (s, t) ∈ f.1) :
    (⟨s, (f.2.2 _ h).1⟩, ⟨t, (f.2.2 _ h).2⟩) ∈ f := h
theorem WShapeFun.mem_val' {f : WShapeFun n} {s t : Shape n} (h : (s, t) ∈ f.1) :
    ∃ hs ht, (⟨s, hs⟩, ⟨t, ht⟩) ∈ f := ⟨(f.2.2 _ h).1, (f.2.2 _ h).2, h⟩

def WShapeFun.elems (f : WShapeFun n) : List (WShape n × WShape n) :=
  f.1.pmap (fun a wf => (⟨a.1, wf.1⟩, ⟨a.2, wf.2⟩)) f.2.2

@[simp] theorem WShapeFun.mem_elems {f : WShapeFun n} : a ∈ f.elems ↔ a ∈ f := by
  simp only [elems, List.mem_pmap, Prod.exists, mem_def]
  exact ⟨fun ⟨_, _, h, rfl⟩ => h, fun h => ⟨_, _, h, rfl⟩⟩

@[ext] theorem WShape.ext {s t : WShape n} (h : s.1 = t.1) : s = t := Subtype.ext h
@[ext] theorem WShapeFun.ext {s t : WShapeFun n} (h : s.1 = t.1) : s = t := Subtype.ext h

def WShapeFun.NonZero (f : WShapeFun n) := f.1.NonZero
instance {f : WShapeFun n} : Decidable f.NonZero := inferInstanceAs (Decidable f.1.NonZero)

def WShape.bot : WShape n := ⟨.bot, .bot⟩
def WShape.sort (r : Bool) : WShape n := ⟨.sort r, .sort⟩
abbrev WShape.type : WShape n := .sort true
abbrev WShape.prop : WShape n := .sort false
def WShape.indTy (r : Bool) : WShape (n+1) := ⟨.indTy r, trivial⟩
def WShape.forallE (s : WShape n) (f : WShapeFun n) : WShape (n + 1) := ⟨.forallE s.1 f.1, s.2, f.2⟩
def WShape.lam (f : WShapeFun n) (h : f.NonZero) :
    WShape (n + 1) := ⟨.lam f.1, f.2, h⟩
def WShape.lam' (f : WShapeFun n) : WShape (n + 1) := if h : f.NonZero then .lam f h else .bot
theorem WShape.lam_eq_lam' {f : WShapeFun n} {hl} : WShape.lam f hl = .lam' f := by
  simp [lam', hl]

def WShape.ListNonZero (l : List (WShape n)) := ∃ x ∈ l, ¬x.1 ≤ .bot
instance {l : List (WShape n)} : Decidable (WShape.ListNonZero l) :=
  inferInstanceAs (Decidable (∃ x ∈ l, ¬x.1 ≤ .bot))

theorem WShape.ListNonZero.def {l : List (WShape n)} :
    ListNonZero l ↔ Shape.ListNonZero (l.map (·.1)) := by
  simp only [ListNonZero, Shape.ListNonZero, List.mem_map]
  exact ⟨fun ⟨_, h1, h2⟩ => ⟨_, ⟨_, h1, rfl⟩, h2⟩, fun ⟨_, ⟨_, h1, rfl⟩, h2⟩ => ⟨_, h1, h2⟩⟩
def WShape.ctor (c : Name) (l : List (WShape n))
    (H : IsStruct c → ListNonZero l) : WShape (n + 1) := by
  refine ⟨.ctor c (l.map (·.1)), fun _ h => ?_, ListNonZero.def.1 ∘ H⟩
  have ⟨x, _, eq⟩ := List.mem_map.1 h; exact eq ▸ x.2
def WShape.ctor' (c : Name) (l : List (WShape n)) : WShape (n + 1) :=
  if h : IsStruct c → ListNonZero l then
    .ctor c l (by simpa [Shape.le_bot] using h)
  else .bot

theorem WShape.mk_ctor {n} (l : List (Shape n)) (wf : Shape.WF (n := n+1) (.ctor c l)) :
    ∃ h, WShape.ctor c (l.pmap Subtype.mk wf.1) h = ⟨.ctor c l, wf⟩ := by
  refine ⟨fun h => ?_, Subtype.ext ?_⟩
  · simp [ListNonZero]; let ⟨_, h1, h2⟩ := wf.2 h; exact ⟨_, ⟨_, h1, rfl⟩, h2⟩
  · simp [WShape.ctor]; congr 1; rw [List.map_pmap, List.pmap_eq_map, List.map_id']

theorem WShape.ctor_eq_ctor' : ctor c l h = ctor' c l := by rw [ctor', dif_pos]

def WShapeFun.bot {n : Nat} : WShapeFun n := ⟨.bot, .bot⟩

theorem WShapeFun.NonZero.bot : ¬NonZero (n := n) .bot := by
  simp [NonZero, WShapeFun.bot, ShapeFun.bot, ShapeFun.NonZero]

@[simp] theorem WShape.lam'_bot : WShape.lam' (n := n) .bot = .bot := by
  simp [lam', WShapeFun.NonZero.bot]

theorem WShapeFun.mem_bot : (x, y) ∈ WShapeFun.bot ↔ x = .bot ∧ y = .bot := by
  simp [WShapeFun.mem_def, bot, WShape.ext_iff, WShape.bot, ShapeFun.bot]

/-- Case split on a `WShape (n+1)`. -/
@[elab_as_elim]
def WShape.casesOn' {motive : WShape (n+1) → Sort u}
    (s : WShape (n+1))
    (bot : motive .bot)
    (sort : ∀ r, motive (.sort r))
    (forallE : ∀ s f, motive (.forallE s f))
    (lam : ∀ f h, motive (.lam f h))
    (ctor : ∀ c l h, motive (.ctor c l h))
    (indTy : ∀ r, motive (.indTy r)) : motive s := by
  obtain ⟨s, wf⟩ := s
  cases s with
  | bot => exact bot
  | sort r => exact sort r
  | forallE s' f' => exact forallE ⟨s', wf.1⟩ ⟨f', wf.2⟩
  | lam f' => exact lam ⟨f', wf.1⟩ wf.2
  | ctor c l => exact (WShape.mk_ctor l wf).2 ▸ ctor ..
  | indTy r => exact indTy r

/-- Case split on a `WShape n`. -/
@[elab_as_elim]
def WShape.casesOn {motive : ∀ {n}, WShape n → Sort u}
    {n} (s : WShape n)
    (bot : motive (n := n) .bot)
    (sort : ∀ r, motive (n := n) (.sort r))
    (forallE : ∀ {n'} s f, motive (n := n'+1) (.forallE s f))
    (lam : ∀ {n'} f h, motive (n := n'+1) (.lam f h))
    (ctor : ∀ {n'} c l h, motive (n := n'+1) (.ctor c l h))
    (indTy : ∀ {n'} (r), motive (n := n'+1) (.indTy r)) : motive s := by
  cases n with
  | zero =>
    obtain ⟨s, wf⟩ := s
    cases s with
    | bot => exact bot
    | sort r => exact sort r
  | succ n => exact s.casesOn' bot sort forallE lam ctor indTy

def WShape.lift {n} (m) (s : WShape n) : WShape m := by
  refine ⟨(s.1.olift (m := m)).getD .bot, ?_⟩
  cases eq : s.1.olift <;> [exact .bot; exact (Shape.WF.olift eq).1 s.2]

def WShapeFun.lift {n} (m) (s : WShapeFun n) : WShapeFun m := by
  refine ⟨(ShapeFun.olift Shape.olift s.1).getD ShapeFun.bot, ?_⟩
  cases eq : ShapeFun.olift Shape.olift s.1 <;> [exact .bot; exact (ShapeFun.WF.olift eq).1 s.2]

abbrev WShape.LE (a b : WShape n) := a.1 ≤ b.1
abbrev WShapeFun.LE (a b : WShapeFun n) := a.1.LE b.1
instance : LE (WShape n) := ⟨WShape.LE⟩
instance : LE (WShapeFun n) := ⟨WShapeFun.LE⟩

instance : DecidableRel (α := WShape n) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (a.1 ≤ b.1))
instance : DecidableRel (α := WShapeFun n) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a.1.LE b.1))

theorem WShape.LE.def {a b : WShape n} : a ≤ b ↔ a.1 ≤ b.1 := .rfl
theorem WShapeFun.LE.def {a b : WShapeFun n} : a ≤ b ↔ a.1.LE b.1 := .rfl

theorem WShapeFun.NonZero.iff {f : WShapeFun n} : f.NonZero ↔ ∃ x ∈ f, ¬x.2 ≤ .bot :=
  ⟨fun ⟨_, h1, h2⟩ => ⟨_, f.mem_val h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨_, h1, h2⟩⟩

theorem WShapeFun.NonZero.mono {f f' : WShapeFun n} :
    (h1 : f.LE f') → (h2 : NonZero f) → NonZero f' :=
  ShapeFun.NonZero.mono

theorem WShape.ListNonZero.mono {l l' : List (WShape n)}
    (le : l.Forall₂ (· ≤ ·) l') : ListNonZero l → ListNonZero l' := by
  simp [ListNonZero.def]; apply Shape.ListNonZero.mono; simpa

theorem WShape.lift_val {s : WShape n} (le : n ≤ m) : (s.lift m).1 = s.1.lift m := by
  simp [lift, Shape.olift_eq_lift le]

theorem WShapeFun.lift_val {s : WShapeFun n} (le : n ≤ m) :
    (s.lift m).1 = ShapeFun.lift (Shape.lift m) s.1 := by
  simp [lift, ShapeFun.olift_eq_lift le]

theorem WShapeFun.mem_lift {s : WShapeFun n} (le : n ≤ m) :
    (x, x') ∈ s.lift m ↔ ∃ y y', (y, y') ∈ s ∧ x = y.lift m ∧ x' = y'.lift m := by
  cases x; cases x'
  simp [mem_def, lift_val le, WShape.lift_val le, ShapeFun.lift, WShape.ext_iff]
  constructor <;> exact fun ⟨_, _, h1, h2, h3⟩ => ⟨_, _, s.mem_val h1, h2.symm, h3.symm⟩

theorem WShape.forallE.inj {f : WShapeFun n} :
    WShape.forallE a f = WShape.forallE a' f' ↔ a = a' ∧ f = f' := by
  simp [WShape.ext_iff, WShapeFun.ext_iff, forallE]
  exact iff_of_eq (ShapeS.forallE.injEq ..)

@[simp] theorem WShape.lift_bot : (WShape.bot : WShape n).lift m = .bot := by
  ext; simp [lift, bot]

@[simp] theorem WShapeFun.lift_bot : WShapeFun.lift (n := n) m .bot = .bot := by
  ext1; simp [WShapeFun.lift, bot, ShapeFun.olift_bot]

@[simp] theorem WShape.lift_sort : (WShape.sort r : WShape n).lift m = .sort r := by
  ext; simp [lift, sort]

@[simp] theorem WShape.lift_type : (WShape.type (n := n)).lift m = WShape.type := WShape.lift_sort

@[simp] theorem WShape.lift_indTy {n m : Nat} {r} :
    (.indTy r : WShape (n+1)).lift (m+1) = .indTy r :=
  Subtype.ext <| by simp [lift, indTy, Shape.olift]

theorem WShape.lift_self {s : WShape n} : s.lift n = s := by
  ext; rw [lift_val (Nat.le_refl _), Shape.lift_self]

theorem WShapeFun.lift_self {s : WShapeFun n} : s.lift n = s := by
  ext; rw [lift_val (Nat.le_refl _), ShapeFun.lift_self]

theorem WShape.lift_lift {s : WShape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift n₃ := by
  ext; simp [lift]
  by_cases h1 : n₁ ≤ n₂
  · congr 1; ext t; rw [Shape.olift_eq_lift h1, Option.getD]
    obtain h2 | h2 := Nat.le_total n₂ n₃
    · rw [Shape.olift_eq_lift h2, Shape.lift_lift (.inl h1),
        Shape.olift_eq_lift (Nat.le_trans h1 h2)]
    rw [Shape.olift_thm h2]
    obtain h3 | h3 := Nat.le_total n₁ n₃
    · rw [Shape.olift_eq_lift h3, Option.some_inj, ← Shape.lift_lift (.inl h3), Shape.lift_inj h2]
    · rw [Shape.olift_thm h3, ← Shape.lift_lift (.inl h3), Shape.lift_inj h1]
  · have h2 := le.resolve_left h1; have h1 := Nat.le_of_not_ge h1
    cases eq : s.1.olift (m := n₂) <;> simp
    · cases eq' : s.1.olift (m := n₃) <;> simp
      rw [Shape.olift_thm (Nat.le_trans h2 h1), ← Shape.lift_lift (.inl h2),
        ← Shape.olift_thm h1, eq] at eq'; cases eq'
    · rw [(Shape.olift_thm h1).1 eq]; rename_i t
      cases eq₁ : t.olift
      · cases eq₂ : (Shape.lift n₁ t).olift; · rfl
        rw [Shape.olift_thm (Nat.le_trans h2 h1), ← Shape.lift_lift (.inl h2)] at eq₂
        rw [(Shape.lift_inj h1).1 eq₂, (Shape.olift_thm h2).2 rfl] at eq₁; cases eq₁
      · rw [(Shape.olift_thm h2).1 eq₁, Shape.lift_lift (.inl h2),
          (Shape.olift_thm (Nat.le_trans h2 h1)).2 rfl]

theorem WShapeFun.lift_lift {s : WShapeFun n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift n₃ := by
  ext1; simp [lift]
  by_cases h1 : n₁ ≤ n₂
  · congr 1; ext t; rw [ShapeFun.olift_eq_lift h1, Option.getD]
    obtain h2 | h2 := Nat.le_total n₂ n₃
    · rw [ShapeFun.olift_eq_lift h2, ShapeFun.lift_lift (.inl h1),
        ShapeFun.olift_eq_lift (Nat.le_trans h1 h2)]
    rw [ShapeFun.olift_thm h2]
    obtain h3 | h3 := Nat.le_total n₁ n₃
    · rw [ShapeFun.olift_eq_lift h3, Option.some_inj, ← ShapeFun.lift_lift (.inl h3),
        ShapeFun.lift_inj h2]
    · rw [ShapeFun.olift_thm h3, ← ShapeFun.lift_lift (.inl h3), ShapeFun.lift_inj h1]
  · have h2 := le.resolve_left h1; have h1 := Nat.le_of_not_ge h1
    cases eq : ShapeFun.olift (Shape.olift (m := n₂)) s.1 <;> simp
    · cases eq' : ShapeFun.olift (Shape.olift (m := n₃)) s.1 <;> simp
      rw [ShapeFun.olift_thm (Nat.le_trans h2 h1), ← ShapeFun.lift_lift (.inl h2),
        ← ShapeFun.olift_thm h1, eq] at eq'; cases eq'
    · rw [(ShapeFun.olift_thm h1).1 eq]; rename_i t
      cases eq₁ : ShapeFun.olift Shape.olift t
      · cases eq₂ : ShapeFun.olift Shape.olift (ShapeFun.lift (Shape.lift n₁) t); · rfl
        rw [ShapeFun.olift_thm (Nat.le_trans h2 h1), ← ShapeFun.lift_lift (.inl h2)] at eq₂
        rw [(ShapeFun.lift_inj h1).1 eq₂, (ShapeFun.olift_thm h2).2 rfl] at eq₁; cases eq₁
      · rw [(ShapeFun.olift_thm h2).1 eq₁, ShapeFun.lift_lift (.inl h2),
          (ShapeFun.olift_thm (Nat.le_trans h2 h1)).2 rfl]

theorem WShape.lift_le_lift {s t : WShape n} (le : n ≤ m) :
    s.lift m ≤ t.lift m ↔ s ≤ t := by
  show (s.lift m).1 ≤ (t.lift m).1 ↔ s.1 ≤ t.1
  rw [lift_val le, lift_val le]; exact Shape.lift_le_lift le

theorem WShapeFun.lift_le_lift {s t : WShapeFun n} (le : n ≤ m) :
    s.lift m ≤ t.lift m ↔ s ≤ t := by
  show (s.lift m).1.LE (t.lift m).1 ↔ s.1.LE t.1
  rw [lift_val le, lift_val le]; exact ShapeFun.lift_le_lift le

theorem WShapeFun.lift_mono {s t : WShapeFun n} (le : n ≤ m) (h : s ≤ t) : s.lift m ≤ t.lift m :=
  (lift_le_lift le).2 h

theorem WShapeFun.LE.def' {f f' : WShapeFun n} : f ≤ f' ↔
    ∀ x y : WShape n, (x, y) ∈ f → ∃ x' y' : WShape n, (x', y') ∈ f' ∧ x' ≤ x ∧ y ≤ y' := by
  simp [(· ≤ ·), ShapeFun.LE.def]
  constructor <;> intro H x y h1
  · have ⟨_, _, h2, h3⟩ := H _ _ h1
    exact ⟨⟨_, (f'.2.2 _ h2).1⟩, ⟨_, (f'.2.2 _ h2).2⟩, h2, h3⟩
  · have ⟨x', y', h2, h3⟩ := H ⟨_, (f.2.2 _ h1).1⟩ ⟨_, (f.2.2 _ h1).2⟩ h1
    exact ⟨_, _, h2, h3⟩

theorem WShape.lift_mono {s t : WShape n} (le : n ≤ m) : s ≤ t → s.lift m ≤ t.lift m :=
  (lift_le_lift le).2

theorem WShape.lift_le_bot {s : WShape n} (h : n ≤ m) : s.lift m ≤ .bot ↔ s = .bot := by
  rw [← WShape.lift_bot (n := n), WShape.lift_le_lift h]
  exact ⟨fun h => WShape.ext (Shape.le_bot.1 h), fun h => h ▸ Shape.LE.rfl⟩

theorem WShape.lift_eq_bot {s : WShape n} (h : n ≤ m) : s.lift m = .bot ↔ s = .bot := by
  exact ⟨fun h' => (lift_le_bot h).1 (h' ▸ Shape.LE.rfl), fun h' => h' ▸ lift_bot⟩

theorem WShape.le_bot {s : WShape n} : s ≤ .bot ↔ s = .bot :=
  Shape.le_bot.trans (Subtype.ext_iff (a1 := s) (a2 := WShape.bot)).symm

@[simp] theorem WShape.lift_forallE {s : WShape n} {f : WShapeFun n} (h : n ≤ m) :
    (WShape.forallE s f).lift (m+1) = .forallE (s.lift m) (f.lift m) := by
  ext; simp [lift_val (Nat.succ_le_succ h), Shape.lift, WShape.forallE,
    lift_val h, WShapeFun.lift_val h]

theorem WShapeFun.NonZero.lift_iff {n m} {x : WShapeFun n} (le : n ≤ m) :
    (x.lift m).NonZero ↔ NonZero (n := n) x := by
  simp [NonZero, lift_val le, ShapeFun.NonZero.lift_iff le]

theorem WShape.ListNonZero.lift_iff {n m} {x : List (WShape n)} (le : n ≤ m) :
    ListNonZero (x.map (lift m)) ↔ ListNonZero (n := n) x := by
  simp [ListNonZero.def, ← Shape.ListNonZero.lift_iff le]
  apply iff_of_eq; congr 2; ext x; simp [lift_val le]

@[simp] theorem WShape.lift_lam' {f : WShapeFun n} (le : n ≤ m) :
    (WShape.lam' f).lift (m+1) = .lam' (f.lift m) := by
  ext1; simp [lam']; split <;> simp [WShapeFun.lift_val le, WShapeFun.NonZero.lift_iff le,
    lift_val (Nat.succ_le_succ le), lam, Shape.lift, *]

theorem WShape.lift_lam {f : WShapeFun n} {hl} (h : n ≤ m) :
    (WShape.lam f hl).lift (m+1) = .lam (f.lift m) ((WShapeFun.NonZero.lift_iff h).2 hl) := by
  ext1; simp [WShape.lift_val (Nat.succ_le_succ h), lam, WShapeFun.lift_val h, Shape.lift]

theorem WShape.lift_eq_lam' {s : WShape (n+1)} (le : n ≤ m)
    {f : WShapeFun m} (eq : s.lift (m+1) = .lam' f) :
    s = .bot ∧ f ≤ .bot ∨ ∃ f' : WShapeFun n, s = .lam' f' ∧ f = f'.lift m := by
  obtain ⟨f, hf⟩ := f
  have eq := congrArg (·.1) eq; simp [lift_val (Nat.succ_le_succ le)] at eq
  unfold lam' at eq; split at eq <;> rename_i h <;>
    obtain ⟨⟨⟩, wf⟩ := s <;> simp [lam, Shape.lift] at eq <;> cases eq
  · refine .inr ⟨⟨_, wf.1⟩, ?_⟩; rw [lam', dif_pos (by exact (ShapeFun.NonZero.lift_iff le).1 h)]
    exact ⟨rfl, WShapeFun.ext (WShapeFun.lift_val le ▸ rfl)⟩
  · refine .inl ⟨rfl, WShapeFun.LE.def'.2 fun x y h => ?_⟩; rename_i hn
    refine ⟨_, _, WShapeFun.mem_bot.2 ⟨rfl, rfl⟩, Shape.bot_le, Decidable.by_contra (hn ⟨_, h, ·⟩)⟩

theorem WShape.lift_ctor {c : Name} {l : List (WShape n)} {hc} (le : n ≤ m) :
    (WShape.ctor c l hc).lift (m+1) =
    .ctor c (l.map (.lift m)) ((WShape.ListNonZero.lift_iff le).2 ∘ hc) := by
  ext1; simp [WShape.lift_val (Nat.succ_le_succ le), ctor, Shape.lift]
  congr 2; ext1 x; simp [lift_val le]

@[simp] theorem WShape.lift_ctor' {c : Name} {l : List (WShape n)} (le : n ≤ m) :
    (WShape.ctor' c l).lift (m+1) = .ctor' c (l.map (.lift m)) := by
  ext1; simp [ctor']; split <;> rename_i hc <;>
    [rw [dif_pos ((WShape.ListNonZero.lift_iff le).2 ∘ hc)];
     rw [dif_neg (mt ((WShape.ListNonZero.lift_iff le).1 ∘ ·) hc)]] <;>
    simp [lift_val (Nat.succ_le_succ le), ctor, Shape.lift]
  congr 2; ext1 x; simp [lift_val le]

@[simp] theorem WShape.bot_le : WShape.bot ≤ (s : WShape n) := Shape.bot_le

protected theorem WShape.LE.rfl {s : WShape n} : s ≤ s := Shape.LE.rfl
protected theorem WShape.LE.trans {s t u : WShape n} : s ≤ t → t ≤ u → s ≤ u := Shape.LE.trans

theorem WShape.LE.forallE_decomp {s : WShape (n+1)} {a : WShape n} {f : WShapeFun n} :
    s ≤ .forallE a f → s = .bot ∨ ∃ a' f', s = .forallE a' f' := by
  simp [WShape.LE.def, Shape.LE.def, forallE]; obtain ⟨⟨⟩, _⟩ := s <;> simp
  · simp [bot, Shape.bot]
  · rename_i wf; intros; exact .inr ⟨⟨_, wf.1⟩, ⟨_, wf.2⟩, rfl⟩

@[simp] theorem WShape.forallE_le_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    WShape.forallE a f ≤ .forallE a' f' ↔ a ≤ a' ∧ f ≤ f' := Shape.forallE_le_forallE

theorem WShape.le_forallE_iff {s : WShape (n+1)} {a' : WShape n} {f' : WShapeFun n} :
    s ≤ .forallE a' f' ↔ s = .bot ∨ ∃ a f, s = .forallE a f ∧ a ≤ a' ∧ f ≤ f' := by
  constructor
  · cases s using WShape.casesOn' with
    | bot => exact fun _ => .inl rfl
    | forallE a f => exact fun h => .inr ⟨a, f, rfl, forallE_le_forallE.1 h⟩
    | indTy => apply Not.elim; simp [indTy, forallE, LE.def, Shape.LE.def]
    | _ => simp only [sort, lam, ctor, forallE, LE.def, Shape.LE.def, false_implies]
  · rintro (rfl | ⟨a, f, rfl, h1, h2⟩)
    · exact bot_le
    · exact forallE_le_forallE.2 ⟨h1, h2⟩

theorem WShape.le_sort {s : WShape n} : s ≤ .sort r ↔ s = .bot ∨ s = .sort r :=
  Shape.le_sort.trans <| by simp [WShape.ext_iff, WShape.bot, WShape.sort]

theorem WShape.sort_le {s : WShape n} : .sort r ≤ s ↔ .sort r = s :=
  Shape.sort_le.trans <| by simp [WShape.ext_iff, WShape.sort]

theorem WShape.le_indTy {s : WShape (n+1)} {r} : s ≤ .indTy r ↔ s = .bot ∨ s = .indTy r :=
  Shape.le_indTy.trans <| by simp [WShape.ext_iff, WShape.bot, WShape.indTy]

theorem WShape.indTy_le {s : WShape (n+1)} {r} : .indTy r ≤ s ↔ s = .indTy r :=
  Shape.indTy_le.trans ⟨(Subtype.ext ·), (congrArg (·.1) ·)⟩

theorem WShape.forallE_le {s : WShape (n+1)} {a : WShape n} {f : WShapeFun n} :
    WShape.forallE a f ≤ s ↔
      ∃ a' : WShape n, ∃ f' : WShapeFun n, a ≤ a' ∧ f ≤ f' ∧ s = .forallE a' f' := by
  constructor
  · intro h
    have ⟨a', b', h1, h2, h3⟩ := Shape.forallE_le.1 h
    have wf := h3 ▸ s.2
    exact ⟨⟨a', wf.1⟩, ⟨b', wf.2⟩, h1, h2, WShape.ext h3.symm⟩
  · intro ⟨a', f', h1, h2, h3⟩; subst h3; exact WShape.forallE_le_forallE.2 ⟨h1, h2⟩

theorem WShape.lam_le_lam {f f' : WShapeFun n} {hf hf'} :
    WShape.lam f hf ≤ .lam f' hf' ↔ f ≤ f' := .rfl

theorem WShape.lam'_le_lam' {f f' : WShapeFun n} :
    WShape.lam' f ≤ .lam' f' ↔ f ≤ f' := by
  simp [WShape.LE.def, lam', WShapeFun.LE.def]
  split <;> [split <;> rename_i h h'; rename_i h] <;> simp [lam, bot, Shape.LE.def, ShapeFun.LE.def]
  · let ⟨_, h1, h2⟩ := h
    refine ⟨_, _, h1, fun _ _ h3 h4 h5 => h' ⟨_, h3, mt h5.trans h2⟩⟩
  · intro _ y h1; have h2 := Decidable.by_contra (mt (⟨_, h1, ·⟩) h)
    have ⟨_, h⟩ := f'.2.1.1; exact ⟨_, _, h, Shape.bot_le, .trans h2 Shape.bot_le⟩

theorem WShape.LE.le_lam {s : WShape (n+1)} {f : WShapeFun n} {hl} :
    s ≤ .lam f hl → s = .bot ∨ ∃ f' hl', s = .lam f' hl' := by
  simp [WShape.LE.def, Shape.LE.def, lam]; obtain ⟨⟨⟩, _⟩ := s <;> simp
  · simp [bot, Shape.bot]
  · rename_i wf; intros; exact .inr ⟨⟨_, wf.1⟩, wf.2, rfl⟩

theorem WShape.LE.lam_le {s : WShape (n+1)} {f : WShapeFun n} {hl} :
    .lam f hl ≤ s → ∃ f' hl', s = .lam f' hl' := by
  simp [WShape.LE.def, Shape.LE.def, lam]; obtain ⟨⟨⟩, _⟩ := s <;> simp
  rename_i wf; intros; exact ⟨⟨_, wf.1⟩, wf.2, rfl⟩

theorem WShape.LE.le_lam' {s : WShape (n+1)} {f : WShapeFun n} :
    s ≤ .lam' f → ∃ f', s = .lam' f' := by
  rw [lam']; split
  · intro h; obtain rfl | ⟨_, h, rfl⟩ := h.le_lam
    · exact ⟨.bot, by simp⟩
    · exact ⟨_, lam_eq_lam'⟩
  · simp [le_bot]; rintro rfl; exact ⟨.bot, by simp⟩

theorem WShape.lam.inj {f f' : WShapeFun n} {h h'} :
    WShape.lam f h = WShape.lam f' h' ↔ f = f' := by
  simp [WShape.ext_iff, WShapeFun.ext_iff, lam]
  exact iff_of_eq (ShapeS.lam.injEq ..)

theorem WShape.ctor.inj {f f' : List (WShape n)} {h h'} :
    WShape.ctor c f h = WShape.ctor c' f' h' ↔ c = c' ∧ f = f' := by
  simp [WShape.ext_iff, ctor]
  refine iff_of_eq (ShapeS.ctor.injEq ..) |>.trans ?_
  exact and_congr_right' <| List.map_inj_right fun _ _ => Subtype.ext

theorem WShapeFun.bot_mem (f : WShapeFun n) : ∃ y, (.bot, y) ∈ f :=
  let ⟨_, h⟩ := f.2.1.1; ⟨_, f.mem_val h⟩

@[simp] theorem WShapeFun.bot_le {f : WShapeFun n} : bot ≤ f := by
  simp [LE.def', mem_bot, WShape.le_bot, and_left_comm, WShape.bot_le, f.bot_mem]

def WShape.Compat (a b : WShape n) : Prop := a.1.Compat b.1
def WShapeFun.Compat (a b : WShapeFun n) : Prop := ShapeFun.Compat Shape.Compat a.1 b.1
instance : Decidable (WShape.Compat a b) := inferInstanceAs (Decidable (_ = true))
instance : Decidable (WShapeFun.Compat a b) := inferInstanceAs (Decidable (_ = true))

@[simp] theorem WShape.Compat.bot_l {n} {s : WShape n} : bot.Compat s := Shape.Compat.bot_l
@[simp] theorem WShape.Compat.bot_r {n} {s : WShape n} : s.Compat bot := Shape.Compat.bot_r
@[simp] theorem WShape.Compat.sort_sort : Compat (sort r : WShape n) (sort r') ↔ r = r' :=
  Shape.Compat.sort_sort

@[simp] theorem WShape.Compat.forallE_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    (WShape.forallE a f).Compat (.forallE a' f') ↔ a.Compat a' ∧ WShapeFun.Compat f f' :=
  Shape.Compat.forallE_forallE

@[simp] theorem WShape.Compat.lam_lam {f f' : WShapeFun n} {hf hf'} :
    (WShape.lam f hf).Compat (.lam f' hf') ↔ WShapeFun.Compat f f' := Shape.Compat.lam_lam

@[simp] theorem WShape.Compat.ctor_ctor {l l' : List (WShape n)} {hl hl'} :
    (WShape.ctor c l hl).Compat (.ctor c' l' hl') ↔ c = c' ∧ l.Forall₂ Compat l' := by
  simp [WShape.Compat, ctor, Shape.Compat.ctor_ctor]; intro; rfl

theorem WShape.Compat.lam'_lam' {f f' : WShapeFun n} (H : f.Compat f') :
    (WShape.lam' f).Compat (.lam' f') := by
  unfold lam'; split <;> [split <;> [exact lam_lam.2 H; exact .bot_r]; exact .bot_l]

theorem WShape.Compat.ctor'_ctor' {l l' : List (WShape n)}
    (H : l.Forall₂ Compat l') : (WShape.ctor' c l).Compat (.ctor' c l') := by
  unfold ctor'; split <;> [split <;> [exact ctor_ctor.2 ⟨rfl, H⟩; exact .bot_r]; exact .bot_l]

theorem WShapeFun.Compat.def {n} {f f' : WShapeFun n} :
    f.Compat f' ↔ ∀ x ∈ f, ∀ y ∈ f', x.1.Compat y.1 → x.2.Compat y.2 := by
  simp [Compat, ShapeFun.Compat.def]
  constructor <;> intro H _ _ h1 _ _ h2
  · exact H _ _ h1 _ _ h2
  · exact H _ _ (f.mem_val h1) _ _ (f'.mem_val h2)

theorem WShapeFun.join_mem' {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ z, z ∈ f ∧ x.1.join x'.1 ≤ z.1.1 ∧ z.1.1 ≤ x.1.join x'.1 := by
  let ⟨_, h1, h2⟩ := (f.2.1.2 _ (f.mem_val hx) _ (f.mem_val hy)).1 hc
  exact ⟨_, f.mem_val h1, h2⟩

theorem WShapeFun.mem_mono {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) : x ≤ x' → y ≤ y' :=
  (f.2.1.2 _ (f.mem_val hx) _ (f.mem_val hy)).2

protected theorem WShape.Compat.lift {x y : WShape n} (le : n ≤ m) :
    (x.lift m).Compat (y.lift m) ↔ x.Compat y := by
  simp [WShape.Compat, lift_val le, Shape.Compat.lift le]

omit [Params] in
theorem ShapeFun.mem_trunc {f : ShapeFun n} : x ∈ f.trunc a ↔ x ∈ f ∧ x.1 ≤ a := by simp [trunc]

namespace WShape.join_prop
variable (ih : ∀ {x y : WShape n}, (∀ z, x ≤ z → y ≤ z → x.Compat y) ∧
  (x.Compat y → (x.1.join y.1).WF ∧ ∀ z, x.1.join y.1 ≤ z.1 ↔ x ≤ z ∧ y ≤ z))
include ih

theorem exists_max {f : WShapeFun n}
    (hc : ∀ x ∈ f, ∀ y ∈ f, x.1.Compat y.1) : ∃ x ∈ f.1, ∀ x' ∈ f.1, x'.1 ≤ x.1 := by
  suffices ∀ l : ShapeFun n, (∀ x ∈ l, x ∈ f.1) → ∃ x ∈ f.1, ∀ x' ∈ l, x'.1 ≤ x.1 from
    have ⟨_, h1, h2⟩ := this _ fun _ => id; ⟨_, f.mem_val h1, fun _ => h2 _⟩
  intro l hl; induction l with
  | nil => let ⟨_, h⟩ := f.2.1.1; exact ⟨_, h, nofun⟩
  | cons a l ihl =>
    have ⟨hm, hl⟩ := List.forall_mem_cons.1 hl
    have ⟨x, h1, h2⟩ := ihl hl
    have := hc _ (f.mem_val hm) _ (f.mem_val h1)
    have ⟨_, a1, a2⟩ := f.join_mem' (f.mem_val hm) (f.mem_val h1) this
    have ⟨b1, b2⟩ := ((ih.2 this).2 ⟨_, (f.2.2 _ a1).1⟩).1 a2.1
    exact ⟨_, a1, List.forall_mem_cons.2 ⟨b1, fun _ h => (h2 _ h).trans b2⟩⟩

def wf_trunc (f : WShapeFun n) (a : WShape n) : WShapeFun n := by
  refine ⟨f.1.trunc a.1, ?_, fun _ h1 => f.2.2 _ (ShapeFun.mem_trunc.1 h1).1⟩
  simp [ShapeFun.trunc]
  refine ⟨f.2.1.1, fun _ _ h1 h2 _ _ h3 h4 => ?_⟩
  have ⟨a1, a2, h1⟩ := f.mem_val' h1; have ⟨b1, b2, h3⟩ := f.mem_val' h3
  have ⟨a3, a4⟩ := f.2.1.2 _ h1 _ h3; refine ⟨fun h => ?_, a4⟩
  have ⟨⟨z, z'⟩, a5, a6⟩ := a3 h
  refine ⟨_, ⟨⟨_, a5⟩, a6.2.trans ?_⟩, a6⟩
  exact (ih.2 <| (@ih ⟨_, a1⟩ ⟨_, b1⟩).1 _ h2 h4).2 _ |>.2 ⟨h2, h4⟩

theorem trunc_compat (f : WShapeFun n) (a : WShape n)
    {{x}} (h1 : x ∈ wf_trunc ih f a) {{y}} (h2 : y ∈ wf_trunc ih f a) : x.1.Compat y.1 :=
  have ⟨a1, a2⟩ := ShapeFun.mem_trunc.1 h1
  have ⟨b1, b2⟩ := ShapeFun.mem_trunc.1 h2
  (@ih ⟨_, (f.2.2 _ a1).1⟩ ⟨_, (f.2.2 _ b1).1⟩).1 a a2 b2

theorem app_core (f : WShapeFun n) (x : WShape n) :
    ∃ x', x' ≤ x.1 ∧ (x', f.1.app x.1) ∈ f.1 ∧ ∀ y ∈ f.1, y.1 ≤ x.1 → y.2 ≤ f.1.app x.1 := by
  simp only [ShapeFun.app, ShapeFun.maxBelow]
  have ⟨_, h1, h2⟩ := exists_max ih (trunc_compat ih f x)
  simp [wf_trunc, ShapeFun.mem_trunc] at h1 h2
  show let P := _; ∃ x', x' ≤ x.1 ∧ let y' := ((List.find? P _).getD (Shape.bot, Shape.bot)).snd
    (x', y') ∈ f.1 ∧ ∀ y ∈ f.1, y.1 ≤ x.1 → y.2 ≤ y'
  intro P
  have ⟨⟨x', y'⟩, h⟩ := Option.isSome_iff_exists.1 <|
    (List.find?_isSome (p := P)).2 ⟨_, ShapeFun.mem_trunc.2 h1, by simpa [P, ShapeFun.mem_trunc]⟩
  have := List.find?_some h; simp [P, ShapeFun.mem_trunc, h] at this ⊢
  have ⟨h1, h2⟩ := ShapeFun.mem_trunc.1 <| List.mem_of_find?_eq_some h
  exact ⟨_, h2, h1, fun _ _ a1 a2 => (f.2.1.2 _ a1 _ h1).2 (this _ _ a1 a2)⟩

theorem of_compat {x x' : WShape n} (hc : x.Compat x') :
    ∃ j : WShape n, j.1 = x.1.join x'.1 ∧ ∀ w, j ≤ w ↔ x ≤ w ∧ x' ≤ w :=
  ⟨⟨_, (ih.2 hc).1⟩, rfl, (ih.2 hc).2⟩

theorem join_mem' {f : WShapeFun n} {x y x' y'}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ j : WShape n, j.1 = x.1.join x'.1 ∧ ∃ z, z ∈ f ∧ j ≤ z.1 ∧ z.1 ≤ j ∧
      ∀ w, j ≤ w ↔ x ≤ w ∧ x' ≤ w :=
  let ⟨_, a1, a2, a3⟩ := f.join_mem' hx hy hc
  ⟨⟨_, (ih.2 hc).1⟩, rfl, _, a1, a2, a3, (ih.2 hc).2⟩

theorem compat_app_r {f : WShapeFun n} {x x' : WShape n} (hc : x.Compat x') :
    (f.1.app x.1).Compat (f.1.app x'.1) :=
  have ⟨_, a1, a2, _⟩ := app_core ih f x; have a2 := f.mem_val a2
  have ⟨_, b1, b2, _⟩ := app_core ih f x'; have b2 := f.mem_val b2
  have ⟨_, _, _, c2, c3, _, c5⟩ := join_mem' ih a2 b2 (Shape.Compat.mono a1 b1 hc)
  have ⟨c6, c7⟩ := (c5 _).1 .rfl
  ih.1 _ (f.mem_mono a2 c2 (c6.trans c3)) (f.mem_mono b2 c2 (c7.trans c3))

theorem compat_app_l {f f' : WShapeFun n} (hc : f.Compat f') (x : WShape n) :
    (f.1.app x.1).Compat (f'.1.app x.1) := by
  have ⟨_, a1, a2, _⟩ := app_core ih f x; have ⟨a4, a5, a2⟩ := f.mem_val' a2
  have ⟨_, b1, b2, _⟩ := app_core ih f' x; have ⟨b4, b5, b2⟩ := f'.mem_val' b2
  exact (ShapeFun.Compat.def.1 hc _ a2 _ b2 ((@ih ⟨_, a4⟩ ⟨_, b4⟩).1 _ a1 b1) :)

theorem ih_fun {f f' : WShapeFun n} :
    (∀ z, f ≤ z → f' ≤ z → f.Compat f') ∧
    (f.Compat f' → ∃ h, ∀ z, ⟨ShapeFun.join Shape.join f.1 f'.1, h⟩ ≤ z ↔ f ≤ z ∧ f' ≤ z) := by
  simp only [WShapeFun.LE.def']
  refine ⟨fun z le₁ le₂ => ShapeFun.Compat.def.2 fun _ h1 _ h2 h => ?_, fun hc => ?_⟩
  · have ⟨_, _, a1, a2, a3⟩ := le₁ _ _ (f.mem_val h1)
    have ⟨_, _, b1, b2, b3⟩ := le₂ _ _ (f'.mem_val h2)
    have h := Shape.Compat.mono a2 b2 h
    refine Shape.Compat.mono a3 b3 ?_
    have ⟨_, c1, c2, c3⟩ := z.join_mem' a1 b1 h
    have ⟨e1, e2⟩ := ((ih.2 h).2 _).1 c2
    exact ih.1 _ (z.mem_mono a1 c1 e1) (z.mem_mono b1 c1 e2)
  simp only [ShapeFun.WF, ShapeFun.mem_join]
  refine ⟨⟨⟨?_, ?_⟩, fun a => ?_⟩, ?_⟩
  · let ⟨_, a1⟩ := f.bot_mem; let ⟨_, a2⟩ := f'.bot_mem
    refine ⟨_, _, a1, _, a2, Compat.bot_l, cast (Prod.mk.injEq ..).symm ⟨.symm ?_, rfl⟩⟩
    exact Shape.le_bot.1 <| ((ih.2 .bot_l).2 _).2 ⟨.rfl, .rfl⟩
  · rintro _ ⟨x, a1, x', a2, a3, rfl⟩ _ ⟨y, b1, y', b2, b3, rfl⟩
    replace a1 := f.mem_val a1; replace a2 := f'.mem_val a2
    replace b1 := f.mem_val b1; replace b2 := f'.mem_val b2
    change Compat ⟨x.1, (f.2.2 _ a1).1⟩ ⟨x'.1, (f'.2.2 _ a2).1⟩ at a3
    change Compat ⟨y.1, (f.2.2 _ b1).1⟩ ⟨y'.1, (f'.2.2 _ b2).1⟩ at b3
    dsimp only
    have ⟨a, a5, a6⟩ := of_compat ih a3; have ⟨a31, a32⟩ := (a6 _).1 .rfl; have ac := ih.1 _ a31 a32
    have ⟨b, b5, b6⟩ := of_compat ih b3; have ⟨b31, b32⟩ := (b6 _).1 .rfl; have bc := ih.1 _ b31 b32
    refine ⟨fun h1 => ?_, fun h1 => a5 ▸ b5 ▸ ?_⟩
    · have h1' : a.Compat b := by simp [Compat, a5, b5, h1]
      have ⟨c, c1, c2⟩ := of_compat ih h1'; have ⟨c3, c4⟩ := (c2 _).1 .rfl
      have dc := ih.1 _ (a31.trans c3) (b31.trans c4)
      have ⟨d, d1, d', d2, d3, d4, d5⟩ := join_mem' ih a1 b1 dc; have ⟨d6, d7⟩ := (d5 _).1 .rfl
      have ec := ih.1 _ (a32.trans c3) (b32.trans c4)
      have ⟨e, e1, e', e2, e3, e4, e5⟩ := join_mem' ih a2 b2 ec; have ⟨e6, e7⟩ := (e5 _).1 .rfl
      have h4 := d4.trans <| (d5 _).2 ⟨a31.trans c3, b31.trans c4⟩
      have h5 := e4.trans <| (e5 _).2 ⟨a32.trans c3, b32.trans c4⟩
      have hc := ih.1 _ h4 h5
      have ⟨j, j1, j2⟩ := of_compat ih hc; have ⟨j3, j4⟩ := (j2 _).1 .rfl
      refine ⟨_, ⟨_, d2, _, e2, hc, rfl⟩, j1 ▸ a5 ▸ b5 ▸ c1 ▸ ?_⟩; dsimp only
      refine ⟨(c2 _).2 ⟨?_, ?_⟩, (j2 _).2 ⟨h4, h5⟩⟩
      · exact (a6 _).2 ⟨d6.trans (d3.trans j3), e6.trans (e3.trans j4)⟩
      · exact (b6 _).2 ⟨d7.trans (d3.trans j3), e7.trans (e3.trans j4)⟩
    · have ⟨_, c1, c2, _⟩ := app_core ih f a; have ⟨c3, c4, c2⟩ := f.mem_val' c2
      have ⟨_, d1, d2, _⟩ := app_core ih f' a; have ⟨d3, d4, d2⟩ := f'.mem_val' d2
      have ⟨_, f1, f2, cf⟩ := app_core ih f b; have ⟨f3, f4, f2⟩ := f.mem_val' f2
      have ⟨_, g1, g2, dg⟩ := app_core ih f' b; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
      have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, c4⟩) (x' := ⟨_, d4⟩) (compat_app_l ih hc a)
      have ⟨k, k1, k2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc b)
      refine e1 ▸ k1 ▸ (e2 _).2 ⟨?_, ?_⟩
      · exact (cf _ c2 (c1.trans (a5 ▸ b5 ▸ h1))).trans ((k2 _).1 .rfl).1
      · exact (dg _ d2 (d1.trans (a5 ▸ b5 ▸ h1))).trans ((k2 _).1 .rfl).2
  · rintro ⟨b, b3, c, c3, a1, rfl⟩
    have ⟨b1, b2, b3⟩ := f.mem_val' b3; have ⟨c1, c2, c3⟩ := f'.mem_val' c3
    have ⟨d, d1, d2⟩ := of_compat ih (x := ⟨_, b1⟩) (x' := ⟨_, c1⟩) a1
    have ⟨_, f1, f2, cf⟩ := app_core ih f d; have ⟨f3, f4, f2⟩ := f.mem_val' f2
    have ⟨_, g1, g2, dg⟩ := app_core ih f' d; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
    have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc d)
    refine d1 ▸ e1 ▸ ⟨d.2, e.2⟩
  · intro f₃; conv =>
      enter [1,x,y,1]; (conv => apply propext WShapeFun.mem_def); simp only [ShapeFun.mem_join]
    refine ⟨fun H => ?_, fun ⟨H1, H2⟩ => ?_⟩
    · refine ⟨fun x y hf => ?_, fun x y hf' => ?_⟩
      · have ⟨_, hf'⟩ := f'.bot_mem
        have ⟨_, f1, f2, cf⟩ := app_core ih f x; have ⟨f3, f4, f2⟩ := f.mem_val' f2
        have ⟨_, g1, g2, dg⟩ := app_core ih f' x; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
        have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc x)
        have ⟨c₁, c₂, c1, c2, c3⟩ := H ⟨_, Shape.join_bot ▸ x.2⟩ ⟨_, Shape.join_bot ▸ e1 ▸ e.2⟩
          ⟨_, hf, _, hf', Compat.bot_r, rfl⟩
        simp only [bot, Shape.join_bot] at c2 c3
        exact ⟨_, _, c1, c2, .trans ((cf _ hf .rfl).trans (e1 ▸ (show _ ≤ e.1 from ((e2 _).1 .rfl).1) :)) c3⟩
      · have ⟨_, hf⟩ := f.bot_mem
        have ⟨_, f1, f2, cf⟩ := app_core ih f x; have ⟨f3, f4, f2⟩ := f.mem_val' f2
        have ⟨_, g1, g2, dg⟩ := app_core ih f' x; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
        have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc x)
        have ⟨c₁, c₂, c1, c2, c3⟩ := H ⟨_, Shape.bot_join ▸ x.2⟩ ⟨_, Shape.bot_join ▸ e1 ▸ e.2⟩
          ⟨_, hf, _, hf', Compat.bot_l, rfl⟩
        simp only [bot, Shape.bot_join] at c2 c3
        exact ⟨_, _, c1, c2, .trans ((dg _ hf' .rfl).trans (e1 ▸ (show _ ≤ e.1 from ((e2 _).1 .rfl).2) :)) c3⟩
    · rintro ⟨_, hx⟩ ⟨_, hy⟩ ⟨x, a3, y, b3, xy, ⟨⟩⟩
      have ⟨a1, a2, a3⟩ := f.mem_val' a3; have ⟨b1, b2, b3⟩ := f'.mem_val' b3
      have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, a1⟩) (x' := ⟨_, b1⟩) xy
      have ⟨f₁, f1, f2, cf⟩ := app_core ih f e; have ⟨f3, f4, f2⟩ := f.mem_val' f2
      have ⟨g₁, g1, g2, dg⟩ := app_core ih f' e; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
      have ⟨i, i1, i2, hi⟩ := app_core ih f₃ e; have ⟨i3, i4, i2⟩ := f₃.mem_val' i2
      have ⟨j, j1, j2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc e)
      have ⟨l1, l2⟩ := (e2 _).1 .rfl
      refine ⟨_, _, i2, (e1 ▸ i1 :), ?_⟩
      simp only [WShape.LE.def, ← e1, ← j1]
      refine (j2 ⟨_, i4⟩).2 ⟨?_, ?_⟩
      · have ⟨m, m', m1, m2, m3⟩ := H1 _ _ f2; exact m3.trans (hi _ m1 (m2.trans f1))
      · have ⟨m, m', m1, m2, m3⟩ := H2 _ _ g2; exact m3.trans (hi _ m1 (m2.trans g1))

end WShape.join_prop

theorem WShape.join_prop {x y : WShape n} :
    (∀ z, x ≤ z → y ≤ z → x.Compat y) ∧
    (x.Compat y → (x.1.join y.1).WF ∧ ∀ z, x.1.join y.1 ≤ z.1 ↔ x ≤ z ∧ y ≤ z) := by
  induction n with
  | zero =>
    obtain ⟨⟨⟩, wf⟩ := x <;> obtain ⟨⟨⟩, _⟩ := y <;>
      simp +contextual [(·≤·), Compat, Shape.LE, Shape.ble, Shape.Compat, Shape.join, *]
    refine ⟨?_, (· ▸ ⟨wf, ?_⟩)⟩ <;> rintro ⟨⟨⟩⟩ <;> simp [Shape.ble]
    exact (·.trans ·.symm)
  | succ n ih
  have go {f f' : ShapeFun n} (wf : ShapeFun.WF Shape.WF f) (wf' : ShapeFun.WF Shape.WF f') :=
    @join_prop.ih_fun _ _ @ih ⟨f, wf⟩ ⟨f', wf'⟩
  let ⟨x, wf⟩ := x; let ⟨y, wf'⟩ := y
  simp only [WShape.LE.def]; simp [WShape, Compat]
  constructor
  · (cases x with | bot => exact fun _ _ _ _ => Shape.Compat.bot_l | _) <;>
    rintro ⟨⟩ wf₃ h2 h3 <;> simp [Shape.LE.def] at h2 <;>
    (cases y with | bot => exact Shape.Compat.bot_r | _) <;>
    simp [Shape.LE.def, Shape.Compat] at h3 ⊢ <;> dsimp [Shape.WF] at wf wf' wf₃
    · exact h2.trans h3.symm
    · exact ⟨(@ih ⟨_, wf.1⟩ ⟨_, wf'.1⟩).1 ⟨_, wf₃.1⟩ h2.1 h3.1,
        (go wf.2 wf'.2).1 ⟨_, wf₃.2⟩ h2.2 h3.2⟩
    · exact (go wf.1 wf'.1).1 ⟨_, wf₃.1⟩ h2 h3
    · refine ⟨h2.1.trans h3.1.symm, h2.2.and_mem.trans ?_ h3.2.and_mem.flip⟩
      rintro _ _ _ ⟨h1, h2, h3⟩ ⟨h4, h5, _⟩
      exact (@ih ⟨_, wf.1 _ h2⟩ ⟨_, wf'.1 _ h5⟩).1 ⟨_, wf₃.1 _ h3⟩ h1 h4
    · exact h2.trans h3.symm
  · (cases x with | bot => intro; exact ⟨wf', fun _ _ => (and_iff_right Shape.bot_le).symm⟩ | _) <;>
    (cases y with | bot => intro; exact ⟨wf, fun _ _ => (and_iff_left Shape.bot_le).symm⟩ | _) <;>
    simp [Shape.WF] at wf wf' <;>
    simp +contextual [Shape.Compat, Shape.join, Shape.sort, Shape.LE.def, Shape.WF]
    · intro h1 h2
      have ⟨a1, a2⟩ := (@ih ⟨_, wf.1⟩ ⟨_, wf'.1⟩).2 h1
      have ⟨b1, b2⟩ := (go wf.2 wf'.2).2 h2
      simp only [WShape.LE.def, WShapeFun.LE.def] at a1 a2 b1 b2
      simp [WShape, WShapeFun] at a2 b2 ⊢
      refine ⟨⟨a1, b1⟩, ?_⟩
      rintro ⟨⟨⟩⟩ <;> simp +contextual [Shape.WF, and_assoc, and_left_comm, *]
    · intro h1
      have ⟨a1, a2⟩ := (go wf.1 wf'.1).2 h1
      simp only [WShapeFun.LE.def] at a1 a2; simp [WShapeFun] at a2
      exact ⟨⟨a1, wf.2.mono ((a2 _ a1).1 .rfl).1⟩, by rintro ⟨⟩ <;> simp +contextual [Shape.WF, *]⟩
    · rintro rfl H; constructor
      · have := H.and_mem.zipWith_l (f := Shape.join) (S := fun x y => x ≤ y ∧ y.WF)
          fun _ _ ⟨h1, h2⟩ =>
            have ⟨a1, a2⟩ := (@ih ⟨_, wf.1 _ h2.1⟩ ⟨_, wf'.1 _ h2.2⟩).2 h1
            ⟨((a2 ⟨_, a1⟩).1 .rfl).1, a1⟩
        refine ⟨fun _ h => ?_, fun hs => (wf.2 hs).mono <| this.imp fun _ _ => And.left⟩
        have ⟨_, h⟩ := this.forall_exists_r _ h; exact h.2.2
      · rintro ⟨⟩ <;> simp +contextual [Shape.WF, and_left_comm]; rintro wf₃ - -
        rename_i l l' _ l₃
        replace wf := wf.1; replace wf' := wf'.1
        induction l₃ generalizing l l' with cases H <;> simp | cons a₃ l₃ ihl
        have ⟨wf₁, wf₂⟩ := List.forall_mem_cons.1 wf
        have ⟨wf₁', wf₂'⟩ := List.forall_mem_cons.1 wf'
        have ⟨wf₁₃, wf₂₃⟩ := List.forall_mem_cons.1 wf₃
        rename_i h₃ H₃
        refine and_congr (((@ih ⟨_, wf₁⟩ ⟨_, wf₁'⟩).2 h₃).2 ⟨_, wf₁₃⟩)
          (ihl _ _ H₃ wf₂₃ wf₂ wf₂') |>.trans ?_
        simp [(· ≤ ·), and_comm, and_assoc, and_left_comm]

theorem WShape.Compat.iff {x y : WShape n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ?_, fun ⟨_, h1, h2⟩ => WShape.join_prop.1 _ h1 h2⟩
  have ⟨_, _, h2⟩ := WShape.join_prop.of_compat WShape.join_prop h
  exact ⟨_, (h2 _).1 .rfl⟩

theorem WShape.Compat.of_le {x : WShape n} (h : x ≤ y) : x.Compat y :=
  WShape.Compat.iff.2 ⟨_, h, .rfl⟩
theorem WShape.Compat.rfl {x : WShape n} : x.Compat x := .of_le .rfl
theorem WShape.Compat.symm {x : WShape n} : x.Compat y → y.Compat x := Shape.Compat.symm

def WShape.join (a b : WShape n) : WShape n :=
  if h : a.Compat b then ⟨a.1.join b.1, (WShape.join_prop.2 h).1⟩ else .bot
def WShape.Join (x y z : WShape n) : Prop :=
  ∀ w : WShape n, z ≤ w ↔ x ≤ w ∧ y ≤ w
theorem WShape.join_val {a b : WShape n} (h : a.Compat b) : (a.join b).1 = a.1.join b.1 := by
  simp [WShape.join, h]
theorem WShape.Join.le (H : WShape.Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl
theorem WShape.Join.mk (h : x.Compat y) : WShape.Join x y (x.join y) := by
  simp only [join, dif_pos h]; exact (WShape.join_prop.2 h).2

theorem WShape.Join.compat (H : WShape.Join x y z) : x.Compat y :=
  WShape.Compat.iff.2 ⟨z, (H _).1 .rfl⟩

theorem WShape.Join.iff {x y z : WShape n} :
    WShape.Join x y z ↔ x.Compat y ∧ x.join y ≤ z ∧ z ≤ x.join y := by
  refine ⟨fun h => ⟨Compat.iff.2 ⟨_, h.le⟩, ?_⟩, fun ⟨h1, h2, h3⟩ w => ?_⟩
  · exact ⟨((mk h.compat _).2 h.le), (h _).2 (mk h.compat).le⟩
  · exact ⟨fun h => (mk h1 _).1 (h2.trans h), fun h => h3.trans <| (mk h1 _).2 h⟩

theorem WShape.lift_join {x y : WShape n} (le : n ≤ m) :
    (x.join y).lift m = (x.lift m).join (y.lift m) := by
  simp [join]; split <;> rename_i h
  · rw [dif_pos ((WShape.Compat.lift le).2 h)]; ext1; simp [lift_val le, Shape.lift_join le]
  · rw [dif_neg (mt (WShape.Compat.lift le).1 h), lift_bot]

theorem WShapeFun.join_mem {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ z, z ∈ f ∧ x.join x' ≤ z.1 ∧ z.1 ≤ x.join x' := by
  simp only [WShape.LE.def, WShape.join_val hc, f.join_mem' hx hy hc]

@[simp] theorem WShape.bot_join {x : WShape n} : bot.join x = x := by
  ext1; rw [join_val Compat.bot_l, bot, Shape.bot_join]
@[simp] theorem WShape.join_bot {x : WShape n} : x.join bot = x := by
  ext1; rw [join_val Compat.bot_r, bot, Shape.join_bot]
@[simp] theorem WShape.sort_join_sort :
    join (.sort r : WShape n) (.sort r') = if r = r' then .sort r else .bot := by
  ext1; simp [join, WShape.Compat, sort, Shape.Compat.sort_sort]; split <;> rfl

/-
protected theorem Shape.WF.plift (x : WShape n) :
    WF (n := m) x.1.plift.1 ∧ ∀ y : Shape m, x.1.plift.2 = some y → y.WF := by
  induction m generalizing n with | zero => exact ⟨trivial, fun _ _ => trivial⟩ | succ m ih
  cases n with | zero => obtain ⟨⟨⟩⟩ := x <;> simp [WF, plift] | succ n
  specialize @ih n
  let rec go (x : WShapeFun n) :
      ShapeFun.WF (n := m) WF (ShapeFun.plift plift x.1).1 ∧
      ∀ y : ShapeFun m, (ShapeFun.plift plift x.1).2 = some y → ShapeFun.WF WF y := by
    obtain le | le := Nat.le_total n m
    · simp [ShapeFun.plift_eq_lift le, ShapeFun.WF.lift le x.2]
    simp [ShapeFun.plift, ShapeFun.WF, ShapeFun.WF', List.mapM_eq_some]
    -- have ⟨⟨⟨_, a1⟩, a2⟩, a3⟩ := x.2
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, fun _ h1 => ⟨⟨?_, ?_⟩, fun _ _ h2 => ?_⟩⟩
    · have ⟨_, h⟩ := x.2.1.1; exact ⟨_, _, _, h, _, by cases n <;> rfl, rfl, rfl⟩
    · intro _ _ _ _ h1 b₂ h2 rfl rfl _ _ _ _ h3 c₂ h4 rfl rfl; refine ⟨fun h => ?_, fun h => ?_⟩
      · replace ⟨b1, _, h1⟩ := x.mem_val' h1; replace ⟨c1, _, h3⟩ := x.mem_val' h3
        refine have hc := by exact Compat.plift.2 h2 h4 h
          have ⟨⟨d, d'⟩, d1, d2, d3⟩ := x.join_mem h1 h3 hc; ?_
        let b₂' : WShape _ := ⟨b₂, (ih ⟨_, b1⟩).2 _ h2⟩
        let c₂' : WShape _ := ⟨c₂, (ih ⟨_, c1⟩).2 _ h4⟩
        change b₂'.Compat c₂' at h
        have jeq : (b₂'.join c₂').1 = b₂.join c₂ := by simp [b₂', c₂', WShape.join_val h]
        have ⟨j1, j2⟩ := (WShape.Join.mk h).le
        simp [WShape.LE.def, b₂', c₂', jeq] at j1 j2
        have : d.1 ≤ ((b₂'.join c₂').lift n).1 := by
          refine d3.trans <| (WShape.Join.mk hc _).2 ⟨?_, ?_⟩ <;>
            simp [WShape.LE.def, WShape.lift_val le, jeq, ← plift_le le] <;> exact ⟨_, ‹_›, ‹_›⟩
        have ⟨d₂, e1, e2⟩ := (plift_le le).2 (jeq ▸ WShape.lift_val le ▸ this :)
        refine ⟨_, ⟨_, _, _, d1, _, e1, rfl, rfl⟩, jeq ▸ (?_ : _ ≤ d₂), e2⟩
        have ⟨j3, j4⟩ := (WShape.Join.mk hc _).1 d2
        have := (plift_le le).1 ⟨_, e1, .rfl⟩
        refine (WShape.Join.mk h ⟨d₂, (ih _).2 _ e1⟩).2 ⟨?_, ?_⟩
        · have ⟨_, f1, f2⟩ := (plift_le le).2 (j3.trans this); cases h2.symm.trans f1; exact f2
        · have ⟨_, f1, f2⟩ := (plift_le le).2 (j4.trans this); cases h4.symm.trans f1; exact f2
      · rename_i b b' c c'
        refine plift_mono <| x.mem_mono (x.mem_val h1) (x.mem_val h3) ?_
        sorry
    stop
    · intro _ _ _ _ h1 _ h2 rfl rfl; exact ⟨(ih (a3 _ h1).1).2 _ h2, (ih (a3 _ h1).2).1⟩
    · have ⟨_, b1, _, _, rfl⟩ := h1.forall_exists_l _ a1; exact ⟨_, by simpa using b1⟩
    · intro _ b₂ h2 _ c₂ h3
      obtain ⟨⟨b, b'⟩, b1, _, b2, ⟨⟩⟩ := h1.forall_exists_r _ h2
      obtain ⟨⟨c, c'⟩, c1, _, c2, ⟨⟩⟩ := h1.forall_exists_r _ h3; dsimp at *
      refine ⟨fun h => ?_, fun h => ?_⟩
      · sorry
      · sorry
    · obtain ⟨⟨b, b'⟩, b1, _, b2, ⟨⟩⟩ := h1.forall_exists_r _ h2
      exact ⟨(ih (a3 _ b1).1).1, (ih (a3 _ b1).2).2 _ b2⟩
  obtain ⟨x, wf⟩ := x
  cases x with simp [WF] at wf <;> simp [plift, WF, List.mapM_eq_some, *]
  | forallE =>
    refine ⟨⟨(ih ⟨_, wf.1⟩).1, (go ⟨_, wf.2⟩).1⟩, ?_⟩
    rintro _ _ h1 _ h2 rfl; exact ⟨(ih ⟨_, wf.1⟩).2 _ h1, (go ⟨_, wf.2⟩).2 _ h2⟩
  | lam => exact ⟨⟨(go ⟨_, wf.1⟩).1, sorry⟩, fun _ h1 => ⟨(go ⟨_, wf.1⟩).2 _ h1, sorry⟩⟩
  | ctor =>
    refine ⟨⟨fun _ h1 => (ih ⟨_, wf.1 _ h1⟩).1, sorry⟩, fun _ h1 => ⟨fun _ h2 => ?_, sorry⟩⟩
    have ⟨_, h3, h4⟩ := h1.forall_exists_r _ h2; exact (ih ⟨_, wf.1 _ h3⟩).2 _ h4

-- theorem ShapeFun.WF'.plift (h : WF (n := n) Shape.WF x) :
--     WF (n := m) Shape.WF (plift Shape.plift x).1 ∧
--     ∀ y : ShapeFun m, (plift Shape.plift x).2 = some y → WF Shape.WF y := by
--   sorry

-- theorem Shape.WF.plift (h : WF (n := n) x) : WF (n := m) x.plift.1 := sorry
-- theorem ShapeFun.WF.plift (h : WF (n := n) Shape.WF x) :
--     WF (n := m) Shape.WF (plift Shape.plift x).1 := sorry
-/

theorem WShape.Join.lift {x y z : WShape n} (le : n ≤ m) :
    (x.lift m).Join (y.lift m) (z.lift m) ↔ x.Join y z := by
  constructor
  · intro hJ w
    have := hJ (w.lift m)
    rwa [lift_le_lift le, lift_le_lift le, lift_le_lift le] at this
  · intro hJ; have ⟨h1, h2, h3⟩ := Join.iff.1 hJ
    refine Join.iff.2 ⟨(Compat.lift le).2 h1, ?_⟩
    exact lift_join le ▸ ⟨WShape.lift_mono le h2, WShape.lift_mono le h3⟩

theorem WShape.join_self {x y : WShape n} : WShape.Join x x y ↔ x ≤ y ∧ y ≤ x :=
  ⟨fun H => ⟨((H _).1 .rfl).1, (H _).2 ⟨.rfl, .rfl⟩⟩,
   fun ⟨H1, H2⟩ _ => ⟨fun h => ⟨H1.trans h, H1.trans h⟩, fun h => H2.trans h.1⟩⟩

theorem WShape.Join.left {x y : WShape n} (h : y ≤ x) : WShape.Join x y x :=
  fun _ => ⟨fun H => ⟨H, h.trans H⟩, (·.1)⟩

theorem WShape.Join.right {x y : WShape n} (h : y ≤ x) : WShape.Join y x x :=
  fun _ => ⟨fun H => ⟨h.trans H, H⟩, (·.2)⟩

def WShapeFun.Join (x y z : WShapeFun n) : Prop := ∀ w : WShapeFun n, z ≤ w ↔ x ≤ w ∧ y ≤ w

theorem WShapeFun.Join.le (H : WShapeFun.Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl

def WShapeFun.join (x y : WShapeFun n) : WShapeFun n :=
  if h : x.Compat y then
    ⟨ShapeFun.join Shape.join x.1 y.1, ((WShape.join_prop.ih_fun WShape.join_prop).2 h).1⟩
  else .bot

theorem WShapeFun.join_val {x y : WShapeFun n} (H : Compat x y) :
    (x.join y).1 = x.1.join Shape.join y.1 := by simp [join, dif_pos H]

@[simp] theorem WShape.forallE_join_forallE {a a' : WShape n} {f f' : WShapeFun n}
    (hc1 : a.Compat a') (hc2 : WShapeFun.Compat f f') :
    (WShape.forallE a f).join (.forallE a' f') = .forallE (a.join a') (f.join f') := by
  have hc := Compat.forallE_forallE.2 ⟨hc1, hc2⟩
  ext1; rw [join_val hc]; simp [forallE, Shape.join, join_val hc1, WShapeFun.join_val hc2]

@[simp] theorem WShape.indTy_join_indTy {r r' : Bool}
    (hc : (WShape.indTy r : WShape (n+1)).Compat (.indTy r')) :
    (WShape.indTy r : WShape (n+1)).join (.indTy r') = .indTy r := by
  have hrr : r = r' := by simpa [Compat, indTy, Shape.Compat] using hc
  subst hrr; ext1; rw [join_val hc]; simp [indTy, Shape.join]

theorem WShapeFun.Join.mk (H : WShapeFun.Compat x y) : WShapeFun.Join x y (x.join y) := by
  simp [Join, WShapeFun.LE.def, join_val H]
  have ⟨_, h⟩ := (WShape.join_prop.ih_fun WShape.join_prop).2 H; exact h

theorem WShapeFun.Compat.iff {x y : WShapeFun n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ⟨_, (Join.mk h).le⟩, fun ⟨_, h1, h2⟩ => ?_⟩
  exact (WShape.join_prop.ih_fun WShape.join_prop).1 _ h1 h2

@[simp] theorem WShapeFun.Compat.bot_l {s : WShapeFun n} : bot.Compat s := iff.2 ⟨_, bot_le, .rfl⟩
@[simp] theorem WShapeFun.Compat.bot_r {s : WShapeFun n} : s.Compat bot := iff.2 ⟨_, .rfl, bot_le⟩

theorem WShapeFun.Join.compat (H : Join x y z) : x.Compat y := Compat.iff.2 ⟨z, (H _).1 .rfl⟩

theorem WShapeFun.Join.iff :
    Join x y z ↔ x.Compat y ∧ x.join y ≤ z ∧ z ≤ x.join y := by
  refine ⟨fun h => ⟨Compat.iff.2 ⟨_, h.le⟩, ?_⟩, fun ⟨h1, h2, h3⟩ w => ?_⟩
  · exact ⟨((mk h.compat _).2 h.le), (h _).2 (mk h.compat).le⟩
  · exact ⟨fun h => (mk h1 _).1 (h2.trans h), fun h => h3.trans <| (mk h1 _).2 h⟩

theorem WShapeFun.join_mem'' {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') : ∃ z, z ∈ f ∧ x.Join x' z.1 := by
  have ⟨⟨z, w⟩, h1, h2⟩ := f.join_mem' hx hy hc
  refine ⟨_, h1, WShape.Join.iff.2 ⟨hc, ?_⟩⟩
  simpa only [WShape.LE.def, WShape.join_val hc]

def WShapeFun.ofElems (f : List (WShape n × WShape n))
    (h1 : ∃ y, (WShape.bot, y) ∈ f)
    (h2 : ∀ x ∈ f, ∀ y ∈ f,
      (x.1.Compat y.1 → ∃ z ∈ f, x.1.Join y.1 z.1) ∧
      (x.1 ≤ y.1 → x.2 ≤ y.2)) : WShapeFun n := by
  refine ⟨f.map fun x => (x.1.1, x.2.1), ?_, ?_⟩
  · simp only [List.mem_map, Prod.mk.injEq]
    have ⟨_, h1⟩ := h1; refine ⟨⟨_, _, h1, rfl, rfl⟩, ?_⟩
    rintro _ ⟨⟨x, y⟩, a1, rfl⟩ ⟨x', y'⟩ ⟨⟨u, v⟩, a2, ⟨⟩⟩; dsimp
    have ⟨b1, b2⟩ := h2 _ a1 _ a2; refine ⟨fun hc => ?_, b2⟩
    have ⟨_, c1, c2⟩ := b1 hc; have := (WShape.Join.iff.1 c2).2
    simp only [WShape.LE.def, WShape.join_val hc] at this
    exact ⟨_, ⟨⟨_, _⟩, c1, rfl⟩, this⟩
  · simp; rintro _ _ x y _ rfl rfl; exact ⟨x.2, y.2⟩

theorem WShapeFun.mem_ofElems {f : List (WShape n × WShape n)} {h1 h2} :
    (x, y) ∈ WShapeFun.ofElems f h1 h2 ↔ (x, y) ∈ f := by
  show (x.1, y.1) ∈ f.map (fun p => (p.1.1, p.2.1)) ↔ _
  simp only [List.mem_map, Prod.mk.injEq]
  exact ⟨fun ⟨⟨a, b⟩, h, ha, hb⟩ => by cases WShape.ext ha; cases WShape.ext hb; exact h,
    fun h => ⟨_, h, rfl, rfl⟩⟩

@[implicit_reducible] def TShape := Σ n, WShape n
abbrev WShape.T : WShape n → TShape := Sigma.mk _

def TShape.LE (a b : TShape) : Prop := a.2.lift (max a.1 b.1) ≤ b.2.lift _
instance : _root_.LE TShape := ⟨TShape.LE⟩
theorem TShape.LE.def' {a b : TShape} : a ≤ b ↔ a.2.lift (max a.1 b.1) ≤ b.2.lift _ := .rfl

def TShapeFun.LE (a : WShapeFun n) (b : WShapeFun m) : Prop :=
  a.lift (max n m) ≤ b.lift _

theorem TShape.LE.def {a b : TShape} (h1 : a.1 ≤ m) (h2 : b.1 ≤ m) :
    a ≤ b ↔ a.2.lift m ≤ b.2.lift m := by
  refine (WShape.lift_le_lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShapeFun.LE.def {a : WShapeFun n} {b : WShapeFun m} (h1 : n ≤ k) (h2 : m ≤ k) :
    TShapeFun.LE a b ↔ a.lift k ≤ b.lift k := by
  refine (WShapeFun.lift_le_lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShapeFun.lift_lift (.inl (Nat.le_max_left ..)),
    WShapeFun.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShape.LE.forallE_decomp {b : WShape n} {f : WShapeFun n} {b' : WShape n'} {f' : WShapeFun n'}
    (le : (WShape.forallE b f).T ≤ (WShape.forallE b' f').T) :
    b.lift (max n n') ≤ b'.lift (max n n') ∧
      f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have h := (TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 le
  have h_raw : ((WShape.forallE b f).lift _).1 ≤ ((WShape.forallE b' f').lift _).1 := h
  rw [WShape.lift_val (Nat.succ_le_succ le₁), WShape.lift_val (Nat.succ_le_succ le₂)] at h_raw
  simp only [WShape.forallE, Shape.lift, Shape.LE.def] at h_raw
  constructor
  · show (b.lift _).1 ≤ (b'.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact h_raw.1
  · show (f.lift _).1.LE (f'.lift _).1
    rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact h_raw.2

theorem TShape.LE.lam'_decomp {f : WShapeFun n} {f' : WShapeFun n'} :
    (WShape.lam' f).T ≤ (WShape.lam' f').T →
    f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have le₁' := Nat.succ_le_succ le₁; have le₂' := Nat.succ_le_succ le₂
  rw [TShape.LE.def le₁' le₂', WShape.LE.def, WShape.lift_val le₁', WShape.lift_val le₂',
    WShape.lam', WShape.lam']
  dsimp; split <;> rename_i hf
  · split <;> rename_i hf' <;>
      simp [WShape.lam, Shape.lift, WShapeFun.LE.def, WShapeFun.lift_val, le₁, le₂]
    intro h; cases Shape.le_bot.1 h
  · rintro -
    refine WShapeFun.LE.def'.2 fun x y h => ?_
    obtain ⟨_, _, h1, ⟨⟩, ⟨⟩⟩ := (WShapeFun.mem_lift le₁).1 h
    have := WShape.le_bot.1 <| Decidable.by_contra fun h => hf ⟨_, h1, h⟩
    dsimp at this; cases this
    have ⟨_, h⟩ := f'.bot_mem
    exact ⟨_, _, (WShapeFun.mem_lift le₂).2 ⟨_, _, h, rfl, rfl⟩, by simp⟩

theorem TShape.LE.le_lam {f : WShapeFun n} {hl} {f' : WShapeFun n'} {hl'}
    (le : (WShape.lam f hl).T ≤ (WShape.lam f' hl').T) :
    f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have h := (TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 le
  have h_raw : ((WShape.lam f hl).lift _).1 ≤ ((WShape.lam f' hl').lift _).1 := h
  rw [WShape.lift_val (Nat.succ_le_succ le₁), WShape.lift_val (Nat.succ_le_succ le₂)] at h_raw
  simp only [WShape.lam, Shape.lift, Shape.LE.def] at h_raw
  show (f.lift _).1.LE (f'.lift _).1
  rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact h_raw

def TShape.bot : TShape := WShape.T (n := 0) .bot
def TShape.sort (r : Bool) : TShape := WShape.T (n := 0) (.sort r)
def TShape.type : TShape := .sort true

nonrec theorem TShape.LE.rfl {a : TShape} : a ≤ a := WShape.LE.rfl

theorem TShape.LE.trans {a b c : TShape} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  let k := max (max a.1 b.1) c.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  exact (LE.def hk.1.1 hk.2).2 (.trans ((LE.def hk.1.1 hk.1.2).1 h1) ((LE.def hk.1.2 hk.2).1 h2))

theorem TShape.LE.lift_l {a b : TShape} (h1 : a.1 ≤ b.1) : a ≤ b ↔ a.2.lift (b.1) ≤ b.2 :=
  (LE.def h1 (Nat.le_refl _)).trans (WShape.lift_self ▸ .rfl)
theorem TShape.LE.lift_r {a b : TShape} (h1 : b.1 ≤ a.1) : a ≤ b ↔ a.2 ≤ b.2.lift (a.1) :=
  (LE.def (Nat.le_refl _) h1).trans (WShape.lift_self ▸ .rfl)
theorem WShape.LE.T_iff {a b : WShape n} : a.T ≤ b.T ↔ a ≤ b :=
  (TShape.LE.lift_l (Nat.le_refl _) (a := a.T) (b := b.T)).trans (WShape.lift_self ▸ .rfl)
theorem WShape.LE.T {a b : WShape n} : a ≤ b → a.T ≤ b.T := T_iff.2
theorem WShape.LE.of_T {a b : WShape n} : a.T ≤ b.T → a ≤ b := T_iff.1

theorem TShape.bot_eqv : (WShape.bot (n := n)).T ≤ bot ∧ bot ≤ (WShape.bot (n := n)).T := by
  simp [TShape.LE.def', bot, WShape.lift_bot]

theorem TShape.bot_le' : (WShape.bot (n := n)).T ≤ a := by
  simp [TShape.LE.def', WShape.lift_bot]

theorem TShape.bot_le {a : TShape} : bot ≤ a := bot_le'

theorem TShape.le_bot {a : TShape} : a ≤ bot ↔ a.2 = .bot := by
  simp [TShape.LE.def', bot, WShape.lift_le_bot (Nat.le_max_left ..), WShape.lift_bot]

theorem TShape.le_bot' {a : TShape} : a ≤ bot ↔ a = WShape.T (n := a.1) .bot := by
  rw [le_bot]; let ⟨n, s⟩ := a
  exact ⟨fun h => congrArg (Sigma.mk n) h, fun h => Sigma.mk.inj h |>.2 |> eq_of_heq⟩

theorem TShape.lift_eqv {a : TShape} (h : a.1 ≤ m) :
    (a.2.lift m).T ≤ a ∧ a ≤ (a.2.lift m).T := by
  simp [TShape.LE.def', WShape.lift_lift (.inl h), WShape.LE.rfl]

theorem TShape.sort_eqv :
    (WShape.sort (n := n) r).T ≤ .sort r ∧ .sort r ≤ (WShape.sort (n := n) r).T := by
  simp [sort, TShape.LE.def', WShape.lift_sort, WShape.LE.rfl]

theorem TShape.sort_not_le_lam' {f : WShapeFun n'} :
    ¬(.sort r : WShape n).T ≤ (WShape.lam' f).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.lam'] at h; split at h <;>
  · simp only [WShape.lam, WShape.bot, WShape.lift_val (Nat.le_max_right ..)] at h
    have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
    rw [hk] at h; simp [Shape.sort, Shape.lift, Shape.bot] at h

theorem TShape.forallE_not_le_lam' {a : WShape n} {f₁ : WShapeFun n} {f₂ : WShapeFun n'} :
    ¬(.forallE a f₁ : WShape (n+1)).T ≤ (WShape.lam' f₂).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_forallE le₁, WShape.lift_lam' le₂]
  intro hle; have ⟨_, _, _, _, hle⟩ := WShape.forallE_le.1 hle
  unfold WShape.lam' at hle; split at hle <;>
    simp [WShape.ext_iff, WShape.forallE, WShape.lam] at hle
  cases hle

theorem TShape.ctor_not_le_lam' {c : Name} {l : List (WShape n)} {h} {f : WShapeFun n'} :
    ¬(WShape.ctor c l h : WShape (n+1)).T ≤ (WShape.lam' f).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_ctor le₁, WShape.lift_lam' le₂]
  intro hle
  unfold WShape.lam' at hle; split at hle <;>
    simp_all [WShape.LE.def, WShape.ctor, WShape.lam, WShape.bot, Shape.LE.def]

theorem TShape.indTy_not_le_lam' {f : WShapeFun n'} :
    ¬(WShape.indTy r : WShape (n+1)).T ≤ (WShape.lam' f).T := by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)), WShape.lift_indTy,
    WShape.lift_lam' (Nat.le_max_right ..), WShape.indTy_le]
  unfold WShape.lam'; split <;> rintro ⟨⟩

theorem TShape.lam_not_le_forallE {f₁ : WShapeFun n} {hl} {a' : WShape n'} {f' : WShapeFun n'} :
    ¬(.lam f₁ hl : WShape (n+1)).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_lam le₁, WShape.lift_forallE le₂]
  simp [(· ≤ ·), Shape.LE, Shape.ble, WShape.lam, WShape.forallE]

theorem TShape.sort_not_le_forallE {a' : WShape n'} {f' : WShapeFun n'} :
    ¬(.sort r : WShape n).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.forallE, WShape.lift_val (Nat.le_max_right ..)] at h
  have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
  rw [hk] at h; simp [Shape.sort, Shape.lift] at h

theorem TShape.sort_not_le_ctor' {c : Name} {l : List (WShape n')} :
    ¬(.sort r : WShape n).T ≤ (WShape.ctor' c l).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.ctor', WShape.lift_val (Nat.le_max_right ..)] at h
  split at h
  · simp only [WShape.ctor] at h
    have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
    rw [hk] at h; simp [Shape.sort, Shape.lift] at h
  · simp only [WShape.bot] at h
    have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
    rw [hk] at h; simp [Shape.sort, Shape.lift, Shape.bot] at h

theorem TShape.forallE_not_le_ctor' {a : WShape n} {f : WShapeFun n}
    {c : Name} {l : List (WShape n')} :
    ¬(.forallE a f : WShape (n+1)).T ≤ (WShape.ctor' c l).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_forallE le₁, WShape.lift_ctor' le₂]
  intro hle; have ⟨_, _, _, _, hle⟩ := WShape.forallE_le.1 hle
  unfold WShape.ctor' at hle; split at hle
  · simp [WShape.ext_iff, WShape.forallE, WShape.ctor] at hle
  · have := congrArg (·.1) hle
    simp only [WShape.forallE, WShape.bot, Shape.bot] at this
    cases this

theorem TShape.lam_not_le_ctor' {f : WShapeFun n} {hl}
    {c : Name} {l : List (WShape n')} :
    ¬(.lam f hl : WShape (n+1)).T ≤ (WShape.ctor' c l).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_lam le₁, WShape.lift_ctor' le₂]
  unfold WShape.ctor'; split <;>
    simp [(· ≤ ·), Shape.LE, Shape.ble, WShape.lam, WShape.ctor, WShape.bot]

theorem TShape.indTy_not_le_forallE {a' : WShape n'} {f' : WShapeFun n'} :
    ¬(WShape.indTy r : WShape (n+1)).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)),
    WShape.lift_indTy, WShape.lift_forallE (Nat.le_max_right ..), WShape.indTy_le]
  rintro ⟨⟩

theorem TShape.indTy_not_le_sort :
    ¬(WShape.indTy r : WShape (n+1)).T ≤ (.sort r : WShape n').T := by
  intro h
  have := h.trans TShape.sort_eqv.1
  rw [TShape.LE.def (Nat.le_refl _) (Nat.zero_le _), WShape.lift_self, WShape.indTy_le] at this
  cases this

theorem WShape.Compat_lift_val {a : WShape n₁} {b : WShape n₂}
    (le₁ : n₁ ≤ m) (le₂ : n₂ ≤ m) :
    (a.lift m).Compat (b.lift m) ↔ (a.1.lift m).Compat (b.1.lift m) := by
  show (a.lift m).1.Compat (b.lift m).1 ↔ _
  rw [lift_val le₁, lift_val le₂]

def TShape.Compat (x y : TShape) : Prop := (x.2.lift (max x.1 y.1)).Compat (y.2.lift _)

theorem TShape.Compat.def {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    x.Compat y ↔ (x.2.lift m).Compat (y.2.lift _) := by
  refine (WShape.Compat.lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.Compat.T_iff {x y : WShape n} : x.Compat y ↔ x.T.Compat y.T := by
  refine .trans ?_ (TShape.Compat.def (x := x.T) (y := y.T) (Nat.le_refl _) (Nat.le_refl _)).symm
  rw [WShape.lift_self, WShape.lift_self]

theorem WShape.Compat.T {x y : WShape n} : x.Compat y → x.T.Compat y.T := T_iff.1

theorem TShape.Compat.def' {x y : TShape} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ?_, fun ⟨z, h1, h2⟩ => ?_⟩
  · have ⟨z, h1, h2⟩ := WShape.Compat.iff.1 h
    exact ⟨z.T, (LE.lift_l (Nat.le_max_left ..)).2 h1, (LE.lift_l (Nat.le_max_right ..)).2 h2⟩
  · let k := max x.1 (max y.1 z.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
    exact (TShape.Compat.def hk.1 hk.2.1).2 <|
      WShape.Compat.iff.2 ⟨z.2.lift k, (LE.def hk.1 hk.2.2).1 h1, (LE.def hk.2.1 hk.2.2).1 h2⟩

theorem TShape.Compat.bot_l : TShape.bot.Compat x :=
  TShape.Compat.def'.2 ⟨x, TShape.bot_le, .rfl⟩

theorem TShape.Compat.bot_r : Compat x TShape.bot :=
  TShape.Compat.def'.2 ⟨x, .rfl, TShape.bot_le⟩

theorem TShape.Compat.bot_l' : (WShape.bot (n := n)).T.Compat x :=
  TShape.Compat.def'.2 ⟨x, TShape.bot_le', .rfl⟩

theorem TShape.Compat.bot_r' : Compat x (WShape.bot (n := n)).T :=
  TShape.Compat.def'.2 ⟨x, .rfl, TShape.bot_le'⟩

theorem NonZero.not_iff {f : WShapeFun n} : ¬f.NonZero ↔ f ≤ .bot := by
  simp only [WShapeFun.NonZero, ShapeFun.NonZero, Prod.exists, not_exists, not_and,
    Decidable.not_not, WShapeFun.bot, ShapeFun.bot, WShapeFun.LE.def, ShapeFun.LE.def,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, and_assoc, exists_and_left,
    exists_eq_left, Shape.bot_le, true_and]

theorem NonZero.iff {f : WShapeFun n} : f.NonZero ↔ ¬f ≤ .bot :=
  (Decidable.not_iff_comm.1 NonZero.not_iff).symm

theorem WShapeFun.NonZero.join {f f' : WShapeFun n} (h : f.Compat f') :
    (f.join f').NonZero ↔ f.NonZero ∨ f'.NonZero := by
  refine ⟨fun hjoin => ?_, ?_⟩
  · by_cases h1 : f.NonZero <;> [exact .inl h1; skip]
    by_cases h2 : f'.NonZero <;> [exact .inr h2; skip]
    refine (SExpr.NonZero.iff.1 hjoin ?_).elim
    exact (WShapeFun.Join.mk h _).2 ⟨SExpr.NonZero.not_iff.1 h1, SExpr.NonZero.not_iff.1 h2⟩
  · rintro (h1 | h1) <;> refine SExpr.NonZero.iff.2 fun hbot => SExpr.NonZero.iff.1 h1 ?_
    · exact ((WShapeFun.Join.mk h _).1 hbot).1
    · exact ((WShapeFun.Join.mk h _).1 hbot).2

theorem WShape.Compat.mono {x y x' y' : WShape n}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y :=
  have ⟨_, a1, a2⟩ := WShape.Compat.iff.1 H
  WShape.Compat.iff.2 ⟨_, h1.trans a1, h2.trans a2⟩

theorem WShapeFun.Compat.mono {x y x' y' : WShapeFun n}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y :=
  have ⟨_, a1, a2⟩ := WShapeFun.Compat.iff.1 H
  WShapeFun.Compat.iff.2 ⟨_, h1.trans a1, h2.trans a2⟩

theorem TShape.Compat.mono {x y x' y' : TShape}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y := by
  let k := max (max x.1 y.1) (max x'.1 y'.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.LE.def hk.1.1 hk.2.1).1 h1
  have h2 := (TShape.LE.def hk.1.2 hk.2.2).1 h2
  have H := (TShape.Compat.def hk.2.1 hk.2.2).1 H
  exact (TShape.Compat.def hk.1.1 hk.1.2).2 <| H.mono h1 h2

theorem WShape.Compat.lam' {a b : WShapeFun n} : Compat (.lam' a) (.lam' b) ↔ a.Compat b := by
  rw [WShape.lam']; split <;> rename_i h1
  · rw [WShape.lam']; split <;> [rfl; rename_i h2]
    simp; exact .mono .rfl (NonZero.not_iff.1 h2) .bot_r
  · simp; exact .mono (NonZero.not_iff.1 h1) .rfl .bot_l

theorem WShape.Join.lam' {a b c : WShapeFun n} :
    Join (.lam' a) (.lam' b) (.lam' c) ↔ a.Join b c := by
  refine ⟨fun H z => by simpa [lam'_le_lam'] using H (.lam' z), fun H z => ?_⟩
  by_cases hz : ∃ z', .lam' z' = z
  · obtain ⟨z', rfl⟩ := hz; simp only [lam'_le_lam', H _]
  have {x} : WShape.lam' x ≤ z ↔ x ≤ .bot := by
    unfold WShape.lam'; split <;> rename_i h
    · simp [← NonZero.not_iff, h, WShape.LE.def, lam, Shape.lam_le]
      obtain ⟨_, wf⟩ := z; rintro _ h1 ⟨⟩; refine hz ⟨⟨_, wf.1⟩, ?_⟩
      rw [WShape.lam', dif_pos (by exact wf.2)]; rfl
    · simp [NonZero.not_iff.1 h]
  simp only [this, H _]

theorem WShape.ctor'_join {l l' : List (WShape n)} {c : Name}
    (h : List.Forall₂ Compat l l') :
    (WShape.ctor' c l).join (WShape.ctor' c l') = WShape.ctor' c (l.zipWith join l') := by
  have key : (IsStruct c = true → ListNonZero (l.zipWith join l')) ↔
      (IsStruct c = true → ListNonZero l) ∨ (IsStruct c = true → ListNonZero l') := by
    suffices ListNonZero (l.zipWith join l') ↔ ListNonZero l ∨ ListNonZero l' by
      rw [this]
      by_cases hIs : IsStruct c <;> simp [hIs]
    induction h with | nil => simp [ListNonZero] | @cons x y L L' hh _ ih
    have hcompat_join : ¬(x.join y).1 ≤ .bot ↔ ¬x.1 ≤ .bot ∨ ¬y.1 ≤ .bot := by
      have hJ := WShape.Join.mk hh .bot
      simp only [WShape.LE.def, WShape.bot] at hJ
      rw [hJ]
      by_cases hx : x.1 ≤ .bot <;> by_cases hy : y.1 ≤ .bot <;> simp [hx, hy]
    simp only [List.zipWith, ListNonZero, List.mem_cons]
    constructor
    · rintro ⟨z, (rfl | hzL), hznz⟩
      · rcases hcompat_join.mp hznz with hh | hh
        · exact .inl ⟨x, .inl rfl, hh⟩
        · exact .inr ⟨y, .inl rfl, hh⟩
      · rcases ih.mp ⟨z, hzL, hznz⟩ with ⟨z', hz'L, hz'nz⟩ | ⟨z', hz'L, hz'nz⟩
        · exact .inl ⟨z', .inr hz'L, hz'nz⟩
        · exact .inr ⟨z', .inr hz'L, hz'nz⟩
    · rintro (⟨z, (rfl | hzL), hznz⟩ | ⟨z, (rfl | hzL), hznz⟩)
      · exact ⟨_, .inl rfl, hcompat_join.mpr (.inl hznz)⟩
      · obtain ⟨w, hwL, hwnz⟩ := ih.mpr (.inl ⟨z, hzL, hznz⟩)
        exact ⟨w, .inr hwL, hwnz⟩
      · exact ⟨_, .inl rfl, hcompat_join.mpr (.inr hznz)⟩
      · obtain ⟨w, hwL, hwnz⟩ := ih.mpr (.inr ⟨z, hzL, hznz⟩)
        exact ⟨w, .inr hwL, hwnz⟩
  ext1; rw [join_val (Compat.ctor'_ctor' h)]
  unfold WShape.ctor'; split <;> rename_i h1 <;> split <;> rename_i h2
  · rw [dif_pos (key.mpr (.inl h1))]; simp [ctor, Shape.join]
    congr 1; clear h1 h2 key
    induction h with
    | nil => rfl
    | @cons x y L L' hh _ ih => simp [WShape.join_val hh, ih]
  · rw [dif_pos (key.mpr (.inl h1))]; simp [ctor, bot, Shape.join_bot]
    have h2' : ∀ x ∈ l', x.1 ≤ Shape.bot := by simpa [ListNonZero] using fun hNZ => h2 fun _ => hNZ
    congr 1; clear h1 h2 key
    induction h with | nil => rfl | @cons x y L L' hh _ ih
    have hy_bot : y.1 = .bot := Shape.le_bot.1 (h2' y (.head _))
    simp [WShape.join_val hh, hy_bot, Shape.join_bot]
    exact ih (fun z hz => h2' z (.tail _ hz))
  · rw [dif_pos (key.mpr (.inr h2))]; simp [ctor, bot, Shape.bot_join]
    have h1' : ∀ x ∈ l, x.1 ≤ Shape.bot := by
      have ⟨_, hNZ⟩ := Decidable.not_imp_iff_and_not.1 h1
      simp [ListNonZero] at hNZ; exact hNZ
    congr 1; clear h1 h2 key
    induction h with | nil => rfl | @cons x y L L' hh _ ih
    have hx_bot : x.1 = .bot := Shape.le_bot.1 (h1' x (.head _))
    simp [WShape.join_val hh, hx_bot, Shape.bot_join]
    exact ih fun z hz => h1' z (.tail _ hz)
  · rw [dif_neg fun hh => (key.mp hh).elim h1 h2]; rfl

theorem WShape.ctor_le :
    WShape.ctor c l h ≤ s ↔ ∃ l' h', s = WShape.ctor c l' h' ∧ l.Forall₂ (· ≤ ·) l' := by
  simp [ctor, WShape.LE.def, WShape.ext_iff]
  cases s using WShape.casesOn' <;>
    simp [bot, sort, forallE, lam, ctor, indTy, Shape.bot, Shape.sort, Shape.LE.def]
  rename_i l₁ wf; refine ⟨fun ⟨rfl, h2⟩ => ⟨_, rfl, wf, h2⟩, fun ⟨_, h1, _, h3⟩ => ?_⟩
  injection h1 with eq1 eq2
  rw [← List.forall₂_map_right_iff, eq2, List.forall₂_map_right_iff]
  exact ⟨eq1.symm, h3⟩

theorem WShape.ctor'_le : WShape.ctor' c l ≤ s ↔
    ((IsStruct c → ListNonZero l) → ∃ l' h', s = WShape.ctor c l' h' ∧ l.Forall₂ (· ≤ ·) l') := by
  unfold ctor'; split <;> rename_i h1 <;> simp [eq_true h1, h1, WShape.ctor_le]

theorem WShape.ctor'_le_ctor' (h : List.Forall₂ (· ≤ ·) l l') :
    WShape.ctor' c l ≤ WShape.ctor' c l' := by
  unfold ctor'
  split <;> rename_i h1 <;> [skip; exact WShape.bot_le]
  rw [dif_pos (WShape.ListNonZero.mono h ∘ h1)]
  exact Shape.LE.def.2 ⟨rfl, by simpa⟩

theorem TShape.ctor_not_le_forallE :
    ¬(WShape.ctor c l h : WShape (n+1)).T ≤ (.forallE a' f' : WShape (n'+1)).T := fun h => by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)), WShape.lift_ctor (Nat.le_max_left ..),
    WShape.lift_forallE (Nat.le_max_right ..), WShape.ctor_le] at h; obtain ⟨_, _, ⟨⟩, _⟩ := h

theorem WShape.le_zipWith_join (hc : List.Forall₂ WShape.Compat l l') :
    l.Forall₂ (· ≤ ·) (l.zipWith WShape.join l') ∧
    l'.Forall₂ (· ≤ ·) (l.zipWith WShape.join l') := by
  induction hc with | nil => exact ⟨.nil, .nil⟩ | cons h _ ih
  have h := (WShape.Join.mk h).le; exact ⟨.cons h.1 ih.1, .cons h.2 ih.2⟩

def TShape.join (x y : TShape) : TShape := ⟨max x.1 y.1, (x.2.lift _).join (y.2.lift _)⟩

theorem TShape.lift_join {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    (x.join y).2.lift m = (x.2.lift m).join (y.2.lift m) := by
  simp [join, WShape.lift_join (Nat.max_le.2 ⟨h1, h2⟩), WShape.lift_lift (.inl (Nat.le_max_left ..)),
    WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.T_join {a b : WShape n} : a.T.join b.T = (a.join b).T := by
  rw [TShape.join, Nat.max_self n]; simp [lift_self]

def TShape.Join (x y z : TShape) := ∀ w, z ≤ w ↔ x ≤ w ∧ y ≤ w

theorem TShape.Join.le (H : Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl

theorem TShape.Join.def (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) (h3 : z.1 ≤ m) :
    Join x y z ↔ WShape.Join (x.2.lift m) (y.2.lift m) (z.2.lift m) := by
  constructor <;> intro hJ w
  · have hle : m ≤ m := Nat.le_refl m
    have := hJ (⟨m, w⟩ : TShape)
    rwa [TShape.LE.def h3 hle, TShape.LE.def h1 hle, TShape.LE.def h2 hle, WShape.lift_self] at this
  · let k := max m w.1
    have hk : m ≤ k := Nat.le_max_left ..
    have hwk : w.1 ≤ k := Nat.le_max_right ..
    rw [TShape.LE.def (Nat.le_trans h3 hk) hwk, TShape.LE.def (Nat.le_trans h1 hk) hwk,
      TShape.LE.def (Nat.le_trans h2 hk) hwk, ← WShape.lift_lift (.inl h3),
      ← WShape.lift_lift (.inl h1), ← WShape.lift_lift (.inl h2)]
    exact (WShape.Join.lift hk |>.2 hJ) _

theorem WShape.Join.T_iff {x y z : WShape n} : WShape.Join x y z ↔ TShape.Join x.T y.T z.T := by
  refine .symm <| (TShape.Join.def (x := x.T) (y := y.T) (z := z.T)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).trans ?_
  rw [WShape.lift_self, WShape.lift_self, WShape.lift_self]

theorem WShape.Join.T {x y z : WShape n} : Join x y z → TShape.Join x.T y.T z.T := T_iff.1

theorem TShape.Join.mk (H : x.Compat y) : Join x y (x.join y) := by
  let m := max x.1 y.1; have ⟨hx, hy⟩ := Nat.max_le.1 (Nat.le_refl m)
  rw [TShape.Join.def hx hy (Nat.le_refl _), TShape.lift_join hx hy]
  exact .mk ((TShape.Compat.def hx hy).1 H)

theorem ShapeFun.WF.bot_le (wf : WF Shape.WF f) : ShapeFun.bot.LE f := by
  simp [ShapeFun.LE.def, bot]
  exact ⟨.bot, wf.1.1, Shape.bot_le⟩

theorem Shape.WF.lam_non_bot (wf : WF (n := n+1) (.lam f)) : ∃ x y, (x, y) ∈ f ∧ y ≠ .bot :=
  have ⟨⟨_, _⟩, h1, h2⟩ := wf.2; ⟨_, _, h1, mt Shape.le_bot.2 h2⟩

omit [Params] in
theorem ShapeFun.app_core (f : ShapeFun n) (x) :
    f.app x = .bot ∨ ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f ∧ ∀ y ∈ f, y.1 ≤ x → y.1 ≤ x' := by
  refine let P := _; let f' := f.trunc x; (?_ :
    let y' := ((f'.find? P).getD (.bot, .bot)).2
    y' = .bot ∨ ∃ x', x' ≤ x ∧ (x', y') ∈ f ∧ ∀ y ∈ f, y.1 ≤ x → y.1 ≤ x')
  cases h : f'.find? P <;> simp
  have := List.find?_some h; simp [P, mem_trunc] at this ⊢
  have ⟨h1, h2⟩ := mem_trunc.1 <| List.mem_of_find?_eq_some h
  refine .inr ⟨_, h2, h1, this⟩

theorem ShapeFun.WF.app {f : ShapeFun n} (wf : WF Shape.WF f) (wfa : a.WF) : (ShapeFun.app f a).WF := by
  have ⟨_, _, h, _⟩ := WShape.join_prop.app_core WShape.join_prop ⟨_, wf⟩ ⟨_, wfa⟩
  exact (wf.2 _ h).2

def WShapeFun.app (f : WShapeFun n) (a : WShape n) : WShape n :=
  ⟨ShapeFun.app f.1 a.1, f.2.app a.2⟩

theorem WShapeFun.app_core (f : WShapeFun n) (x) :
    ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f ∧ ∀ y ∈ f, y.1 ≤ x → y.2 ≤ f.app x := by
  have ⟨_, h1, h2, h3⟩ := WShape.join_prop.app_core WShape.join_prop f x
  exact ⟨_, h1, f.mem_val h2, fun _ a1 => h3 _ (f.mem_val a1)⟩

theorem WShapeFun.Compat.app_l {f f' : WShapeFun n} :
    f.Compat f' → ∀ x, (f.app x).Compat (f'.app x) := WShape.join_prop.compat_app_l WShape.join_prop

theorem WShape.Compat.app_r (f : WShapeFun n) :
    x.Compat x' → (f.app x).Compat (f.app x') := WShape.join_prop.compat_app_r WShape.join_prop

omit [Params] in
@[simp] theorem ShapeFun.bot_app : (@ShapeFun.bot n).app x = .bot := by
  simp [ShapeFun.bot, ShapeFun.app, ShapeFun.maxBelow, trunc]

def Shape.app : Shape (n + 1) → Shape n → Shape n
  | .lam f, x => ShapeFun.app f x
  | _, _ => .bot

omit [Params] in
@[simp] theorem Shape.bot_app : (@Shape.bot (n+1)).app x = .bot := rfl

omit [Params] in
@[simp] theorem Shape.lift_app (le : n ≤ m) :
    (app f a : Shape n).lift m = app (f.lift _) (a.lift _) := by
  cases f <;> simp [app, lift, ShapeFun.lift_app le]

def WShape.app (f : WShape (n+1)) (a : WShape n) : WShape n := by
  refine ⟨Shape.app f.1 a.1, ?_⟩
  obtain ⟨⟨⟩, wf⟩ := f <;> try exact .bot
  exact (WShapeFun.app ⟨_, wf.1⟩ _).2

@[simp] theorem WShape.bot_app {x : WShape n} : WShape.app (WShape.bot (n := n+1)) x = .bot :=
  WShape.ext (Shape.bot_app (x := x.1))

@[simp] theorem WShape.lam_app {f : WShapeFun n} {hl} {x : WShape n} :
    WShape.app (WShape.lam f hl) x = f.app x := rfl

theorem WShapeFun.app_of_mem {f : WShapeFun n} (h : (x, y) ∈ f) :
    f.app x ≤ y ∧ y ≤ f.app x :=
  have ⟨_, h1, h2, h3⟩ := f.app_core x
  ⟨f.mem_mono h2 h h1, h3 _ h .rfl⟩

theorem WShapeFun.app_eq (f : WShapeFun n) (x : WShape n) :
    ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f :=
  let ⟨x', h1, h2, _⟩ := f.app_core x; ⟨x', h1, h2⟩

theorem WShapeFun.app_mono_l {f f' : WShapeFun n} (h : f ≤ f') (a : WShape n) :
    f.app a ≤ f'.app a := by
  have ⟨_, a1, a2, a3⟩ := f.app_core a
  have ⟨_, b1, b2, b3⟩ := f'.app_core a
  have ⟨_, _, c1, c2, c3⟩ := WShapeFun.LE.def'.1 h _ _ a2
  exact c3.trans <| b3 _ c1 (c2.trans a1)

theorem WShapeFun.app_mono_r {f : WShapeFun n} {a a' : WShape n} (h : a ≤ a') :
    f.app a ≤ f.app a' := by
  have ⟨_, a1, a2, a3⟩ := f.app_core a
  have ⟨_, b1, b2, b3⟩ := f.app_core a'
  exact b3 _ a2 (a1.trans h)

theorem WShape.app_mono_l {f f' : WShape (n+1)} (h : f ≤ f') (a : WShape n) :
    f.app a ≤ f'.app a := by
  change f.1 ≤ f'.1 at h; show Shape.app f.1 a.1 ≤ Shape.app f'.1 a.1
  cases hf : f.1 with | lam => ?_ | _ => exact Shape.bot_le
  let ⟨f', wf'⟩ := f'; have := hf ▸ f.2
  cases f' with rw [hf] at h | lam => ?_ | _ => exact (Shape.LE.def.1 h).elim
  exact WShapeFun.app_mono_l (f := ⟨_, (hf ▸ f.2).1⟩) (f' := ⟨_, wf'.1⟩) h _

theorem WShape.app_mono_r {f : WShape (n+1)} {a a' : WShape n} (h : a ≤ a') :
    f.app a ≤ f.app a' := by
  obtain ⟨⟨⟩, wf⟩ := f <;> try exact .rfl
  exact WShapeFun.app_mono_r (f := ⟨_, wf.1⟩) h

@[simp] theorem WShapeFun.bot_app : (WShapeFun.bot (n := n)).app x = .bot := by
  ext1; exact ShapeFun.bot_app

theorem WShapeFun.lift_app {f : WShapeFun n} {a : WShape n} (le : n ≤ m) :
    (f.app a).lift m = (f.lift m).app (a.lift m) := by
  ext1; simp [WShape.lift_val le, app, WShapeFun.lift_val le]
  exact ShapeFun.lift_app le

@[simp] theorem WShape.lift_app (le : n ≤ m) :
    (app f a : WShape n).lift m = app (f.lift _) (a.lift _) := by
  ext1; simp [lift_val le, app, Shape.lift_app le, lift_val (Nat.succ_le_succ le)]

@[simp] theorem WShape.lam'_app {f : WShapeFun n} {x : WShape n} : (lam' f).app x = f.app x := by
  simp [lam']; split <;> simp; rename_i h
  have ⟨_, h1, h2⟩ := f.app_eq x
  rw [eq_comm, ← WShape.le_bot]; exact Decidable.by_contra <| mt (⟨_, h2, ·⟩) h

theorem TShape.app_mono {f : WShape (n + 1)} {f' : WShape (m + 1)} {a : WShape n} {a' : WShape m}
    (le₁ : f.T ≤ f'.T) (le₂ : a.T ≤ a'.T) : (f.app a).T ≤ (f'.app a').T := by
  have lm₁ := Nat.le_max_left n m; have lm₂ := Nat.le_max_right n m
  rw [TShape.LE.def', WShape.lift_app lm₁, WShape.lift_app lm₂]
  refine (WShape.app_mono_l ?_ _).trans (WShape.app_mono_r le₂)
  exact (LE.def (Nat.succ_le_succ lm₁) (Nat.succ_le_succ lm₂)).1 le₁

theorem WShape.Compat.app {f f' : WShape (n+1)} {a a' : WShape n}
    (cf : f.Compat f') (ca : a.Compat a') : (f.app a).Compat (f'.app a') := by
  have ⟨zf, hf1, hf2⟩ := WShape.Compat.iff.1 cf
  have ⟨za, ha1, ha2⟩ := WShape.Compat.iff.1 ca
  exact WShape.Compat.iff.2 ⟨zf.app za,
    (WShape.app_mono_l hf1 _).trans (WShape.app_mono_r ha1),
    (WShape.app_mono_l hf2 _).trans (WShape.app_mono_r ha2)⟩

theorem TShape.Compat.app {f : WShape (n + 1)} {f' : WShape (m + 1)}
    {a : WShape n} {a' : WShape m}
    (cf : f.T.Compat f'.T) (ca : a.T.Compat a'.T) :
    (f.app a).T.Compat (f'.app a').T := by
  have le₁ := Nat.le_max_left n m; have le₂ := Nat.le_max_right n m
  rw [TShape.Compat.def le₁ le₂, WShape.lift_app le₁, WShape.lift_app le₂]
  exact WShape.Compat.app
    ((TShape.Compat.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 cf)
    ((TShape.Compat.def le₁ le₂).1 ca)

theorem WShapeFun.mem_join {f f' : WShapeFun n} {a} (hc : f.Compat f') :
    (a, b) ∈ f.join f' ↔ ∃ x ∈ f, ∃ y ∈ f', x.1.Compat y.1 ∧
      let j := x.1.join y.1; a = j ∧ b = (f.app j).join (f'.app j) := by
  simp only [WShapeFun.mem_def, WShapeFun.join_val hc, ShapeFun.mem_join]
  constructor
  · intro ⟨x, h1, y, h2, h3, h4⟩
    refine have h3' := ?_; ⟨_, f.mem_val h1, _, f'.mem_val h2, h3', ?_⟩; · exact h3
    cases a; cases b; cases h4; simp; constructor <;> ext1
    · simp [WShape.join_val h3']
    · rw [WShape.join_val (hc.app_l _)]; simp [app, WShape.join_val h3']
  · rintro ⟨x, h1, y, h2, h3, rfl, rfl⟩; refine ⟨_, h1, _, h2, h3, ?_⟩
    simp [WShape.join_val h3]; rw [WShape.join_val (hc.app_l _)]; simp [app, WShape.join_val h3]

def ShapeFun.single (x y : Shape n) : ShapeFun n :=
  (x, y) :: if x ≤ .bot then [] else [(.bot, .bot)]

omit [Params] in
theorem ShapeFun.self_mem_single : (x, y) ∈ single x y := .head _

protected theorem ShapeFun.WF.single (x y : WShape n) : WF Shape.WF (single x.1 y.1) := by
  refine ⟨?_, fun p hp => ?_⟩; rotate_left
  · simp [single] at hp
    obtain rfl | ⟨_, rfl⟩ := hp
    · exact ⟨x.2, y.2⟩
    · exact ⟨.bot, .bot⟩
  simp only [single, List.mem_cons, List.mem_ite_nil_left, List.not_mem_nil, or_false,
    exists_eq_or_imp, forall_eq_or_imp, and_imp, forall_eq_apply_imp_iff, Shape.bot_le,
    imp_self, and_true]
  have self : x.1.join x.1 ≤ x.1 ∧ x.1 ≤ x.1.join x.1 :=
    WShape.join_val .rfl ▸ (WShape.Join.iff.1 (WShape.join_self.2 ⟨.rfl, .rfl⟩)).2
  refine ⟨?_, ⟨⟨fun _ => .inl self, fun _ => .rfl⟩, ?_⟩, fun nle => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · obtain ⟨x, _⟩ := x; by_cases h : x ≤ .bot
    · cases Shape.le_bot.1 h; exact ⟨_, .inl rfl⟩
    · exact ⟨_, .inr ⟨h, rfl⟩⟩
  · exact (⟨by simp [Shape.join_bot, Shape.LE.rfl], ·.elim⟩)
  · simp [Shape.bot_join, Shape.LE.rfl]
  · simp [Shape.bot_join, nle]

def WShapeFun.single (x y : WShape n) : WShapeFun n :=
  ⟨ShapeFun.single x.1 y.1, .single x y⟩

omit [Params] in
theorem ShapeFun.single_app : (single x y).app x' = if x ≤ x' then y else .bot := by
  simp [single, app, trunc, maxBelow, List.find?]
  by_cases h : x ≤ x' <;> simp [h, Shape.LE.rfl]; split <;> simp

theorem WShapeFun.single_app {x y : WShape n} {x' : WShape n} :
    (WShapeFun.single x y).app x' = if x ≤ x' then y else .bot := by
  ext1; simp [WShapeFun.single, app, ShapeFun.single_app]
  split <;> simp [*, WShape.LE.def, WShape.bot]

theorem WShapeFun.mem_single {x y : WShape n} :
    a ∈ WShapeFun.single x y ↔ a = (x, y) ∨ ¬x ≤ .bot ∧ a = (.bot, .bot) := by
  cases a; simp [WShapeFun.mem_def, WShapeFun.single, ShapeFun.single,
    WShape.ext_iff, WShape.LE.def, WShape.bot]

theorem WShapeFun.single_le {f : WShapeFun n} :
    WShapeFun.single x y ≤ f ↔ ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' := by
  simp [WShapeFun.LE.def', WShapeFun.mem_single]
  refine ⟨fun H => H _ _ (.inl ⟨rfl, rfl⟩), ?_⟩
  rintro H _ _ (⟨rfl, rfl⟩ | ⟨h4, rfl, rfl⟩)
  · exact H
  · let ⟨_, h1⟩ := f.bot_mem; exact ⟨_, _, h1, .rfl, WShape.bot_le⟩

theorem WShapeFun.lift_single (le : n ≤ m) {x y : WShape n} :
    (WShapeFun.single x y).lift m = WShapeFun.single (x.lift m) (y.lift m) := by
  ext1; simp [lift_val le, single, WShape.lift_val le, ShapeFun.single, ShapeFun.lift]
  split <;> simp [*, Shape.lift_le_bot le, ← Shape.le_bot]

theorem WShapeFun.compat_single {f : WShapeFun n} :
    Compat f (single x y) ↔ ∀ a ∈ f, a.1.Compat x → a.2.Compat y := by
  simp [WShapeFun.Compat.def, mem_single, WShape.Compat.bot_r]

omit [Params] in
theorem ShapeFun.lift_single (le : n ≤ m) {x y : Shape n} :
    lift (Shape.lift _) (ShapeFun.single x y) = (ShapeFun.single (x.lift m) (y.lift m)) := by
  simp [lift, single] <;> split <;> rename_i h <;>
    simpa [Shape.lift_le_bot le, Shape.le_bot] using h

theorem WShapeFun.Join.app_l {f g h : WShapeFun n}
    (hJ : Join f g h) (p : WShape n) : WShape.Join (f.app p) (g.app p) (h.app p) := by
  refine fun z => ⟨fun H => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · exact (app_mono_l hJ.le.1 p).trans H
  · exact (app_mono_l hJ.le.2 p).trans H
  · refine (app_mono_l (Join.iff.1 hJ).2.2 _).trans ?_
    have ⟨x, a1, a2, a3⟩ := (f.join g).app_core p
    obtain ⟨⟨a, _⟩, b1, ⟨b, _⟩, b2, b3, rfl, b5⟩ := (WShapeFun.mem_join hJ.compat).1 a2
    have hJ' := WShape.Join.mk (hJ.compat.app_l (a.join b))
    exact b5 ▸ (hJ' _).2 ⟨(app_mono_r a1).trans h1, (app_mono_r a1).trans h2⟩

def hasType.core (hasType : Shape n → Shape n → Bool)
    (f : ShapeFun n) (a : Shape n) (G : Shape n → Shape n) : Bool :=
  f.all fun (x, y) => (f.any fun (x', y') => x' ≤ x && y ≤ y' && hasType x' a) && hasType y (G x)

/--
Shape-level typing.

**Two clauses quantify over the codomain's sort by disjunction** (`.bot`/`.lam` against
`.forallE`). They used to read `fun _ => .type`, i.e. `.sort true`, asserting that a Pi-type's
codomains are `Sort`-valued and so denying that a proof can inhabit a `Prop`-valued Pi.
`r : Bool` is finite, so the existential is writable directly; quantifying *outside* the
`hasType.core` call gives one sort for the whole codomain family, which is the correct
reading -- a Pi-type's codomains share a level.

**Editing these clauses costs proof repair proportional to how many proofs rely on this
function *reducing*.** That dependency is pervasive and easy to miss: `HasType.unfold_iff`
closes cases with `cases n <;> rfl`, and five negations elsewhere are `nofun`
(`WShape.HasType.lam_isType` and neighbours). All work only because `hasType` computes. -/
def Shape.hasType : ∀ {n}, Shape n → Shape n → Bool
  | _+1, .bot, .forallE a b =>
    hasType.core hasType b a (fun _ => .sort false) ||
    hasType.core hasType b a (fun _ => .sort true)
  | _+1, .forallE a b, .sort r => hasType.core hasType b a fun _ => .sort r
  | 0, .bot, _ | _+1, .bot, .bot | _+1, .bot, .sort _ | _+1, .bot, .indTy _ => true
  | 0, .sort _, .sort j | _+1, .sort _, .sort j => j
  | _+1, .lam f, .forallE a b =>
    (hasType.core hasType b a (fun _ => .sort false) ||
     hasType.core hasType b a (fun _ => .sort true)) &&
    hasType.core hasType f a (ShapeFun.app b)
  -- Section 7: a `.ctor` shape is classified only by a `Type`-valued inductive.  With
  -- `.indTy false` (a `Prop`-valued inductive) this must be `false`, or `proofIrrel` is
  -- refuted by `.ctor c [] : .indTy false` -- see `proofIrrel_fails`.
  | _+1, .ctor _ _, .indTy r => r
  | _+1, .indTy r, .sort r' => r = r'
  | _, _, _ => false

def Shape.HasType : Shape n → Shape n → Prop := (hasType · ·)

/-- `a` classifies terms: it is a type *or a proposition*. Replaces the former
`HasType a .type`, which forced the sort boolean to `true` and so silently asserted that
every classifying shape is `Sort`-valued -- false once `.indTy false` exists.

**This framing is correct, not merely convenient, and the evidence is that nothing broke.**
`.type` was load-bearing only in *signatures*, never in arguments: the `LogRel` fields that
demanded it (`bot`, `mono_r_2`, `mono_r_2_ty`, `join_ty`) have instance proofs that bind
those hypotheses and never use them -- see `mono_r_2_ty` in the `LR0` instance, whose
binders are literally `le _ _`. So replacing `HasType a .type` by `IsType a` does not weaken
any proof; it deletes an unused hypothesis that happened to assert something false. -/
def Shape.IsType (a : Shape n) : Prop := ∃ r, HasType a (.sort r)

def Shape.HasDom (f : ShapeFun n) (a : Shape n) :=
  ∀ x y, (x, y) ∈ f → ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' ∧ x'.HasType a

def Shape.HasTypePi (b : ShapeFun n) (a : Shape n) (rel : Bool) :=
  Shape.HasDom b a ∧ ∀ x y, (x, y) ∈ b → y.HasType (.sort rel)

def Shape.HasTypeLam (f : ShapeFun n) (a : Shape n) (b : ShapeFun n) :=
  (∃ r, Shape.HasTypePi b a r) ∧ Shape.HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (b.app x)

omit [Params] in
theorem Shape.hasType.core.iff {a : Shape n} :
    hasType.core hasType f a G ↔ HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (G x) := by
  simp [hasType.core, HasDom, forall_and, HasType, and_assoc]

omit [Params] in
/-- The disjunction that the `.bot`/`.lam`-against-`.forallE` clauses of `hasType` use to
quantify over the codomain family's sort, packaged as the existential it means. Downstream
proofs should go through this rather than unfolding the `||`. -/
theorem Shape.hasType.core_sort_or {b : ShapeFun n} {a : Shape n} :
    (hasType.core hasType b a (fun _ => .sort false) ||
     hasType.core hasType b a (fun _ => .sort true)) = true ↔ ∃ r, HasTypePi b a r := by
  simp only [Bool.or_eq_true, core.iff, HasTypePi]
  exact ⟨fun h => h.elim (⟨false, ·⟩) (⟨true, ·⟩),
    fun ⟨r, h⟩ => match r, h with | false, h => .inl h | true, h => .inr h⟩

inductive Shape.HasTypeU : ∀ {n}, Shape n → Shape n → Prop
  | bot : HasType x (.sort r) → HasTypeU .bot x
  | sort : HasTypeU (.sort r) .type
  | forallE : HasTypePi (n := n) b a r → HasTypeU (n := n+1) (.forallE a b) (.sort r)
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam f) (.forallE a b)
  | ctor : HasTypeU (n := n+1) (.ctor c l) (.indTy true)
  | indTy : HasTypeU (n := n+1) (.indTy r) (.sort r)

omit [Params] in
theorem Shape.HasType.unfold {m a : Shape n} : HasType m a → HasTypeU m a := by
  unfold HasType Shape.hasType
  split <;> intro h
  case h_1 =>  -- `.bot` against `.forallE`: the disjunction picks `HasTypeU.bot`'s `r`
    obtain ⟨r, hr⟩ := hasType.core_sort_or.1 h
    exact .bot (r := r) (by simpa [HasType, hasType, hasType.core.iff, HasTypePi] using hr)
  case h_2 => exact .forallE (by simpa [HasTypePi, hasType.core.iff] using h)
  case h_3 => rename_i x; cases x <;> exact .bot (r := true) rfl
  case h_4 => exact .bot (r := true) rfl
  case h_5 => exact .bot rfl
  case h_6 => rename_i r'; exact .bot (r := r') (by simp [HasType, hasType])
  case h_7 => simp only [h]; exact .sort
  case h_8 => simp only [h]; exact .sort
  case h_9 =>  -- `.lam` against `.forallE`
    rw [Bool.and_eq_true] at h
    exact .lam ⟨hasType.core_sort_or.1 h.1,
      (hasType.core.iff.1 h.2).1, (hasType.core.iff.1 h.2).2⟩
  case h_10 => subst h; exact .ctor
  case h_11 => simp only [decide_eq_true_eq] at h; subst h; exact .indTy
  case h_12 => exact Bool.noConfusion h

omit [Params] in
theorem Shape.HasType.unfold_iff {m a : Shape n} : HasType m a ↔ HasTypeU m a := by
  refine ⟨(·.unfold), fun h => ?_⟩
  cases h with
  | @bot _ x r h =>
    -- `.bot` inhabits anything that is classified by *some* sort, so go by cases on `x`
    -- rather than on `h.unfold`, whose `sort` case would need `r = true`.
    cases n with
    | zero => cases a <;> rfl
    | succ n =>
      cases a with
      | bot | sort | indTy => rfl
      | forallE a b =>
        exact hasType.core_sort_or.2
          ⟨r, by simpa [HasType, hasType, hasType.core.iff, HasTypePi] using h⟩
      | lam f => exact absurd h (by simp [HasType, hasType])
      | ctor c l => exact absurd h (by simp [HasType, hasType])
  | sort => cases n <;> rfl
  | forallE H => simpa [HasType, hasType, hasType.core.iff, HasTypePi] using H
  | lam H =>
    rw [HasType, hasType, Bool.and_eq_true]
    exact ⟨hasType.core_sort_or.2 H.1, hasType.core.iff.2 ⟨H.2.1, H.2.2⟩⟩
  | ctor => rfl
  | indTy => simp [HasType, hasType]

omit [Params] in
protected theorem Shape.HasType.lift (le : n ≤ n') :
    Shape.HasType (m.lift n') (a.lift n') ↔ Shape.HasType (n := n) m a := by
  dsimp [HasType]; rw [← Bool.eq_iff_iff]
  induction n generalizing n' with
  | zero =>
    cases n' with | zero => simp [Shape.lift_self] | succ n'
    cases m <;> cases a <;> simp [Shape.lift, hasType]
  | succ n ih =>
    let n' + 1 := n'; replace le := Nat.le_of_succ_le_succ le
    replace ih {m a} := @ih _ m a le
    have core {a : ShapeFun n} {a' : Shape n} {G G'}
        (H : ∀ x, G' (lift n' x) = lift n' (G x)) :
        hasType.core hasType (ShapeFun.lift (lift n') a) (lift n' a') G' =
        hasType.core hasType a a' G := by
      rw [Bool.eq_iff_iff]; simp [hasType.core, ShapeFun.lift, H, ih, lift_le_lift le]
    -- `repeat`, not `try rw`: the `.bot`/`.lam`-against-`.forallE` clauses now hold *two*
    -- `hasType.core` calls (the codomain-sort disjunction), and `rw` rewrites only the first.
    cases m <;> cases a <;> simp only [lift, hasType, type] <;>
      repeat rw [core fun _ => lift_sort.symm]
    · rw [core fun _ => (ShapeFun.lift_app le).symm]

omit [Params] in
protected theorem Shape.HasDom.lift (le : n ≤ n') :
    HasDom (ShapeFun.lift (lift n') m) (a.lift n') ↔ HasDom (n := n) m a := by
  simp only [HasDom, ShapeFun.lift, List.mem_map, Prod.mk.injEq]
  constructor <;> [intro H x y h; rintro H x y ⟨_, h, rfl, rfl⟩]
  · obtain ⟨_, _, ⟨_, h1, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ ⟨_, h, rfl, rfl⟩
    exact ⟨_, _, h1, (Shape.lift_le_lift le).1 h2,
      (Shape.lift_le_lift le).1 h3, (Shape.HasType.lift le).1 h4⟩
  · have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
    exact ⟨_, _, ⟨_, h1, rfl, rfl⟩, Shape.lift_mono h2,
      Shape.lift_mono h3, (Shape.HasType.lift le).2 h4⟩

omit [Params] in
protected theorem Shape.HasTypePi.lift (le : n ≤ n') :
    HasTypePi (ShapeFun.lift (lift n') m) (a.lift n') rel ↔ HasTypePi (n := n) m a rel := by
  simp only [HasTypePi]
  exact and_congr (HasDom.lift le) <| by
    simp only [ShapeFun.lift, List.mem_map, Prod.mk.injEq]
    constructor <;> [intro H x y h; rintro H _ _ ⟨⟨x, y⟩, h, rfl, rfl⟩]
    · exact (Shape.HasType.lift le).1 (Shape.lift_sort.symm ▸ H _ _ ⟨_, h, rfl, rfl⟩)
    · exact Shape.lift_sort ▸ (Shape.HasType.lift le).2 (H _ _ h)

omit [Params] in
theorem Shape.HasTypeLam.lift (le : n ≤ n') :
    HasTypeLam (ShapeFun.lift (lift n') f) (a.lift n') (ShapeFun.lift (lift n') b) ↔
    HasTypeLam (n := n) f a b := by
  simp only [HasTypeLam]
  refine and_congr (exists_congr fun _ => HasTypePi.lift le) <|
    and_congr (HasDom.lift le) ⟨?_, ?_⟩ <;> intro H x y h
  · have h' : (x.lift n', y.lift n') ∈ ShapeFun.lift (Shape.lift n') f :=
      List.mem_map.2 ⟨_, h, rfl⟩
    have := H _ _ h'
    rw [← ShapeFun.lift_app le] at this
    exact (Shape.HasType.lift le).1 this
  · obtain ⟨⟨x₀, y₀⟩, h₀, heq⟩ := List.mem_map.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    rw [← ShapeFun.lift_app le]
    exact (Shape.HasType.lift le).2 (H _ _ h₀)

omit [Params] in
protected theorem Shape.HasType.bot {a : Shape n} {r} (H : HasType a (.sort r)) :
    HasType .bot a :=
  unfold_iff.2 (.bot H)
omit [Params] in
protected theorem Shape.HasType.sort : HasType (n := n) (.sort rel) .type := unfold_iff.2 .sort
omit [Params] in
protected theorem Shape.HasType.forallE (H : HasTypePi (n := n) b a r) :
    HasType (n := n+1) (.forallE a b) (.sort r) := unfold_iff.2 (.forallE H)
omit [Params] in
protected theorem Shape.HasType.lam (H : HasTypeLam (n := n) f a b) :
    HasType (n := n+1) (.lam f) (.forallE a b) := unfold_iff.2 (.lam H)
omit [Params] in
protected theorem Shape.HasType.indTy : HasType (n := n+1) (.indTy r) (.sort r) := unfold_iff.2 .indTy

omit [Params] in
theorem Shape.HasType.bot_r (H : HasType (n := n) x .bot) : x = .bot := by
  cases n <;> cases x <;> simp [HasType, hasType, bot] at H ⊢

omit [Params] in
theorem Shape.HasType.isType (H : HasType m a) : a.IsType := by
  cases H.unfold with
  | bot H => exact ⟨_, H⟩
  | sort | forallE | indTy => exact ⟨_, .sort⟩
  | lam H' => have ⟨r, hr⟩ := H'.1; exact ⟨r, .forallE hr⟩
  | ctor => exact ⟨_, .indTy⟩

def WShape.HasType (m a : WShape n) : Prop := Shape.HasType m.1 a.1
/-- Stated with `WShape.HasType` rather than as `Shape.IsType a.1` (which is definitionally
the same) so that destructuring an `IsType` yields a hypothesis whose head is
`WShape.HasType`, keeping dot-notation (`.mono_l`, `.forallE_l`, ...) working. -/
def WShape.IsType (a : WShape n) : Prop := ∃ r, WShape.HasType a (.sort r)
def WShape.HasDom (f : WShapeFun n) (a : WShape n) := Shape.HasDom f.1 a.1
def WShape.HasTypePi (b : WShapeFun n) (a : WShape n) := Shape.HasTypePi b.1 a.1
def WShape.HasTypeLam (f : WShapeFun n) (a : WShape n) (b : WShapeFun n) :=
  Shape.HasTypeLam f.1 a.1 b.1

theorem WShape.HasDom.def : HasDom f a ↔
    ∀ x y, (x, y) ∈ f → ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' ∧ x'.HasType a :=
  ⟨fun H _ _ h => have ⟨_, _, h1, h2⟩ := H _ _ h; ⟨_, _, f.mem_val h1, h2⟩,
   fun H _ _ h => have ⟨_, _, h1, h2⟩ := H _ _ (f.mem_val h); ⟨_, _, h1, h2⟩⟩

theorem WShape.HasTypePi.def {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x y, (x, y) ∈ b → y.HasType (.sort rel) :=
  and_congr_right' ⟨fun H _ _ h => H _ _ h, fun H _ _ h => H _ _ (b.mem_val h)⟩

theorem WShape.HasTypeLam.def {f : WShapeFun n} {a b} :
  HasTypeLam f a b ↔
    (∃ r, HasTypePi b a r) ∧ HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (b.app x) :=
  and_congr_right' <| and_congr_right' ⟨fun H _ _ h => H _ _ h, fun H _ _ h => H _ _ (f.mem_val h)⟩

theorem WShape.HasDom.lift (le : n ≤ m) :
    HasDom (f.lift m) (a.lift m) ↔ HasDom (n := n) f a := by
  simp only [HasDom, Shape.HasDom, WShapeFun.lift_val le, ShapeFun.lift, List.mem_map,
    Prod.mk.injEq, WShape.lift_val le]
  constructor <;> [intro H x y h; rintro H x y ⟨_, h, rfl, rfl⟩]
  · obtain ⟨_, _, ⟨_, h1, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ ⟨_, h, rfl, rfl⟩
    exact ⟨_, _, h1, (Shape.lift_le_lift le).1 h2,
      (Shape.lift_le_lift le).1 h3, (Shape.HasType.lift le).1 h4⟩
  · have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
    exact ⟨_, _, ⟨_, h1, rfl, rfl⟩, Shape.lift_mono h2,
      Shape.lift_mono h3, (Shape.HasType.lift le).2 h4⟩

theorem WShape.HasType.isType : HasType m a → a.IsType := Shape.HasType.isType

/-- Package a classification at a *known* sort as the existential `IsType`.  Replaces the
former `HasType.toType`, which coerced `HasType a (.sort r)` to `HasType a .type` and so
silently claimed every classifying shape is `Sort`-valued. -/
theorem WShape.HasType.toIsType {a : WShape n} {r} (h : HasType a (.sort r)) : a.IsType := ⟨r, h⟩

theorem WShape.HasDom.isType (H : WShape.HasDom f a) : a.IsType := by
  have ⟨_, h⟩ := f.bot_mem
  have ⟨_, _, _, h2, _, h4⟩ := HasDom.def.1 H _ _ h
  cases le_bot.1 h2; exact h4.isType

theorem WShape.HasType.mono_r {m a a' : WShape n} (ha : a ≤ a')
    (Ha : HasType a' (.sort r)) (H : HasType m a) : HasType m a' := by
  have ⟨m, mwf⟩ := m; have ⟨a, awf⟩ := a; have ⟨a', awf'⟩ := a'
  simp only [HasType, sort, WShape.LE.def] at *
  cases H.unfold with
  | bot H => exact .bot Ha
  | sort | forallE | indTy => cases Shape.sort_le.1 ha; exact H
  | ctor => cases Shape.indTy_le.1 ha; exact H
  | @lam n _ _ _ H' =>
    obtain ⟨_, _, h1, h2, ⟨⟩⟩ := Shape.forallE_le.1 ha
    let .forallE Ha := Ha.unfold
    have ih := @WShape.HasType.mono_r n
    let rec ih_dom {f : WShapeFun n} {a a' r} (ha : a ≤ a') (Ha : HasType a' (.sort r))
        (H : HasDom (n := n) f a) : HasDom f a' := by
      rw [WShape.HasDom.def] at H ⊢; intro _ _ h
      have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
      exact ⟨_, _, h1, h2, h3, ih ha Ha h4⟩
    let rec ih_lam {f : WShapeFun n} {a a' b b'} (Ha : HasTypePi b' a' r)
        (ha : a ≤ a') (hb : b ≤ b') (H : HasTypeLam f a b) : HasTypeLam f a' b' := by
      rw [HasTypeLam.def] at H ⊢
      have ⟨_, ht⟩ := (HasTypePi.def.1 Ha).1.isType
      refine ⟨⟨_, Ha⟩, ih_dom ha ht H.2.1, fun x y h => ?_⟩
      have ⟨_, h1, h2⟩ := b'.app_eq x
      exact .mono_r (WShapeFun.app_mono_l hb _) ((HasTypePi.def.1 Ha).2 _ _ h2) (H.2.2 _ _ h)
    exact .lam (ih_lam (f := ⟨_, mwf.1⟩) (a := ⟨_, awf.1⟩)
      (a' := ⟨_, awf'.1⟩) (b := ⟨_, awf.2⟩) (b' := ⟨_, awf'.2⟩) Ha h1 h2 H')

theorem WShape.HasDom.mono_r {f : WShapeFun n} {a a' r} :
    a ≤ a' → HasType a' (.sort r) → HasDom f a → HasDom f a' := HasType.mono_r.ih_dom HasType.mono_r

theorem WShape.HasTypeLam.mono_r {f : WShapeFun n} {a a' b b'} :
    HasTypePi b' a' r → a ≤ a' → b ≤ b' → HasTypeLam f a b → HasTypeLam f a' b' :=
  HasType.mono_r.ih_lam HasType.mono_r

omit [Params] in
private theorem find_cycle (R : α → α → Prop)
    (trans : ∀ {x y z}, R x y → R y z → R x z) (l : List α)
    (H : ∀ x ∈ l, ∃ y ∈ l, R x y) : ∀ x ∈ l, ∃ y ∈ l, R x y ∧ R y y := by
  intro x h
  suffices ∀ l₁ l₂, l.Perm (l₁ ++ l₂) → (∀ y ∈ l₂, ∀ z ∈ l, R x z → R y z) →
      ∃ y ∈ l, R x y ∧ R y y from this l [] (by simp) nofun
  intro l₁; generalize eq : l₁.length = i; revert x l₁
  refine i.strongRecOn ?_; rintro i ih x₀ h₀ l₁ rfl l₂ he hl
  have ⟨x', a1, a2⟩ := H x₀ h₀
  obtain hm | hm := List.mem_append.1 (he.mem_iff.1 a1)
  · have ⟨l', hp⟩ := List.perm_cons_of_mem hm
    have he' := he.trans (.append_right _ hp) |>.trans List.perm_middle.symm
    refine have ⟨_, c1, c2, c3⟩ := ih l'.length ?_ _ a1 _ rfl _ he' ?_; ⟨_, c1, trans a2 c2, c3⟩
    · rw [hp.length_eq]; apply Nat.lt_succ_self
    · rintro x' (⟨⟩ | ⟨_, hx⟩) z hz hr <;> [exact hr; exact hl _ hx _ hz (trans a2 hr)]
  · exact ⟨_, a1, a2, hl _ hm _ a1 a2⟩

namespace WShape.HasType.mono_l
variable (ih : ∀ {m m' a : WShape n}, m ≤ m' → m' ≤ m → HasType m a → HasType m' a)
include ih

theorem ih_dom {f f' : WShapeFun n} (hf1 : f ≤ f') (hf2 : f' ≤ f)
    (H : HasDom f a) : HasDom f' a := by
  rw [HasDom.def] at H ⊢; intro x y h
  have ⟨z, h1, ⟨c, c1, c2, c3, _⟩, d, d1, d2, _, d4⟩ := find_cycle ?_ f'.1 ?_ _ h
    (R := fun x y => ∃ z : WShape n, y.1 ≤ z.1 ∧ z.1 ≤ x.1 ∧ x.2 ≤ y.2 ∧ z.HasType a)
  · exact ⟨_, _, f'.mem_val h1, c1.trans c2, c3, ih d2 d1 d4⟩
  · rintro x y z ⟨_, a1, a2, a3, a4⟩ ⟨_, b1, b2, b3, b4⟩
    exact ⟨_, b1, b2.trans (a1.trans a2), a3.trans b3, b4⟩
  · rintro x h
    have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hf2 _ _ (f'.mem_val h)
    have ⟨x₂, y₂, b1, b2, b3, b4⟩ := H _ _ a1
    have ⟨x₃, y₃, c1, c2, c3⟩ := WShapeFun.LE.def'.1 hf1 _ _ b1
    exact ⟨_, c1, _, c2, b2.trans a2, a3.trans (b3.trans c3), b4⟩

theorem ih_pi {b b'} {a a' : WShape n}
    (hb1 : b ≤ b') (hb2 : b' ≤ b) (ha1 : a ≤ a') (ha2 : a' ≤ a)
    (H : HasTypePi b a r) : HasTypePi b' a' r := by
  rw [HasTypePi.def] at H ⊢
  have ⟨_, hIs⟩ := H.1.isType
  refine ⟨ih_dom ih hb1 hb2 H.1 |>.mono_r ha1 (ih ha1 ha2 hIs), fun x y h => ?_⟩
  have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hb2 _ _ h
  have ⟨x₂, y₂, b1, b2, b3⟩ := WShapeFun.LE.def'.1 hb1 _ _ a1
  have ⟨_, c1, c2⟩ := b.app_eq x
  exact ih (b3.trans <| b'.mem_mono b1 h (b2.trans a2)) a3 (H.2 _ _ a1)

theorem ih_lam {f f' : WShapeFun n} (hf1 : f ≤ f') (hf2 : f' ≤ f)
    (H : HasTypeLam f a b) : HasTypeLam f' a b := by
  rw [HasTypeLam.def] at H ⊢; refine ⟨H.1, ih_dom ih hf1 hf2 H.2.1, fun x y h => ?_⟩
  have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hf2 _ _ h
  have ⟨x₂, y₂, b1, b2, b3⟩ := WShapeFun.LE.def'.1 hf1 _ _ a1
  have ⟨_, c1, c2⟩ := b.app_eq x
  have ⟨_, hr⟩ := H.1
  refine .mono_r (b.app_mono_r a2) ((HasTypePi.def.1 hr).2 _ _ c2) ?_
  exact ih (b3.trans <| f'.mem_mono b1 h (b2.trans a2)) a3 (H.2.2 _ _ a1)

end WShape.HasType.mono_l

theorem WShape.HasType.mono_l {m m' a : WShape n}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a := by
  have ⟨m, mwf⟩ := m; have ⟨m', mwf'⟩ := m'; have ⟨a, awf⟩ := a
  simp only [HasType, WShape.LE.def] at *
  cases H.unfold with
  | bot => cases Shape.le_bot.1 hm2; exact H
  | sort => cases Shape.sort_le.1 hm1; exact H
  | forallE H' =>
    obtain ⟨_, _, a1, a2, ⟨⟩⟩ := Shape.forallE_le.1 hm1
    have ⟨b1, b2⟩ := Shape.forallE_le_forallE.1 hm2
    exact .forallE <| mono_l.ih_pi mono_l (b := ⟨_, mwf.2⟩) (b' := ⟨_, mwf'.2⟩)
      (a := ⟨_, mwf.1⟩) (a' := ⟨_, mwf'.1⟩) a2 b2 a1 b1 H'
  | lam H' =>
    obtain ⟨_, a1, ⟨⟩⟩ := Shape.lam_le.1 hm1; have b1 := Shape.lam_le_lam.1 hm2
    exact .lam <| mono_l.ih_lam mono_l (f := ⟨_, mwf.1⟩) (f' := ⟨_, mwf'.1⟩)
      (a := ⟨_, awf.1⟩) (b := ⟨_, awf.2⟩) hm1 hm2 H'
  | ctor => cases m' <;> simp [Shape.LE.def] at hm1; rfl
  | indTy => cases Shape.indTy_le.1 hm1; exact H

theorem WShape.HasDom.mono_l {f f' : WShapeFun n} : f ≤ f' → f' ≤ f →
    HasDom f a → HasDom f' a := WShape.HasType.mono_l.ih_dom WShape.HasType.mono_l
theorem WShape.HasTypePi.mono_l {a a' : WShape n} : b ≤ b' → b' ≤ b → a ≤ a' → a' ≤ a →
    HasTypePi b a r → HasTypePi b' a' r := WShape.HasType.mono_l.ih_pi WShape.HasType.mono_l
theorem WShape.HasTypeLam.mono_l {f f' : WShapeFun n} : f ≤ f' → f' ≤ f →
    HasTypeLam f a b → HasTypeLam f' a b := WShape.HasType.mono_l.ih_lam WShape.HasType.mono_l

theorem WShape.HasDom.iff {f : WShapeFun n} :
    HasDom f a ↔ ∀ x, ∃ x', x' ≤ x ∧ x'.HasType a ∧ f.app x ≤ f.app x' := by
  refine WShape.HasDom.def.trans ⟨fun H x => ?_, fun H x₀ y₀ h₀ => ?_⟩
  · have ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
    have ⟨x₂, y₂, b1, b2, b3, b4⟩ := H _ _ a2
    exact ⟨_, b2.trans a1, b4, .trans b3 (f.app_of_mem b1).2⟩
  · have ⟨z, h1, ⟨c, c1, c2, c3, _⟩, d, d1, d2, _, d4⟩ := find_cycle ?_ f.1 ?_ _ h₀
      (R := fun x y => ∃ z : WShape n, y.1 ≤ z.1 ∧ z.1 ≤ x.1 ∧ x.2 ≤ y.2 ∧ z.HasType a)
    · exact ⟨_, _, f.mem_val h1, c1.trans c2, c3, d4.mono_l d2 d1⟩
    · rintro x y z ⟨_, a1, a2, a3, a4⟩ ⟨_, b1, b2, b3, b4⟩
      exact ⟨_, b1, b2.trans (a1.trans a2), a3.trans b3, b4⟩
    · rintro x h
      have ⟨x', a1, a2, a3⟩ := H ⟨_, (f.2.2 _ h).1⟩
      have ⟨x₁, b1, b2⟩ := f.app_eq x'
      exact ⟨_, b2, _, b1, a1, (f.app_of_mem (f.mem_val h)).2.trans a3, a2⟩

theorem WShape.HasTypePi.iff {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x, x.HasType a → (b.app x).HasType (.sort rel) := by
  refine WShape.HasTypePi.def.trans <| and_congr_right fun hd =>
    ⟨fun H x h => ?_, fun H x y h => ?_⟩
  · have ⟨_, h1, h2⟩ := b.app_eq x; exact H _ _ h2
  · have ⟨h1, h2⟩ := b.app_of_mem h
    have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 hd x
    exact (H _ a2).mono_l (b.app_mono_r a1 |>.trans h1) (h2.trans a3)

theorem WShape.HasTypePi.iff' {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x, (b.app x).HasType (.sort rel) := by
  refine WShape.HasTypePi.iff.trans <| and_congr_right fun h1 => ⟨fun H x => ?_, fun H _ _ => H _⟩
  have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 h1 x
  exact (H _ a2).mono_l (WShapeFun.app_mono_r a1) a3

theorem WShape.HasTypeLam.iff {f : WShapeFun n} {a b} :
    HasTypeLam f a b ↔ (∃ r, HasTypePi b a r) ∧ HasDom f a ∧
      ∀ x, x.HasType a → (f.app x).HasType (b.app x) := by
  refine WShape.HasTypeLam.def.trans <| and_congr_right fun hp => and_congr_right fun hd =>
    ⟨fun H x h => ?_, fun H x y h => ?_⟩
  · have ⟨_, h1, h2⟩ := f.app_eq x
    have ⟨_, hp'⟩ := hp
    exact .mono_r (b.app_mono_r h1) ((WShape.HasTypePi.iff.1 hp').2 _ h) <| H _ _ h2
  · have ⟨h1, h2⟩ := f.app_of_mem h
    have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 hd x
    have ⟨_, hp'⟩ := hp
    have ⟨x₂, b1, b2, b3⟩ := HasDom.iff.1 hp'.1 x
    exact .mono_r (b.app_mono_r a1)
      ((WShape.HasTypePi.iff.1 hp').2 _ b2 |>.mono_l (b.app_mono_r b1) b3)
      ((H _ a2).mono_l (.trans (f.app_mono_r a1) h1) (h2.trans a3))

theorem WShape.HasTypeLam.iff' {b : WShapeFun n} :
    HasTypeLam f a b ↔
      (∃ r, HasTypePi b a r) ∧ HasDom f a ∧ ∀ x, (f.app x).HasType (b.app x) := by
  refine WShape.HasTypeLam.iff.trans <| and_congr_right fun h1 => and_congr_right fun h2 =>
    ⟨fun H x => ?_, fun H _ _ => H _⟩
  have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 h2 x
  have := (H _ a2).mono_l (WShapeFun.app_mono_r a1) a3
  have ⟨_, h1'⟩ := h1
  exact ((HasTypePi.iff'.1 h1').2 _).mono_r (WShapeFun.app_mono_r a1) this

theorem WShape.HasTypePi.lift (le : n ≤ m) :
    HasTypePi (b.lift m) (a.lift m) rel ↔ HasTypePi (n := n) b a rel := by
  simp only [HasTypePi, WShapeFun.lift_val le, WShape.lift_val le]
  exact Shape.HasTypePi.lift le

theorem WShape.HasTypeLam.lift (le : n ≤ m) :
    HasTypeLam (f.lift m) (a.lift m) (b.lift m) ↔
    HasTypeLam (n := n) f a b := by
  simp only [HasTypeLam, WShapeFun.lift_val le, WShape.lift_val le]
  exact Shape.HasTypeLam.lift le

inductive WShape.HasTypeU : ∀ {n}, WShape n → WShape n → Prop
  | bot : HasType x (.sort r) → HasTypeU .bot x
  | sort : HasTypeU (.sort r) .type
  | forallE : HasTypePi (n := n) b a r → HasTypeU (n := n+1) (.forallE a b) (.sort r)
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam' f) (.forallE a b)
  | ctor : HasTypeU (n := n+1) (.ctor c l wf) (.indTy true)
  | indTy : HasTypeU (n := n+1) (.indTy r) (.sort r)

theorem WShape.HasType.unfold {m a : WShape n} (H : HasType m a) : HasTypeU m a := by
  let ⟨m, mwf⟩ := m; let ⟨a, awf⟩ := a
  dsimp only [HasType] at H
  cases H.unfold with
  | bot h => exact .bot h
  | sort => exact .sort
  | forallE h => exact .forallE (a := ⟨_, mwf.1⟩) (b := ⟨_, mwf.2⟩) h
  | lam h =>
    have := HasTypeU.lam (f := ⟨_, mwf.1⟩) (a := ⟨_, awf.1⟩) (b := ⟨_, awf.2⟩) h
    rwa [lam', dif_pos (by exact mwf.2)] at this
  | ctor => exact (WShape.mk_ctor _ mwf).2 ▸ .ctor
  | indTy => exact .indTy

theorem WShape.HasType.unfold_iff {m a : WShape n} : HasType m a ↔ HasTypeU m a := by
  refine ⟨(·.unfold), fun h => ?_⟩
  cases h with
  | bot h => exact .bot h
  | sort => exact .sort
  | forallE h => exact .forallE h
  | @lam _ f a b h =>
    unfold lam'; split
    · exact .lam h
    · have ⟨_, h1⟩ := h.1; exact .bot (.forallE h1)
  | ctor => exact Shape.HasType.unfold_iff.2 .ctor
  | indTy => exact .indTy

theorem WShape.HasType.bot' {r} : HasType (n := n) x (.sort r) → HasType .bot x :=
  (unfold_iff.2 <| .bot ·)
theorem WShape.HasType.sort : HasType (n := n) (.sort r) .type := unfold_iff.2 .sort
/-- `.bot` is classified by `.bot`.  Spelled out because the old idiom
`.bot' (.bot' .sort)` no longer determines its sort booleans now that `HasType.bot'`
carries an `r`. -/
theorem WShape.HasType.bot_bot : HasType (n := n) .bot .bot :=
  bot' (r := true) (bot' (r := true) sort)
theorem WShape.HasType.forallE : HasTypePi (n := n) b a r →
    HasType (n := n+1) (.forallE a b) (.sort r) := (unfold_iff.2 <| .forallE ·)
theorem WShape.HasType.lam : HasTypeLam (n := n) f a b →
    HasType (n := n+1) (.lam' f) (.forallE a b) := (unfold_iff.2 <| .lam ·)
theorem WShape.HasType.indTy {n : Nat} : HasType (n := n+1) (.indTy r) (.sort r) := unfold_iff.2 .indTy
theorem WShape.HasType.ctor : HasType (.ctor (n := n) c l wf) (.indTy true) := unfold_iff.2 .ctor
theorem WShape.HasType.ctor' : HasType (n := n+1) (.ctor' c l) (.indTy true) := by
  unfold WShape.ctor'; split <;> [apply ctor; exact bot' .indTy]

/-- **Section 7's payoff.** `.indTy false` -- a `Prop`-valued inductive -- classifies only
`.bot`, because `HasTypeU.ctor` is gated to `.indTy true`.  This is the clause that makes
`WShape.HasType.proofIrrel` true again; before the gating, `.ctor c []` inhabited
`.indTy false` and refuted it (see `proofIrrel_gated`). -/
theorem Shape.HasType.indTy_false_bot {x : Shape (n+1)} (h : HasType x (.indTy false)) :
    x = .bot := by
  cases x <;> simp_all [HasType, hasType, Shape.bot]

theorem WShape.HasType.indTy_false_bot {x : WShape (n+1)} (h : HasType x (.indTy false)) :
    x = .bot :=
  Subtype.ext (Shape.HasType.indTy_false_bot h)

theorem WShape.HasType.lam_isType {f : WShapeFun n} {hf} :
    ¬HasType (WShape.lam f hf) (.sort r) := nofun
theorem WShape.HasType.ctor_isType {c : Name} {l : List (WShape n)} {h} :
    ¬HasType (n := n+1) (WShape.ctor c l h) (.sort r) := nofun
theorem WShape.IsType.not_lam {f : WShapeFun n} {hf} : ¬(WShape.lam f hf).IsType :=
  fun ⟨_, h⟩ => WShape.HasType.lam_isType h
theorem WShape.IsType.not_ctor {c : Name} {l : List (WShape n)} {h} :
    ¬(WShape.ctor c l h).IsType := fun ⟨_, hh⟩ => WShape.HasType.ctor_isType hh

theorem WShape.HasType.sort_not_forallE {a : WShape n} {f : WShapeFun n} :
    ¬HasType (n := n+1) (.sort r) (.forallE a f) := nofun
theorem WShape.HasType.forallE_not_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    ¬HasType (n := n+1) (.forallE a f) (.forallE a' f') := nofun
theorem WShape.HasType.ctor_not_forallE {c l h a} {f : WShapeFun n} :
    ¬HasType (n := n+1) (WShape.ctor c l h) (.forallE a f) := nofun

theorem WShape.HasType.bot : HasType (n := n) x (.sort r) → HasType .bot x := .bot'

theorem WShape.HasType.bot_r (H : HasType (n := n) x .bot) : x = .bot := by
  cases n <;> cases H.unfold <;> rfl

theorem WShape.HasType.bot_iff : HasType (n := n) .bot x ↔ x.IsType :=
  ⟨isType, fun ⟨_, h⟩ => .bot' h⟩

theorem WShape.HasDom.bot_iff {a : WShape n} : HasDom .bot a ↔ a.IsType := by
  simp [HasDom.def, WShapeFun.mem_bot, HasType.bot_iff]

theorem WShape.HasDom.bot : a.IsType → HasDom .bot a := bot_iff.2

/-- Restated for the `indTy` migration. The old form pinned the codomain sort to `true`,
which is false once a `Prop`-valued Pi-shape exists: `.bot` inhabits it too. -/
theorem WShape.HasTypeLam.bot {b : WShapeFun n} :
    HasTypeLam .bot a b ↔ ∃ r, HasTypePi b a r := by
  refine ⟨fun h => h.1, fun h => ?_⟩
  have ⟨r, hr⟩ := h
  refine HasTypeLam.def.2 ⟨h, HasDom.bot (HasDom.isType (HasTypePi.def.1 hr).1), ?_⟩
  intro x y hm
  obtain ⟨rfl, rfl⟩ := WShapeFun.mem_bot.1 hm
  exact .bot' ((HasTypePi.iff'.1 hr).2 _)

theorem WShape.HasType.lift (h : n ≤ n') :
    HasType (m.lift n') (a.lift n') ↔ HasType (n := n) m a := by
  simp only [HasType, lift_val h]; exact Shape.HasType.lift h

theorem WShape.HasType.forallE_l {a : WShape n} {f : WShapeFun n} :
    HasType (.forallE a f) t ↔ ∃ r, HasTypePi f a r ∧ t = .sort r := by
  simp only [HasType, WShape.forallE, HasTypePi, WShape.sort,
    WShape.ext_iff, Shape.HasType.unfold_iff]
  generalize a.1 = a₁, f.1 = f₁, t.1 = t₁
  refine ⟨fun (.forallE H) => ⟨_, H, rfl⟩, fun ⟨_, H, eq⟩ => eq ▸ .forallE H⟩

theorem WShape.HasType.forallE_inv {m : WShape (n+1)} {a : WShape n} {f : WShapeFun n}
    (H : HasType m (.forallE a f)) : ∃ g, m = .lam' g ∧ HasTypeLam g a f := by
  generalize eq : a.forallE f = a' at H
  cases H.unfold with
  | bot H' =>
    refine ⟨.bot, by simp, ?_⟩; subst eq
    obtain ⟨_, H, ⟨⟩⟩ := HasType.forallE_l.1 H'
    exact HasTypeLam.bot.2 ⟨_, H⟩
  | lam H' => obtain ⟨rfl, rfl⟩ := forallE.inj.1 eq; exact ⟨_, rfl, H'⟩
  | _ => cases congrArg (·.1) eq

omit [Params] in
/-- `.bot` is classified by every sort -- it is the shape of a term about which nothing is
known, including whether it is a proof. -/
theorem Shape.HasType.sort_bot {n : Nat} {r : Bool} : HasType (n := n) .bot (.sort r) := by
  cases n <;> rfl

/-
`WShape.IsType.common` -- "two compatible classifying shapes share a sort" --

    Compat a a' → a.IsType → a'.IsType → ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r)

**is FALSE**, refuted by `cx_refutes` immediately below.  It was approved twice (once at
`Shape`, once at `WShape`) and neither placement helps: `ShapeFun.Compat`'s obligation on
values is guarded by the keys, so the pair that would force `false = true` has incompatible
keys and never fires.  Join-closure and monotonicity of `ShapeFun.WF` were both checked and
are satisfied, so `WF` is not where a proof attempt dies.  Do not re-propose it; the
replacement invariant is `LE_Interp`-relative (see the banner, §4).
-/

section CounterexampleProbe
/-- Candidate refutation of `WShape.IsType.common` at `forallE`/`forallE`. -/
private def cxB : Shape 1 := .sort true
private def cxF : ShapeFun 1 := [(.bot, .bot), (.sort true, .indTy false)]
private def cxF' : ShapeFun 1 := [(.bot, .bot), (.indTy true, .indTy true)]
private def cxA : Shape 2 := .forallE cxB cxF
private def cxA' : Shape 2 := .forallE cxB cxF'

#eval (Shape.Compat cxA cxA', Shape.hasType cxA (.sort false), Shape.hasType cxA (.sort true),
       Shape.hasType cxA' (.sort false), Shape.hasType cxA' (.sort true))

private theorem cxA_wf : Shape.WF cxA := by
  simp [cxA, cxB, cxF, Shape.WF, ShapeFun.WF, Shape.Compat, Shape.join, Shape.LE.def]

private theorem cxA'_wf : Shape.WF cxA' := by
  simp [cxA', cxB, cxF', Shape.WF, ShapeFun.WF, Shape.Compat, Shape.join, Shape.LE.def]

/-- **`WShape.IsType.common` is false.** Both shapes are well-formed and compatible, each is
classified by a sort, and no sort classifies both: `cxA`'s codomain family pins `Prop` (via
`.indTy false`) while `cxA'`'s pins `Type` (via `.indTy true`). `ShapeFun.Compat` never
compares those two values, because it only fires on pairs whose *keys* are compatible, and
`.sort true` is incompatible with `.indTy true`. -/
private theorem cx_refutes :
    ¬ ∀ {n : Nat} {a a' : WShape n},
        a.Compat a' → a.IsType → a'.IsType →
        ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r) := by
  intro H
  have ⟨r, h1, h2⟩ := H (a := ⟨cxA, cxA_wf⟩) (a' := ⟨cxA', cxA'_wf⟩)
    (by simp [WShape.Compat, cxA, cxA', cxB, cxF, cxF']; rfl)
    ⟨false, by simp [WShape.HasType, WShape.sort]; rfl⟩
    ⟨true, by simp [WShape.HasType, WShape.sort]; rfl⟩
  simp only [WShape.HasType, WShape.sort] at h1 h2
  cases r
  · exact Bool.noConfusion h2
  · exact Bool.noConfusion h1
/-- **Why relativising to `TyDefEq` / `PiDefEq` does NOT recover `cx_refutes`.**

`LRS.PiDefEq`'s obligations on a codomain family are POINTWISE in the key: they constrain
`f.app p`, one `p` at a time.  The table below is every key that is typed at `cxB`, and at
each one **at most one of the two families has a non-`.bot` value**:

    p              cxF.app p        cxF'.app p
    ----------------------------------------------
    bot            bot              bot
    sort true      indTy false      bot
    indTy true     bot              indTy true

So no pointwise comparison can ever notice that one family pins `Prop` and the other pins
`Type` -- the disagreeing values sit at keys the other family does not reach.  This is the
first diagnosis sentence again, one layer up: the constraint is on VALUES, keyed by the
DOMAIN, and the two domains' keys are incompatible. -/
private theorem piDefEq_cannot_see :
    ShapeFun.app cxF .bot = .bot ∧ ShapeFun.app cxF' .bot = .bot ∧
    ShapeFun.app cxF (.sort true) = .indTy false ∧ ShapeFun.app cxF' (.sort true) = .bot ∧
    ShapeFun.app cxF (.indTy true) = .bot ∧ ShapeFun.app cxF' (.indTy true) = .indTy true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Does the same witness refute `WShape.HasType.join`? -/
private def jF : ShapeFun 2 := [(.bot, .bot)]
private def jM : Shape 3 := .forallE cxA jF
private def jM' : Shape 3 := .forallE cxA' jF

#eval (-- both are Pi-shapes over the two incompatible-sorted domains, at a shared codomain sort
       Shape.Compat jM jM',
       Shape.hasType jM (.sort true), Shape.hasType jM' (.sort true),
       -- ... and the join
       Shape.hasType (Shape.join jM jM') (.sort true),
       -- the underlying reason: is `.bot` still typeable at the joined domain?
       Shape.hasType (.bot : Shape 2) (Shape.join cxA cxA'))

private theorem jM_wf : Shape.WF jM :=
  ⟨cxA_wf, by simp [jF, ShapeFun.WF, Shape.WF, Shape.Compat, Shape.join, Shape.LE.def]⟩

private theorem jM'_wf : Shape.WF jM' :=
  ⟨cxA'_wf, by simp [jF, ShapeFun.WF, Shape.WF, Shape.Compat, Shape.join, Shape.LE.def]⟩

/-- **`WShape.HasType.join` is false too.** `jM` and `jM'` are well-formed and compatible and
both are classified by `.sort true`, but their join is not. The mechanism is the same one that
refutes `IsType.common`, lifted one level: the two Pi-shapes' *domains* are `cxA` and `cxA'`,
which are compatible but share no sort, so the joined domain admits nothing -- in particular
`.bot` is no longer typeable at it, and `HasDom` fails for the joined family.

The shared codomain sort (`true` here) constrains the families' *values*, never their
*domains*, which is exactly why the shared `a` of the statement does not reach the obstruction. -/
private theorem j_refutes :
    ¬ ∀ {n : Nat} {m₁ m₂ a : WShape n},
        m₁.Compat m₂ → m₁.HasType a → m₂.HasType a → (m₁.join m₂).HasType a := by
  intro H
  have hC : WShape.Compat (⟨jM, jM_wf⟩ : WShape 3) ⟨jM', jM'_wf⟩ := by
    show Shape.Compat jM jM' = true; rfl
  have h1 : WShape.HasType (⟨jM, jM_wf⟩ : WShape 3) ⟨.sort true, trivial⟩ := by
    show Shape.hasType jM (.sort true) = true; rfl
  have h2 : WShape.HasType (⟨jM', jM'_wf⟩ : WShape 3) ⟨.sort true, trivial⟩ := by
    show Shape.hasType jM' (.sort true) = true; rfl
  have hbad := H hC h1 h2
  simp only [WShape.HasType, WShape.join_val hC] at hbad
  exact Bool.noConfusion hbad

/-! ### Pass 1: does the same witness refute `HasTypeLam.join` (the `go_lam` route)? -/
private def lB : ShapeFun 3 := [(.bot, .sort true)]
private def lF : ShapeFun 3 := [(.bot, jM)]
private def lF' : ShapeFun 3 := [(.bot, jM')]

/-! ### Pass 2: does `HasDom`'s `exists`-with-`le` escape hatch save `HasDom.join`? -/

#eval (-- pass 1: the lambda-family values are `jM` / `jM'`, joined at the shared codomain
       ShapeFun.Compat Shape.Compat lF lF',
       Shape.hasType jM (ShapeFun.app lB .bot),                 -- lF's value types
       Shape.hasType jM' (ShapeFun.app lB .bot),                -- lF''s value types
       Shape.hasType (Shape.join jM jM') (ShapeFun.app lB .bot),-- ... the join does not
       -- pass 2: HasDom's witness must itself carry the *joined* domain
       Shape.hasType (.bot : Shape 2) cxA,
       Shape.hasType (.bot : Shape 2) cxA',
       Shape.hasType (.bot : Shape 2) (Shape.join cxA cxA'))

/-- **Pass 1 -- `HasTypeLam.join` fails.** `ShapeFun.join` merges the two bot-keyed entries by
joining their *values*, so `HasTypeLam (lF.join lF') a lB` would have to give
`(jM.join jM').HasType (lB.app bot)`. The three facts below say both components type there and
the join does not, so `go_lam` does not survive either: **no `HasType` join is true.** -/
private theorem lam_join_fails :
    Shape.hasType jM (ShapeFun.app lB .bot) = true ∧
    Shape.hasType jM' (ShapeFun.app lB .bot) = true ∧
    Shape.hasType (Shape.join jM jM') (ShapeFun.app lB .bot) = false :=
  ⟨rfl, rfl, rfl⟩

/-- **Pass 2 -- `HasDom`'s escape hatch does not save `HasDom.join`.** `HasDom` may pick a
witness `x' <= x`, but that witness must still satisfy `x'.HasType a` at the **joined** domain.
Taking `f = f' = jF = [(bot, bot)]`, the only candidate is `bot` itself, and it does not type
at `cxA.join cxA'`. The `<=` relaxation is on the *key*, never on the *type*, so it cannot
absorb a failure that is about the type. -/
private theorem hasDom_escape_fails :
    Shape.hasType (.bot : Shape 2) cxA = true ∧
    Shape.hasType (.bot : Shape 2) cxA' = true ∧
    Shape.hasType (.bot : Shape 2) (Shape.join cxA cxA') = false :=
  ⟨rfl, rfl, rfl⟩

/-- **The refutation that forced section 7, and the regression test that it is closed.**

Before `HasTypeU.ctor` was gated to `.indTy true`, `HasTypeU.ctor : HasTypeU (.ctor c l)
(.indTy r)` fired at **every** `r`.  With `.indTy false` now denoting a `Prop`-valued
inductive, that made

    WShape.HasType.proofIrrel (ha : HasType a .prop) (hx : HasType x a) : x = .bot

FALSE, with `a := .indTy false`, `x := .ctor `Foo` []` at `n = 1`: both are `Shape.WF`
(`WF (.indTy _)` is `True`; `WF (.ctor c [])` is vacuous), `hasType x a` was `true`,
`hasType a .prop` is `true`, and `x` is not `.bot`.  That was the third of the three-way
tension's four faces to be refuted, and it left denying (i) -- section 7 -- as the only
remaining resolution.

The first clause below is the regression test: `.ctor` no longer types at `.indTy false`.
The second says the gating did not simply delete the `ctor` rule -- it still types at
`.indTy true`.  The third pins the `Prop`-ness of `.indTy false`, which is what makes the
old witness a witness at all. -/
private def piX : Shape 1 := .ctor `Foo []
private def piA : Shape 1 := .indTy false
private def piA' : Shape 1 := .indTy true

private theorem proofIrrel_gated :
    Shape.hasType piX piA = false ∧
    Shape.hasType piX piA' = true ∧
    Shape.hasType piA (Shape.prop (n := 1)) = true :=
  ⟨rfl, rfl, rfl⟩

/-- ... and the witness really was one: it is well-formed and is not `.bot`. -/
private theorem proofIrrel_witness_wf :
    piX ≠ (.bot : Shape 1) ∧
    Shape.WF piA ∧ (∀ x ∈ ([] : List (Shape 0)), Shape.WF x) :=
  ⟨nofun, trivial, nofun⟩

/-- **Section 7's route (beta) is REFUTED, at `Eq`.**

(beta) was: make `Pattern.WF` demand `rel = true` at constructor leaves, so a `Prop`-valued
inductive's iota-rule is simply not a `Pattern`.  Its premise was "the major premise is a
proof, `proofIrrel` gives it `.bot`, so the whole redex is `.bot` and the shape model does not
need the rule" -- PLAN.md's *small elimination* fact.

**`Eq` is a `Prop` that LARGE-eliminates**, so the premise does not hold for it.  `@Eq.rec`'s
motive is `Sort u_1`, not `Prop`; the term below is a `Nat`, and its iota-rule computes to
`7` by `rfl`.  The redex is not a proof, `proofIrrel` does not apply, and its shape is not
`.bot`.  Small elimination covers `Acc.rec` and `Quot.lift`-over-a-`Prop`; it does NOT cover
the subsingleton eliminators, and `Eq` is the one that started all of this.

The consequence is the failure mode that is worst to detect.  Under (beta),
`Params.pat_wf : Pat p r -> p.WF classify` plus `ParamsExtra.extra_pat` (every
`env.defeqs df` must be covered by some `Pat p r`) makes **`ParamsExtra` unsatisfiable for any
environment containing `Eq`** -- i.e. every real one, since `Eq` is in `stdPrelude`.  Nothing
in the tree would notice: there is no `ParamsExtra` instance, so every downstream result would
go silently vacuous.  `ParamsExtra`'s own docstring records that this project has already been
burned by exactly that once. -/
private theorem eq_large_eliminates :
    Eq.rec (motive := fun (b : Nat) (_ : (0:Nat) = b) => Nat) 7 (rfl : (0:Nat) = 0) = 7 := rfl

/-- **Section 7's route (gamma) is REFUTED too, and not by where a premise sits.**

(gamma) was: move `LE_Interp.const`'s `m'.HasType a` premise out of the way, so `Eq.refl`
could keep its `.ctor` shape without being classified by a `Prop`-valued inductive.

Moving it does not help, because `InterpTyped` demands the same classification independently:

    InterpTyped rho m M A := exists m' a, m <= m' /\ LE_Interp rho m' M /\
                             LE_Interp rho a A /\ m'.HasType a

and `strongSoundS`'s `const` case builds that packaging with the constructor's premise
LITERALLY as the `HasType` field (`.mk b3 (.const b1 b2 .rfl b4 b5 b6 b7) b5 b4` -- `b4`
appears twice).  Dropping the premise leaves nothing to put there; a probe that removed it
produced 36 errors and the one at that line has no repair, because the fact is not derivable
from anything else.

The underlying reason is this lemma, which does not mention `LE_Interp` at all: **no shape
both classifies a `.ctor` and is itself `Prop`-valued.**  So for `Eq.refl` there is no `a`
that can sit in `InterpTyped`'s slot at its natural shape, wherever the premise lives.

    => Section 7's residue is a design problem, not a repair.  (alpha) costs 107 instances
       plus a lemma that looks false under it; (beta) is refuted at `Eq` by
       `eq_large_eliminates`; (gamma) is refuted here. -/
private theorem ctor_not_prop_typed (a : Shape 1) (h : Shape.hasType piX a = true) :
    Shape.hasType a (Shape.prop (n := 1)) = false := by
  cases a <;> simp_all [piX, Shape.hasType, Shape.prop, Shape.sort]

end CounterexampleProbe

theorem WShape.HasType.join {m₁ m₂ a : WShape n} (hJ : m₁.Compat m₂)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : (m₁.join m₂).HasType a := by
  obtain ⟨m₁, wf₁⟩ := m₁; obtain ⟨m₂, wf₂⟩ := m₂; obtain ⟨a, wf'⟩ := a
  simp [HasType, WShape.join_val hJ, Compat] at h1 h2 hJ ⊢
  cases n with
  | zero =>
    cases m₂ with | bot => exact h1 | sort
    cases m₁ with | bot => exact h2 | sort
    simp only [Shape.Compat, decide_eq_true_eq] at hJ
    simpa only [Shape.join, hJ]
  | succ n
  have ih := @join n
  let rec go_dom {a a' : WShape n} {f f' : WShapeFun n}
      (hf : f.Compat f') (ha : a.Compat a')
      (h1 : WShape.HasDom f a) (h2 : WShape.HasDom f' a') :
      WShape.HasDom (f.join f') (a.join a') := by
    rw [WShape.HasDom.iff] at h1 h2 ⊢
    have hJa := WShape.Join.mk ha
    have hJf := WShapeFun.Join.mk hf
    intro x
    have ⟨x₁, a1, a2, a3⟩ := h1 x
    have ⟨x₂, b1, b2, b3⟩ := h2 x
    have hcx := Compat.iff.2 ⟨_, a1, b1⟩; have hjx := WShape.Join.mk hcx
    have ajt := ih ha a2.isType b2.isType
    have := ih hcx (.mono_r hJa.le.1 ajt a2) (.mono_r hJa.le.2 ajt b2)
    refine ⟨_, (hjx _).2 ⟨a1, b1⟩, this, ?_⟩
    refine (hJf.app_l x _).2 ⟨a3.trans ?_, b3.trans ?_⟩
    · exact (WShapeFun.app_mono_r hjx.le.1).trans (hJf.app_l _).le.1
    · exact (WShapeFun.app_mono_r hjx.le.2).trans (hJf.app_l _).le.2
  let rec go_pi {a a' : WShape n} {b b' : WShapeFun n} {r}
      (ha : a.Compat a') (hb : b.Compat b')
      (h1 : WShape.HasTypePi b a r) (h2 : WShape.HasTypePi b' a' r) :
      WShape.HasTypePi (b.join b') (a.join a') r := by
    rw [WShape.HasTypePi.iff'] at h1 h2 ⊢
    have hJa := WShape.Join.mk ha
    have hJb := WShapeFun.Join.mk hb
    refine ⟨go_dom hb ha h1.1 h2.1, fun x => ?_⟩
    have ⟨a1, a2, a3⟩ := Join.iff.1 (hJb.app_l x)
    exact ih a1 (h1.2 _) (h2.2 _) |>.mono_l a2 a3
  let rec go_lam {f f' : WShapeFun n} {a b} (hf : f.Compat f')
      (h1 : WShape.HasTypeLam f a b) (h2 : WShape.HasTypeLam f' a b) :
      WShape.HasTypeLam (f.join f') a b := by
    rw [WShape.HasTypeLam.iff'] at h1 h2 ⊢
    have := Join.iff.1 <| (join_self (x := a)).2 ⟨.rfl, .rfl⟩
    have ⟨_, hIs⟩ := h1.2.1.isType
    refine ⟨h1.1, go_dom hf .rfl h1.2.1 h2.2.1 |>.mono_r this.2.1 hIs, fun x => ?_⟩
    have hJf := WShapeFun.Join.mk hf
    have ⟨a1, a2, a3⟩ := Join.iff.1 (hJf.app_l x)
    exact ih a1 (h1.2.2 _) (h2.2.2 _) |>.mono_l a2 a3
  cases h1.unfold with
  | bot => exact h2
  | sort =>
    (cases m₂ with | bot => exact h1 | _) <;>
      simp only [Shape.Compat, decide_eq_true_eq, Bool.false_eq_true] at hJ
    simpa only [Shape.join, hJ]
  | forallE h1' =>
    (cases h2.unfold with | bot => exact h1 | forallE h2' | _) <;>
      simp only [Shape.Compat, Bool.false_eq_true, Bool.and_eq_true] at hJ
    have := go_pi (b := ⟨_, wf₁.2⟩) (b' := ⟨_, wf₂.2⟩)
      (a := ⟨_, wf₁.1⟩) (a' := ⟨_, wf₂.1⟩) hJ.1 hJ.2 h1' h2'
    rw [HasTypePi, WShape.join_val (by exact hJ.1), WShapeFun.join_val (by exact hJ.2)] at this
    exact .forallE this
  | lam h1' =>
    (cases h2.unfold with | bot => exact h1 | lam h2' | _) <;> simp only [Shape.Compat] at hJ
    have := go_lam (f := ⟨_, wf₁.1⟩) (f' := ⟨_, wf₂.1⟩)
      (a := ⟨_, wf'.1⟩) (b := ⟨_, wf'.2⟩) hJ h1' h2'
    rw [HasTypeLam, WShapeFun.join_val (by exact hJ)] at this
    exact .lam this
  | ctor =>
    (cases h2.unfold with | bot => exact h1 | ctor | _) <;>
      simp only [Shape.Compat, Bool.and_eq_true, decide_eq_true_eq] at hJ
    simp only [Shape.join, if_pos hJ.1]; exact Shape.HasType.unfold_iff.2 .ctor
  | indTy =>
    (cases h2.unfold with
      | bot => exact h1
      | indTy => simp only [Shape.join, if_pos rfl]; exact h1
      | _) <;>
      simp only [Shape.Compat, Bool.false_eq_true] at hJ

theorem WShape.HasDom.join {a a' : WShape n} {f f' : WShapeFun n} :
    f.Compat f' → a.Compat a' → HasDom f a → HasDom f' a' →
    HasDom (f.join f') (a.join a') := HasType.join.go_dom _ HasType.join
theorem WShape.HasTypePi.join {a a' : WShape n} {b b' : WShapeFun n} {r} :
    a.Compat a' → b.Compat b' → HasTypePi b a r → HasTypePi b' a' r →
    WShape.HasTypePi (b.join b') (a.join a') r := HasType.join.go_pi _ HasType.join
theorem WShape.HasTypeLam.join {f f' : WShapeFun n} {a b} :
    f.Compat f' → HasTypeLam f a b → HasTypeLam f' a b →
    WShape.HasTypeLam (f.join f') a b := HasType.join.go_lam _ HasType.join

theorem WShape.HasType.join' {m₁ m₂ m a : WShape n} (hJ : m₁.Join m₂ m)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : m.HasType a :=
  have ⟨a1, a2, a3⟩ := Join.iff.1 hJ
  h1.join a1 h2 |>.mono_l a2 a3

theorem WShape.HasDom.join' (h1 : HasDom f₁ a₁) (h2 : HasDom f₂ a₂)
    (hJ : WShapeFun.Join f₁ f₂ h') (hJa : WShape.Join a₁ a₂ a') : HasDom h' a' := by
  have ⟨a1, a2, a3⟩ := WShapeFun.Join.iff.1 hJ
  have ⟨b1, b2, b3⟩ := WShape.Join.iff.1 hJa
  have := h1.join a1 b1 h2 |>.mono_l a2 a3
  have ⟨w, hIs⟩ := WShape.HasDom.isType this
  exact this.mono_r b2 <| WShape.HasType.mono_l b2 b3 hIs

def TShape.HasType (x y : TShape) : Prop := (x.2.lift (max x.1 y.1)).HasType (y.2.lift _)

/-- `TShape`-level counterpart of `WShape.IsType`: `a` classifies terms. Replaces the former
`HasType a .type`, which forced the sort boolean to `true`. -/
def TShape.IsType (a : TShape) : Prop := ∃ r, TShape.HasType a (.sort r)

theorem TShape.HasType.def {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    x.HasType y ↔ (x.2.lift m).HasType (y.2.lift m) := by
  refine (WShape.HasType.lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.HasType.T_iff {x y : WShape n} : x.T.HasType y.T ↔ x.HasType y := by
  refine (TShape.HasType.def (x := x.T) (y := y.T) (Nat.le_refl _) (Nat.le_refl _)).trans ?_
  simp [WShape.HasType, WShape.lift_self]

theorem WShape.HasType.T {x y : WShape n} : x.HasType y → x.T.HasType y.T := T_iff.2

theorem TShape.HasType.bot_r (H : HasType x .bot) : x ≤ .bot := by
  simp only [TShape.HasType, bot, WShape.lift_bot] at H
  have h := WShape.HasType.bot_r H
  simp only [TShape.LE.def', bot, WShape.lift_bot]
  exact (h : x.2.lift _ = .bot) ▸ WShape.LE.rfl

theorem TShape.HasType.mono_r {m a a' : TShape} (ha : a ≤ a')
    (h1 : HasType a' (.sort r)) (h2 : HasType m a) : HasType m a' := by
  let k := max (max m.1 a.1) a'.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 h1
  have h2 := (TShape.HasType.def hk.1.1 hk.1.2).1 h2
  have ha := (TShape.LE.def hk.1.2 hk.2).1 ha
  exact (TShape.HasType.def hk.1.1 hk.2).2 (h1.mono_r ha h2)

theorem TShape.HasType.bot : HasType x (.sort r) → HasType .bot x := by
  rw [TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _),
    TShape.HasType.def (Nat.zero_le _) (Nat.le_refl _)]
  simp [sort]; exact .bot

theorem TShape.HasType.bot' {r} : HasType x (.sort r) → HasType .bot x := .bot

theorem TShape.HasType.sort : HasType (.sort r) .type := by
  simp [HasType, TShape.sort, TShape.type, WShape.lift_sort, WShape.HasType]
  exact WShape.HasType.sort

theorem TShape.HasType.join' (hJ : Join m₁ m₂ m)
    (h1 : HasType m₁ a) (h2 : HasType m₂ a) : HasType m a := by
  let k := max (max m₁.1 m₂.1) (max m.1 a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.1.1 hk.2.2).1 h1
  have h2 := (TShape.HasType.def hk.1.2 hk.2.2).1 h2
  have hJ := (TShape.Join.def hk.1.1 hk.1.2 hk.2.1).1 hJ
  exact (TShape.HasType.def hk.2.1 hk.2.2).2 (h1.join' hJ h2)

theorem TShape.HasType.bot_r' (ha : a ≤ .bot) (H : HasType x a) : x ≤ .bot :=
  (mono_r (r := true) ha (.bot' .sort) H).bot_r

nonrec theorem TShape.HasType.isType (H : HasType m a) : a.IsType :=
  let k := max m.1 a.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  have ⟨r, hr⟩ := WShape.HasType.isType H
  ⟨r, (TShape.HasType.def hk.2 (Nat.zero_le _)).2 hr⟩

inductive LE_Forall {n} : TShape → WShape n → WShapeFun n → Prop where
  | bot : a ≤ .bot → LE_Forall a b f
  | forallE : b'.T ≤ b.T → TShapeFun.LE (n := m) f' f →
    LE_Forall (WShape.T (n := m+1) (.forallE b' f')) b f

theorem TShape.LE.le_forall (ha : a ≤ WShape.T (n := n+1) (.forallE b f)) :
    LE_Forall a b f := by
  by_cases h : a ≤ .bot; · exact .bot h
  obtain ⟨an, aw⟩ := a
  cases an with
  | zero =>
    exfalso; apply h; rw [TShape.le_bot]
    have hle := (TShape.LE.def (Nat.zero_le _) (Nat.le_refl _)).1 ha
    have hle_raw : (aw.lift _).1 ≤ ((WShape.forallE b f).lift _).1 := hle
    rw [WShape.lift_val (Nat.zero_le _), WShape.lift_val (Nat.le_refl _)] at hle_raw
    obtain ⟨val, wf⟩ := aw
    cases val with | bot => rfl | sort r
    simp [Shape.lift, WShape.forallE, Shape.LE.def] at hle_raw
  | succ m =>
    have hle := (TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left m n))
        (Nat.succ_le_succ (Nat.le_max_right m n))).1 ha
    have hle_raw : (aw.lift _).1 ≤ ((WShape.forallE b f).lift _).1 := hle
    rw [WShape.lift_val (Nat.succ_le_succ (Nat.le_max_left m n)),
        WShape.lift_val (Nat.succ_le_succ (Nat.le_max_right m n))] at hle_raw
    simp only [WShape.forallE, Shape.lift] at hle_raw
    obtain ⟨val, wf⟩ := aw
    cases val with
    | bot => exfalso; apply h; rw [TShape.le_bot]; rfl
    | forallE b' f' =>
      simp [Shape.lift, Shape.LE.def] at hle_raw
      let b'w : WShape m := ⟨b', wf.1⟩; let f'w : WShapeFun m := ⟨f', wf.2⟩
      have le₁ := Nat.le_max_left m n; have le₂ := Nat.le_max_right m n
      refine .forallE
        ((TShape.LE.def le₁ le₂).2 (?_ : (b'w.lift _).1 ≤ (b.lift _).1))
        ((TShapeFun.LE.def le₁ le₂).2 (?_ : (f'w.lift _).1.LE (f.lift _).1))
      · rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact hle_raw.1
      · rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact hle_raw.2
    | _ => simp [Shape.lift, Shape.LE.def] at hle_raw

def TShape.HasTypeLam (f : WShapeFun n) (a : WShape m) (b : WShapeFun m) :=
  WShape.HasTypeLam (f.lift (max n m)) (a.lift (max n m)) (b.lift (max n m))

theorem TShape.HasTypeLam.def (le₁ : n ≤ k) (le₂ : m ≤ k) :
    HasTypeLam (n := n) (m := m) f a b ↔
    WShape.HasTypeLam (f.lift k) (a.lift k) (b.lift k) := by
  rw [TShape.HasTypeLam, ← WShape.HasTypeLam.lift (Nat.max_le.2 ⟨le₁, le₂⟩),
    WShapeFun.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..)),
    WShapeFun.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShape.HasType.ty_forallE_inv
    {x : TShape} (H : x.HasType (WShape.T (n := m+1) (.forallE b f))) :
    x = .bot ∨ ∃ n g, x = WShape.T (n := n+1) (.lam' g) ∧ TShape.HasTypeLam g b f := by
  refine have le₁ := Nat.le_succ_of_le (Nat.le_max_left ..)
    have le₂ := Nat.succ_le_succ (Nat.le_max_right ..)
    have H := (TShape.HasType.def le₁ le₂).1 H; ?_
  rw [WShape.lift_forallE (Nat.le_of_succ_le_succ le₂)] at H
  have ⟨g, hg, htl⟩ := WShape.HasType.forallE_inv H
  obtain ⟨_|n, x⟩ := x
  · unfold WShape.lam' at hg; split at hg
    · obtain ⟨⟨⟩, _⟩ := x <;> cases congrArg (·.1) hg
    · dsimp at le₁; cases (WShape.lift_eq_bot le₁).1 hg; exact .inl rfl
  refine .inr ⟨n, ?_⟩; dsimp at *
  obtain ⟨rfl, h⟩ | ⟨g, rfl, rfl⟩ := WShape.lift_eq_lam' (Nat.le_of_succ_le_succ le₁) hg
  · refine ⟨.bot, by simp, ?_⟩
    rw [HasTypeLam, WShapeFun.lift_bot, ← WShapeFun.lift_bot,
      WShape.HasTypeLam.lift (Nat.le_max_right ..), WShape.HasTypeLam.bot]
    have ⟨_, hH⟩ := WShape.HasType.bot_iff.1 H
    obtain ⟨_, h, _⟩ := WShape.HasType.forallE_l.1 hH
    exact ⟨_, (WShape.HasTypePi.lift (Nat.le_of_succ_le_succ le₂)).1 h⟩
  · exact ⟨_, rfl, (HasTypeLam.def (by omega) (by omega)).2 htl⟩

theorem TShape.HasType.mono_l {m a : TShape}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a := by
  let k := max (max m.1 a.1) m'.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have H := (TShape.HasType.def hk.1.1 hk.1.2).1 H
  have hm1 := (TShape.LE.def hk.1.1 hk.2).1 hm1
  have hm2 := (TShape.LE.def hk.2 hk.1.1).1 hm2
  exact (TShape.HasType.def hk.2 hk.1.2).2 (H.mono_l hm1 hm2)

theorem TShape.HasType.sort_T : HasType (WShape.T (n := n) (.sort r)) .type :=
  mono_l TShape.sort_eqv.2 TShape.sort_eqv.1 .sort

theorem TShape.HasType.sort_r {x : WShape n} : x.T.HasType (.sort r) ↔ x.HasType (.sort r) :=
  .trans ⟨mono_r TShape.sort_eqv.2 .sort_T, mono_r TShape.sort_eqv.1 .sort⟩ WShape.HasType.T_iff

theorem TShape.HasType.bot_T (H : HasType x (.sort r)) : HasType (WShape.T (n := n) .bot) x :=
  H.bot.mono_l bot_eqv.2 bot_eqv.1
/-- `TShape` counterpart of `WShape.HasType.bot_bot`. -/
theorem TShape.HasType.bot_bot : HasType (WShape.T (n := n) .bot) .bot :=
  bot_T (r := true) (bot (r := true) sort)

theorem TShape.HasType.bot_T' {r} (H : HasType x (.sort r)) :
    HasType (WShape.T (n := n) .bot) x := H.bot_T

theorem TShape.HasType.join {m₁ m₂ a : TShape} (hJ : m₁.Compat m₂)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : (m₁.join m₂).HasType a := by
  let k := max (max m₁.1 m₂.1) a.1
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.1.1 hk.2).1 h1
  have h2 := (TShape.HasType.def hk.1.2 hk.2).1 h2
  have hJ := (TShape.Compat.def hk.1.1 hk.1.2).1 hJ
  have := TShape.lift_join hk.1.1 hk.1.2 ▸ h1.join hJ h2
  exact (TShape.HasType.def (Nat.max_le.2 hk.1) hk.2).1 this

theorem WShape.HasType.proofIrrel
    (ha : HasType (n := n) a .prop) (hx : HasType x a) : x = .bot := by
  cases n with | zero => cases ha.unfold; exact hx.bot_r | succ n
  cases ha.unfold with
  | bot => exact hx.bot_r
  -- Section 7: `.prop = .sort false` now admits `a = .indTy false`, and only `.bot` is
  -- classified by it.  Without the gating this case is a counterexample, not a proof.
  | indTy => exact hx.indTy_false_bot
  | @forallE _ b a _ ha
  generalize eq : WShape.forallE .. = t at hx
  cases hx.unfold with | bot => rfl | @lam _ f a' b' hx' => ?_ | _ => cases eq
  obtain ⟨rfl, rfl⟩ : a = a' ∧ b = b' := by
    cases a'; cases b'; cases congrArg (·.1) eq; exact ⟨rfl, rfl⟩
  unfold lam'; split <;> [rename_i hf; rfl]
  obtain ⟨⟨x, y⟩, h1, h2⟩ := hf; have ⟨hx, hy⟩ := f.2.2 _ h1; change (⟨x,hx⟩, ⟨y,hy⟩) ∈ f at h1
  have ⟨x', a1, a2, a3⟩ := WShape.HasDom.iff.1 hx'.2.1 ⟨x, hx⟩
  have hfx := (WShape.HasTypeLam.iff.1 hx').2.2 x' a2
  have hba := (WShape.HasTypePi.iff.1 ha).2 x' a2
  cases h2 <| (f.app_of_mem h1).2.trans <| a3.trans <| le_bot.2 <| proofIrrel hba hfx

theorem TShape.HasType.proofIrrel
    (ha : HasType a (.sort false)) (hx : HasType x a) : x ≤ .bot := by
  let k := max x.1 a.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  have ha' := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 ha
  have hx' := (TShape.HasType.def hk.1 hk.2).1 hx
  simp [TShape.sort] at ha'
  have := ha'.proofIrrel hx'
  rw [TShape.LE.def hk.1 (Nat.zero_le _)]
  simp [TShape.bot, WShape.lift_bot, this]

theorem WShape.HasType.retype (ha : HasType (n := n) a (.sort r))
    (ha' : HasType a' (.sort r')) (le : a ≤ a') : HasType a (.sort r') := by
  cases n with
  | zero =>
    cases ha.unfold with
    | bot => exact .bot .sort
    | sort => exact sort_le.1 le ▸ ha'
  | succ n
  cases ha.unfold with
  | bot => exact .bot .sort
  | sort => exact sort_le.1 le ▸ ha'
  | indTy => exact (show a' = .indTy r from Subtype.ext (Shape.indTy_le.1 le)) ▸ ha'
  | forallE Ha
  obtain ⟨_, _, le₁, le₂, rfl⟩ := WShape.forallE_le.1 le
  have ⟨H1, H2⟩ := HasTypePi.iff'.1 Ha
  obtain ⟨_, Ha', ⟨⟩⟩ := forallE_l.1 ha'
  refine .forallE <| HasTypePi.iff'.2 ⟨H1, fun x => ?_⟩
  exact retype (H2 _) ((HasTypePi.iff'.1 Ha').2 x) (WShapeFun.app_mono_l le₂ _)

theorem TShape.HasType.retype (ha : HasType a (.sort r))
    (ha' : HasType a' (.sort r')) (le : a ≤ a') : HasType a (.sort r') := by
  let k := max a.1 a'.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  have ha := (TShape.HasType.def hk.1 (Nat.zero_le _)).1 ha
  have ha' := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 ha'
  exact (TShape.HasType.def hk.1 (Nat.zero_le _)).2 <| ha.retype ha' le

/-- **Costing `join_sort`: `Compat` alone already pins the sort EVERYWHERE EXCEPT
`forallE`/`forallE`.**  `cx_refutes` shows the `Compat`-only form is false; this says the
failure is confined to exactly ONE of the thirty-six constructor pairs.  A `LogRel`-relative
version therefore needs new information at that one case only, and `ValTyPi2` supplies it --
see the banner, section 4.  (At `n = 0` there is no `.forallE`, so the statement is
unconditional there and is not repeated.) -/
theorem Shape.IsType.common_of_not_forallE {n} {a a' : Shape (n+1)} {r r'}
    (hC : Shape.Compat a a' = true) (hr : HasType a (.sort r)) (hr' : HasType a' (.sort r'))
    (hne : ∀ (b : Shape n) f (b' : Shape n) f', ¬(a = .forallE b f ∧ a' = .forallE b' f')) :
    ∃ r, HasType a (.sort r) ∧ HasType a' (.sort r) := by
  cases a <;> cases a' <;>
    first
      | exact ⟨_, Shape.HasType.sort_bot, hr'⟩
      | exact ⟨_, hr, Shape.HasType.sort_bot⟩
      | exact absurd ⟨rfl, rfl⟩ (hne _ _ _ _)
      | simp_all [Shape.Compat, HasType, hasType, Shape.sort, Shape.bot]

/-- **The true form of `IsType.common`.** `Compat a a'` -- i.e. "*some* upper bound exists" --
is not enough (`cx_refutes`); a **classified** upper bound is, and the proof is three lines of
`HasType.retype`.  This is the fact the join family actually needs, and the whole question is
whether a call site can produce the `z`. -/
theorem WShape.IsType.common_of_le {a a' z : WShape n}
    (le1 : a ≤ z) (le2 : a' ≤ z) (hz : z.IsType) (h : a.IsType) (h' : a'.IsType) :
    ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r) := by
  obtain ⟨r, hr⟩ := hz
  obtain ⟨_, h1⟩ := h
  obtain ⟨_, h2⟩ := h'
  exact ⟨r, WShape.HasType.retype h1 hr le1, WShape.HasType.retype h2 hr le2⟩

/-! ### The `bvar` test: does `j_refutes`' witness survive a TYPED valuation? -/

private def cxAW : WShape 2 := ⟨cxA, cxA_wf⟩
private def cxA'W : WShape 2 := ⟨cxA', cxA'_wf⟩
private def jFW : WShapeFun 2 := ⟨jF, jM_wf.2⟩

/-- **No, it does not -- and this is what makes the strengthened induction viable.**

`le_interp_common_fails` plants `cxA`/`cxA'` in a valuation by taking `rho i` to be an upper
bound of the two, which `Compat` guarantees exists.  `j_refutes` does the same one level up
for `jM`/`jM'`.  Both witnesses need `rho i` to be an upper bound of a pair that shares no
sort -- and **no such upper bound is typed**:

    z above both is a `.forallE z1 z2` whose domain `z1` is above BOTH `cxA` and `cxA'`
    (`forallE_le`); `z.IsType` unfolds to `HasTypePi z2 z1 r`, whose `HasDom z2 z1` gives
    `z1.IsType` by `HasDom.isType`; and then `IsType.common_of_le` hands `cxA` and `cxA'` a
    common sort, which `cx_refutes` says they do not have.

So a valuation whose entries are typed -- which is exactly what `Valuation.Fits.cons`
produces, via `x.HasType a` -- cannot host either witness.  The `bvar` case of a strengthened
`compat_join` is therefore not blocked the way the shape-level lemmas were; what it needs is a
typed-valuation hypothesis, not a new idea. -/
private theorem jM_no_typed_bound :
    ¬ ∃ z : WShape 3, WShape.forallE cxAW jFW ≤ z ∧ WShape.forallE cxA'W jFW ≤ z ∧ z.IsType := by
  rintro ⟨z, le1, le2, hz⟩
  obtain ⟨a1, f1, hle1, -, rfl⟩ := WShape.forallE_le.1 le1
  obtain ⟨a2, f2, hle2, -, heq⟩ := WShape.forallE_le.1 le2
  have hle2' : cxA'W ≤ a1 := by
    injection congrArg (·.1) heq with e1 _
    exact (Subtype.ext e1.symm : a2 = a1) ▸ hle2
  obtain ⟨r, hr⟩ := hz
  obtain ⟨r', hpi, -⟩ := WShape.HasType.forallE_l.1 hr
  have ha1 : a1.IsType := (WShape.HasTypePi.iff.1 hpi).1.isType
  obtain ⟨rr, h1, h2⟩ := WShape.IsType.common_of_le hle1 hle2' ha1
    ⟨false, by show Shape.hasType cxA (Shape.sort false) = true; rfl⟩
    ⟨true, by show Shape.hasType cxA' (Shape.sort true) = true; rfl⟩
  simp only [WShape.HasType, WShape.sort] at h1 h2
  cases rr
  · exact Bool.noConfusion h2
  · exact Bool.noConfusion h1

/-- **THE OPEN SPOT OF BANNER SECTION 15, CLOSED -- NEGATIVELY.**

`go_dom`'s inner recursive call fails EVEN WITH `ajt` (the joined type being a type) in hand.
The witness is `j_refutes`'s own: `x₁ := jM`, `x₂ := jM'`, `a = a' := .sort true`.  All of
`go_dom`'s locally available data is satisfied -- the subjects are compatible, the two types
are compatible, each subject has its type, and the join of the types IS a type -- and the
conclusion is still false.

Read together with `jM_no_typed_bound` (that same pair has NO typed common upper bound) this
says exactly where the tower is entangled: the inner call needs a TYPED BOUND FOR `x₁, x₂`,
and `HasDom.iff`'s `∀ x` is arbitrary and carries no typedness.  A top-level typed-bound
hypothesis does NOT descend to it.

So the base does not stand alone.  Repairing it means `HasDom` itself carrying typedness --
a change to a DEFINITION, not to a proof.  Not done here: weakening a definition to make a
proof go through is the move this project forbids, and this one belongs to the abstract spec. -/
private theorem go_dom_inner_fails :
    ¬ ∀ {n : Nat} {x₁ x₂ a a' : WShape n},
        x₁.Compat x₂ → a.Compat a' → x₁.HasType a → x₂.HasType a' →
        (a.join a').IsType → (x₁.join x₂).HasType (a.join a') := by
  intro H
  have hC : WShape.Compat (⟨jM, jM_wf⟩ : WShape 3) ⟨jM', jM'_wf⟩ := by
    show Shape.Compat jM jM' = true; rfl
  have hCa : WShape.Compat (⟨.sort true, trivial⟩ : WShape 3) ⟨.sort true, trivial⟩ := by
    show Shape.Compat (Shape.sort true) (Shape.sort true) = true; rfl
  have h1 : WShape.HasType (⟨jM, jM_wf⟩ : WShape 3) ⟨.sort true, trivial⟩ := by
    show Shape.hasType jM (.sort true) = true; rfl
  have h2 : WShape.HasType (⟨jM', jM'_wf⟩ : WShape 3) ⟨.sort true, trivial⟩ := by
    show Shape.hasType jM' (.sort true) = true; rfl
  have hIs : (WShape.join (⟨.sort true, trivial⟩ : WShape 3) ⟨.sort true, trivial⟩).IsType := by
    refine ⟨true, ?_⟩
    simp only [WShape.HasType, WShape.join_val hCa]
    show Shape.hasType (Shape.join (Shape.sort true) (Shape.sort true)) (Shape.sort true) = true
    rfl
  have hbad := H hC hCa h1 h2 hIs
  simp only [WShape.HasType, WShape.join_val hC, WShape.join_val hCa] at hbad
  exact Bool.noConfusion hbad

/-- **`jM_no_typed_bound` generalized off its witness.**  A typed common upper bound forces the
two domains to share a sort -- so it kills the ENTIRE `j_refutes` counterexample family, not
just the one shape, at the shape layer, with no `LE_Interp` anywhere.

This is the fact `go_dom` is missing at its `ajt` line, where the deleted-as-false
`WShape.IsType.common` used to sit.  Supplied by: `WShape.IsType.common_of_le`. -/
theorem WShape.forallE_common_of_typed_bound {n} {a₁ a₂ : WShape n} {f₁ f₂ : WShapeFun n}
    {z : WShape (n+1)} {r₀ : Bool}
    (h1 : (WShape.forallE a₁ f₁).HasType (WShape.sort r₀))
    (h2 : (WShape.forallE a₂ f₂).HasType (WShape.sort r₀))
    (hz1 : WShape.forallE a₁ f₁ ≤ z) (hz2 : WShape.forallE a₂ f₂ ≤ z) (hz : z.IsType) :
    ∃ r, a₁.HasType (WShape.sort r) ∧ a₂.HasType (WShape.sort r) := by
  obtain ⟨b1, g1, hle1, -, rfl⟩ := WShape.forallE_le.1 hz1
  obtain ⟨b2, g2, hle2, -, heq⟩ := WShape.forallE_le.1 hz2
  have hle2' : a₂ ≤ b1 := by
    injection congrArg (·.1) heq with e1 _
    exact (Subtype.ext e1.symm : b2 = b1) ▸ hle2
  obtain ⟨r, hr⟩ := hz
  obtain ⟨r', hpi, -⟩ := WShape.HasType.forallE_l.1 hr
  have hb1 : b1.IsType := (WShape.HasTypePi.iff.1 hpi).1.isType
  obtain ⟨p1, hp1, -⟩ := WShape.HasType.forallE_l.1 h1
  obtain ⟨p2, hp2, -⟩ := WShape.HasType.forallE_l.1 h2
  exact WShape.IsType.common_of_le hle1 hle2' hb1
    (WShape.HasTypePi.iff.1 hp1).1.isType (WShape.HasTypePi.iff.1 hp2).1.isType

theorem WShape.HasDom.single :
    HasDom (WShapeFun.single x y) a ↔ x.HasType a ∨ y ≤ .bot ∧ a.IsType := by
  simp [HasDom.def, WShapeFun.mem_single]
  refine ⟨fun H => ?_, ?_⟩
  · obtain ⟨x, y, ⟨rfl, rfl⟩ | ⟨h, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ (.inl ⟨rfl, rfl⟩)
    · exact .inl h4
    · exact .inr ⟨h3, h4.isType⟩
  · rintro H x y (⟨rfl, rfl⟩ | ⟨h, rfl, rfl⟩)
    · obtain h | ⟨h1, h2⟩ := H
      · exact ⟨_, _, .inl ⟨rfl, rfl⟩, .rfl, .rfl, h⟩
      · by_cases hx : x ≤ .bot
        · exact ⟨_, _, .inl ⟨rfl, rfl⟩, .rfl, .rfl, le_bot.1 hx ▸ HasType.bot_iff.2 h2⟩
        · exact ⟨_, _, .inr ⟨hx, rfl, rfl⟩, bot_le, h1, HasType.bot_iff.2 h2⟩
    · refine ⟨_, _, .inr ⟨h, rfl, rfl⟩, .rfl, .rfl, HasType.bot_iff.2 ?_⟩
      obtain h | ⟨_, h⟩ := H <;> [exact h.isType; exact h]

theorem WShape.HasDom.mono {r} (le : a ≤ a') (h : a'.HasType (.sort r)) (H : HasDom f a) :
    HasDom f a' :=
  HasDom.def.2 fun x y hm => let ⟨x', y', h1, h2, h3, h4⟩ := HasDom.def.1 H x y hm
    ⟨x', y', h1, h2, h3, .mono_r le h h4⟩

def Valuation := Nat → TShape

def Valuation.nil : Valuation := fun _ => ⟨0, .bot⟩
def Valuation.push (ρ : Valuation) (u : TShape) : Valuation
  | 0 => u
  | n+1 => ρ n

def Valuation.LE (ρ ρ' : Valuation) : Prop := ∀ n, ρ n ≤ ρ' n

theorem Valuation.LE.rfl {ρ : Valuation} : ρ.LE ρ := fun _ => .rfl

theorem Valuation.LE.push {ρ ρ' : Valuation} :
    (ρ.push a).LE (ρ'.push a') ↔ ρ.LE ρ' ∧ a ≤ a' :=
  ⟨fun H => ⟨fun _ => H (_+1), H 0⟩, fun ⟨H1, H2⟩ => fun | 0 => H2 | _+1 => H1 _⟩

/-- Two valuations are compatible if their entries are compatible at each index
(after lifting to a common level). -/
def Valuation.Compat (ρ₁ ρ₂ : Valuation) : Prop := ∀ i, (ρ₁ i).Compat (ρ₂ i)

/-- Pointwise join of two valuations. Each entry is lifted to a common level and joined. -/
def Valuation.join (ρ₁ ρ₂ : Valuation) : Valuation := fun i => (ρ₁ i).join (ρ₂ i)

theorem Valuation.Compat.le_join {ρ₁ ρ₂ : Valuation}
    (hc : ρ₁.Compat ρ₂) : ρ₁.LE (ρ₁.join ρ₂) ∧ ρ₂.LE (ρ₁.join ρ₂) :=
  ⟨fun i => (TShape.Join.mk (hc i)).le.1, fun i => (TShape.Join.mk (hc i)).le.2⟩

/-! ## `MArg` -- the matched-argument record  (banner section 12, group A)

`LE_Interp.Matches` indexes its arguments by their SHAPES, and `Matches.unique` recovers the
matched constructor and its sub-arguments back out of the shape at an `app` position.  That is
the double duty section 7 breaks: a `Prop`-valued head must get shape `.bot`, and then the
recovery is gone (`toy_unique_fails`).  `MArg` separates the two -- it records the match, and
the shape is read off it by `toShape`, free to collapse.  `toy_unique_of_record` is the check
that this is sufficient.

Written in `Shape`'s own style, as a `def` recursing on the level, so that the nested list in
the `ctor` case needs no well-founded recursion.  There is no `ctor` at level `0`: `Matches.app`
concludes at `n+1`. -/
def MArg : Nat → Type
  | 0 => WShape 0
  | n+1 => WShape (n+1) ⊕ Name × List (MArg n)

/-- A `var` position: a bare argument shape. -/
@[match_pattern] def MArg.shape : ∀ {n}, WShape n → MArg n
  | 0, x => x
  | _+1, x => .inl x

/-- An `app` position: the matched constructor and its own argument records. -/
@[match_pattern] def MArg.ctor {n} (c : Name) (l : List (MArg n)) : MArg (n+1) := .inr (c, l)

/-- The shape a record denotes.  This is the only place `WShape.ctor'` is applied to a matched
argument list, so it is the single point at which a `Prop`-valued head could be made to
collapse -- without `Matches` losing anything, because the record is the index. -/
def MArg.toShape : ∀ {n}, MArg n → WShape n
  | 0, x => x
  | _+1, .inl x => x
  | _+1, .inr (c, l) => WShape.ctor' c (l.map toShape).reverse

def MArg.lift : ∀ {n}, (m : Nat) → MArg n → MArg m
  | 0, m, x => .shape (WShape.lift m x)
  | _+1, 0, x => (MArg.toShape x).lift 0
  | _+1, _+1, .inl x => .inl (x.lift _)
  | _+1, _+1, .inr (c, l) => .inr (c, l.map (lift _))

/-- Order.  Aligned only: `Matches.mono_l` relates two matches of the SAME pattern, so a `var`
position is never compared with an `app` one. -/
def MArg.ble : ∀ {n}, MArg n → MArg n → Bool
  | 0, x, y => Shape.ble x.1 y.1
  | _+1, .inl x, .inl y => Shape.ble x.1 y.1
  | _+1, .inr (c, l), .inr (c', l') => c == c' && l.Forall₂ (ble · ·) l'
  | _+1, _, _ => false

def MArg.LE (x y : MArg n) : Prop := x.ble y
instance : LE (MArg n) := ⟨MArg.LE⟩

/-- Compatibility.  **Total**, unlike `join`: `Matches.matches_inter` relates matches of two
DIFFERENT patterns, so a `var` position genuinely can meet an `app` one.  The mixed case falls
back to the denoted shapes. -/
def MArg.Compat : ∀ {n}, MArg n → MArg n → Bool
  | 0, x, y => Shape.Compat x.1 y.1
  | _+1, .inl x, .inl y => Shape.Compat x.1 y.1
  | _+1, .inr (c, l), .inr (c', l') => c == c' && l.Forall₂ (Compat · ·) l'
  | _+1, x, y => Shape.Compat (MArg.toShape x).1 (MArg.toShape y).1

/-- Join.  **Partial**: only ever applied to pattern-aligned pairs (`Matches.compat_join`
relates two matches of the same pattern), so the mixed and mismatched cases go to `.bot`
rather than being given a meaning they would not have. -/
def MArg.join : ∀ {n}, MArg n → MArg n → MArg n
  | 0, x, y => WShape.join x y
  | _+1, .inl x, .inl y => .inl (WShape.join x y)
  | _+1, .inr (c, l), .inr (c', l') =>
    if c = c' then .inr (c, l.zipWith join l')
    else .shape (WShape.join (MArg.toShape (.inr (c, l))) (MArg.toShape (.inr (c', l'))))
  | _+1, x, y => .shape (WShape.join (MArg.toShape x) (MArg.toShape y))

/-! ### Row 6: `toShape` is a homomorphism

These four are exactly what the consumer rows need: `Matches.mono_l` wants monotonicity,
`matches_inter` wants `Compat`, `compat_join` wants the join equation, and the two `lift`
lemmas want the lift equation.  Nothing else about `MArg` is used downstream. -/

@[simp] theorem MArg.toShape_shape {n} {x : WShape n} : (MArg.shape x).toShape = x := by
  cases n <;> rfl

theorem MArg.toShape_ctor {n} {c} {l : List (MArg n)} :
    (MArg.ctor c l).toShape = WShape.ctor' c (l.map toShape).reverse := rfl

theorem MArg.toShape_lift : ∀ {n m}, n ≤ m → ∀ x : MArg n,
    (x.lift m).toShape = (x.toShape).lift m
  | 0, _, _, _ => by simp [lift, toShape]
  | _+1, _+1, _, .inl _ => rfl
  | n+1, m+1, le, .inr (c, l) => by
    show WShape.ctor' c (((l.map (lift m)).map toShape).reverse)
        = WShape.lift (m+1) (WShape.ctor' c ((l.map toShape).reverse))
    rw [WShape.lift_ctor' (Nat.le_of_succ_le_succ le)]
    congr 1
    simp only [List.map_map, List.map_reverse]
    congr 1
    exact List.map_congr_left fun a _ => toShape_lift (Nat.le_of_succ_le_succ le) a

theorem MArg.toShape_mono : ∀ {n} {x y : MArg n}, x ≤ y → x.toShape ≤ y.toShape
  | 0, _, _, h => h
  | _+1, .inl _, .inl _, h => h
  | _+1, .inr (c, l), .inr (c', l'), h => by
    have h' : (c == c' && decide (l.Forall₂ (fun a b => ble a b = true) l')) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
    obtain ⟨rfl, hl⟩ := h'
    refine WShape.ctor'_le_ctor' (List.Forall₂.reverse.2 ?_)
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 ?_)
    exact hl.imp fun _ _ hxy => toShape_mono hxy

theorem MArg.toShape_compat : ∀ {n} {x y : MArg n}, x.Compat y → x.toShape.Compat y.toShape
  | 0, _, _, h => h
  | _+1, .inl _, .inl _, h => h
  | _+1, .inl _, .inr _, h => h
  | _+1, .inr _, .inl _, h => h
  | _+1, .inr (c, l), .inr (c', l'), h => by
    have h' : (c == c' && decide (l.Forall₂ (fun a b => Compat a b = true) l')) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
    obtain ⟨rfl, hl⟩ := h'
    refine WShape.Compat.ctor'_ctor' (List.Forall₂.reverse.2 ?_)
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 ?_)
    exact hl.imp fun _ _ hxy => toShape_compat hxy

theorem MArg.toShape_join : ∀ {n} {x y : MArg n}, x.Compat y →
    (x.join y).toShape = x.toShape.join y.toShape
  | 0, _, _, _ => rfl
  | _+1, .inl _, .inl _, _ => rfl
  | _+1, .inl _, .inr _, _ => rfl
  | _+1, .inr _, .inl _, _ => rfl
  | n+1, .inr (c, l), .inr (c', l'), h => by
    have h' : (c == c' && decide (l.Forall₂ (fun a b => Compat a b = true) l')) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
    obtain ⟨rfl, hl⟩ := h'
    have key : ∀ {l l' : List (MArg n)}, List.Forall₂ (fun a b => Compat a b = true) l l' →
        (l.zipWith join l').map toShape
          = (l.map toShape).zipWith WShape.join (l'.map toShape) := by
      intro l l' hh
      induction hh with
      | nil => rfl
      | cons hx _ ih => simp only [List.zipWith_cons_cons, List.map_cons, toShape_join hx, ih]
    have hcm : List.Forall₂ WShape.Compat (l.map toShape) (l'.map toShape) :=
      List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (hl.imp fun _ _ => toShape_compat))
    show (MArg.join (MArg.ctor c l) (MArg.ctor c l')).toShape
        = (MArg.ctor c l).toShape.join (MArg.ctor c l').toShape
    have hj : MArg.join (MArg.ctor c l) (MArg.ctor c l')
        = MArg.ctor c (l.zipWith join l') := if_pos rfl
    rw [hj, toShape_ctor, toShape_ctor, toShape_ctor, key hl,
      WShape.ctor'_join (List.Forall₂.reverse.2 hcm),
      List.reverse_zipWith hcm.length_eq]

inductive LE_Interp.Matches : (p : Pattern) → ∀ {n}, Name → List (WShape n) → (p.Path → TShape) → Prop
  | const : Matches (.const c) c [] nofun
  | var : Matches f c rargs mf → Matches (.var f) c (a :: rargs) (·.elim a.T mf)
  | app : Matches (n := n+1) f c rargs mf → Matches (n := n) a c' rargs' ma →
    Matches (n := n+1) (.app f a) c (.ctor' c' rargs'.reverse :: rargs) (Sum.elim mf ma)

variable {p : Pattern} (ls : p.LPath → List SLevel) (m2 : p.Path → TShape)
  (R : TShape → SExpr → Prop) in
inductive LE_Interp.RHS : TShape → p.RHS → Prop
  | bot : RHS (WShape.T .bot) r
  | const : R m ((SExpr.mk e).instL (ls lp)) → RHS m (.fixed e lp cl)
  | var : m ≤ m2 path → RHS m (.var path)
  | app : RHS (WShape.T (n := n + 1) f) F → RHS a.T A → m ≤ (f.app a).T → RHS m (.app F A)

variable (c : Name) (ls : List SLevel) (R : TShape → SExpr → Prop) {n : Nat} in
inductive LE_Interp.Const : List (WShape n) → TShape → Prop
  | bot : Const rargs (WShape.T (n := n') .bot)
  | lam : (∀ x y : WShape n, (x, y) ∈ f → Const (x :: rargs) y.T) →
    m ≤ WShape.T (n := n + 1) (.lam' f) → Const rargs m
  | ctor : Params.classify c = some (.ctor rargs.length) →
    m ≤ WShape.T (n := n + 1) (.ctor' c rargs.reverse) → Const rargs m
  /-- **The rule that makes the join family repairable.** The shape's sort boolean now comes
  from `classify c`, so it is a function of the *head constant*. Two shapes realizing the same
  term therefore cannot disagree about it -- which is exactly the invariant the join lemmas
  need and `Compat` alone does not give. See `docs/design-shape-lattice.md`. -/
  | indTy : Params.classify c = some (.indTy rargs.length rel) →
    m ≤ (WShape.indTy rel : WShape (n+1)).T → Const rargs m
  /-- `lsm` is the PER-LEAF level map, bound here rather than shared across the whole
  `Const`: it depends on `p`, which this rule binds.  `ls` above is the head constant's own
  list and is what `LE_Interp.const` supplies; the two meet in `build_spine`, which reads
  `lsm` off the `MatchesS`. -/
  | pat {p : Pattern} {r} {lsm : p.LPath → List SLevel} {m' m} :
    Params.Pat p r → Matches p c rargs m' → RHS lsm m' R m r.1 → Const rargs m

inductive LE_Interp : Valuation → TShape → SExpr → Prop
  | bot : LE_Interp ρ (WShape.T (n := n) .bot) M
  | bvar : m ≤ ρ i → LE_Interp ρ m (.bvar i)
  | sort : m ≤ .sort (l ≠ .zero) → LE_Interp ρ m (.sort l)
  | app : LE_Interp ρ (WShape.T f) F → LE_Interp ρ a.T A →
    m ≤ (f.app a).T → LE_Interp ρ m (.app F A)
  | lam : LE_Interp ρ (WShape.T (n := n) a) A →
    WShape.HasDom f a → (∀ x, x.HasType a → LE_Interp (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := _+1) (.lam' f) → LE_Interp ρ m (.lam A F)
  | forallE : LE_Interp ρ (WShape.T (n := n) b) B → LE_Interp ρ (WShape.T (n := n) b') B →
    WShape.HasDom f b' → (∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := n+1) (.forallE b f) → LE_Interp ρ m (.forallE B F)
  | const :
    Params.env.constants c = some ci → ls.length = ci.uvars →
    m ≤ m' → m'.HasType a →
    LE_Interp ρ a ((SExpr.mk ci.type).instL ls) →
    LE_Interp.Const c R [] m' → (∀ m e, R m e → LE_Interp ρ m e) →
    LE_Interp ρ m (.const c ls)

theorem LE_Interp.bvar' : LE_Interp ρ (ρ i) (.bvar i) := .bvar .rfl
theorem LE_Interp.bvar0 : LE_Interp (.push ρ x) x (.bvar 0) := .bvar' (ρ := ρ.push x) (i := 0)
theorem LE_Interp.sort' : LE_Interp ρ (.sort (l ≠ .zero)) (.sort l) := .sort .rfl
theorem LE_Interp.app' (h1 : LE_Interp ρ (WShape.T f) F) (h2 : LE_Interp ρ a.T A) :
    LE_Interp ρ (f.app a).T (.app F A) := .app h1 h2 .rfl
theorem LE_Interp.lam' {f : WShapeFun n} {a : WShape n}
    (h1 : LE_Interp ρ (WShape.T a) A) (h2 : WShape.HasDom f a)
    (h3 : ∀ x, x.HasType a → LE_Interp (ρ.push x.T) (f.app x).T F) :
    LE_Interp ρ (WShape.T (n := n+1) (WShape.lam' f)) (.lam A F) := .lam h1 h2 h3 .rfl
theorem LE_Interp.forallE' {f : WShapeFun n} {b b' : WShape n}
    (h1 : LE_Interp ρ b.T B) (h2 : LE_Interp ρ b'.T B) (h3 : WShape.HasDom f b')
    (h4 : ∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F) :
    LE_Interp ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F) := .forallE h1 h2 h3 h4 .rfl

theorem LE_Interp.bvar_iff : LE_Interp ρ m (.bvar i) ↔ m ≤ ρ i :=
  ⟨fun | .bot => TShape.bot_le' | .bvar h => h, .bvar⟩

theorem LE_Interp.le_sort (H : LE_Interp ρ m (.sort u)) : m ≤ .sort (u ≠ .zero) := by
  generalize eq : SExpr.sort u = M at H
  induction H with cases eq
  | bot => exact TShape.bot_le'
  | sort h => exact h.trans TShape.sort_eqv.1

theorem LE_Interp.le_sort' (H : LE_Interp ρ m (.sort u)) : m.2 ≤ .sort (u ≠ .zero) :=
  (TShape.LE.lift_r (Nat.zero_le _)).1 H.le_sort

theorem LE_Interp.RHS.mono (h : m ≤ m')
    (hR : ∀ {a a' A}, a ≤ a' → R a' A → R' a A)
    (H : RHS m1 m2 R m' r) : RHS m1 m2 R' m r := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | const h1 => exact .const (hR h h1)
  | var h1 => exact .var (h.trans h1)
  | app hf ha h1 ihf iha => exact .app (ihf .rfl) (iha .rfl) (h.trans h1)

theorem LE_Interp.Const.mono (h : m ≤ m')
    (hR : ∀ {a a' A}, a ≤ a' → R a' A → R' a A)
    (H : Const c R rargs m') : Const c R' rargs m := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | lam _ h2 ih => exact .lam (ih · · · .rfl) (h.trans h2)
  | ctor h1 h2 => exact .ctor h1 (h.trans h2)
  | indTy h1 h2 => exact .indTy h1 (h.trans h2)
  | pat h1 h2 h3 => exact .pat h1 h2 (h3.mono h hR)

theorem LE_Interp.mono (h : m ≤ m') (H : LE_Interp ρ m' M) : LE_Interp ρ m M := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | bvar h1 => exact .bvar (h.trans h1)
  | sort h1 => exact .sort (h.trans h1)
  | app hf ha h1 => exact .app hf ha (h.trans h1)
  | lam ha hdom hbody h1 => exact .lam ha hdom hbody (h.trans h1)
  | forallE hb hb' hdom hbody h1 => exact .forallE hb hb' hdom hbody (h.trans h1)
  | const h1 h2 h3 h4 h5 h6 h7 => exact .const h1 h2 (h.trans h3) h4 h5 h6 h7

theorem LE_Interp.mono_l (hρ : ρ.LE ρ') (H : LE_Interp ρ m M) : LE_Interp ρ' m M := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar h1 => exact .bvar (h1.trans (hρ _))
  | sort h1 => exact .sort h1
  | app _ _ h1 ih_f ih_a => exact .app (ih_f hρ) (ih_a hρ) h1
  | lam _ hdom _ h1 ih_a ih_body =>
    exact .lam (ih_a hρ) hdom (fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)) h1
  | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b hρ) (ih_b' hρ) hdom ?_ h1
    exact fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)
  | const h1 h2 h3 h4 _ h6 _ ihA ihR => exact .const h1 h2 h3 h4 (ihA hρ) h6 (ihR · · · hρ)

theorem LE_Interp.unlift (le : m.1 ≤ n)
    (H : LE_Interp ρ (m.2.lift n).T M) : LE_Interp ρ m M := H.mono (TShape.lift_eqv le).2

theorem LE_Interp.RHS.mono_l (hm : ∀ p, m2' p ≤ m2 p) (H : RHS m1 m2' R m r) : RHS m1 m2 R m r := by
  induction H  with try subst eq
  | bot => exact .bot
  | const h1 => exact .const h1
  | app hf ha h1 ihf iha => exact .app ihf iha h1
  | @var _ path h1 => exact .var (h1.trans (hm path))

theorem LE_Interp.Matches.varN_const_head
    (H : Matches (.varN (.const c) n) c' rargs m) : c = c' := by
  induction n generalizing rargs with
  | zero => cases H; rfl
  | succ n ih => let .var H := H; exact ih H

theorem LE_Interp.Matches.arity (H : Matches p c rargs m) : Arity (.const c) rargs.length p := by
  induction H with
  | const => exact .refl
  | var _ ih => exact .var ih
  | app _ _ ih_f _ => exact .app ih_f

theorem LE_Interp.Matches.head_wf (H : Matches p c rargs m) (wf : p.WF cl top k) :
    ∃ k, cl c = some (if top then .symb k else .ctor k) := by
  induction H generalizing k with
  | const => exact ⟨_, wf⟩
  | var _ ih => exact ih wf
  | app _ _ ih => exact ih wf.1

theorem LE_Interp.Matches.head_wf_eq (H : Matches p c rargs m) (wf : p.WF cl top k) :
    cl c = some (if top then .symb (k + rargs.length) else .ctor (k + rargs.length)) := by
  induction H generalizing k with
  | const => simpa [Pattern.WF] using wf
  | var _ ih =>
    have := ih (k := k + 1) wf
    rw [List.length_cons]; rw [Nat.add_succ, ← Nat.succ_add]; exact this
  | app _ _ ih =>
    have := ih (k := k + 1) wf.1
    rw [List.length_cons]; rw [Nat.add_succ, ← Nat.succ_add]; exact this

theorem LE_Interp.Matches.mono_l {rargs rargs'} (wfp : p.WF Params.classify b k)
    (hc : List.Forall₂ (· ≤ ·) rargs rargs') (H : Matches (n := n) p c rargs m) :
    ∃ m', Matches (n := n) p c rargs' m' ∧ ∀ p, m p ≤ m' p := by
  induction H generalizing b k with
  | const => cases hc; exact ⟨_, .const, nofun⟩
  | var _ ih =>
    have .cons hc1 hc := hc; have ⟨_, h1, h2⟩ := ih wfp hc
    exact ⟨_, h1.var, (·.casesOn hc1.T h2)⟩
  | app _ ha ih1 ih2 =>
    have .cons hc1 hc := hc; have ⟨m2f, f1, f2⟩ := ih1 wfp.1 hc
    obtain ⟨l, b1, rfl, b2⟩ := WShape.ctor'_le.1 hc1 fun h => by
      have ⟨_, eq⟩ := ha.head_wf wfp.2; simp [IsStruct, eq] at h
    obtain ⟨l, rfl⟩ : ∃ l', List.reverse l' = l := ⟨_, l.reverse_reverse⟩
    simp [List.Forall₂.reverse, WShape.ctor_eq_ctor'] at b2 hc1 ⊢
    have ⟨m2a, a1, a2⟩ := ih2 wfp.2 b2
    exact ⟨Sum.elim m2f m2a, f1.app a1, (·.casesOn f2 a2)⟩

theorem LE_Interp.Const.mono_l (h : rargs.Forall₂ (· ≤ ·) rargs')
    (H : Const c R rargs m) : Const c R rargs' m := by
  induction H generalizing rargs' with
  | bot => exact .bot
  | lam h1 h2 ih => exact .lam (fun x y h' => ih _ _ h' (.cons .rfl h)) h2
  | ctor h1 h2 =>
    exact .ctor (h.length_eq ▸ h1) <| h2.trans (WShape.ctor'_le_ctor' (List.Forall₂.reverse.2 h)).T
  | indTy h1 h2 => exact .indTy (h.length_eq ▸ h1) h2
  | pat h1 h2 h3 =>
    have ⟨_, a1, a2⟩ := h2.mono_l (Params.pat_wf h1) h
    refine .pat h1 a1 (h3.mono_l a2)

theorem LE_Interp.Matches.matches_inter {rargs rargs'}
    (hc : List.Forall₂ WShape.Compat rargs rargs')
    (hp : Matches (n := n) p c rargs m) (wfp : p.WF Params.classify b k)
    (hq : Matches (n := n) q c rargs' m') (wfq : q.WF Params.classify b' k') :
    ∃ r, p.inter q = some r := by
  induction hp generalizing q b b' k k' with
  | const => cases hc; cases hq; simp [Pattern.inter]
  | var _ ih =>
    have .cons _ hc := hc
    cases hq with
    | var hq' => obtain ⟨_, ihf⟩ := ih hc wfp hq' wfq; simp [Pattern.inter, ihf]
    | app hf' => obtain ⟨_, ihf⟩ := ih hc wfp hf' wfq.1; simp [Pattern.inter, ihf]
  | @app _ _ _ _ _ _ c rargs _ hf ha ihf iha =>
    have .cons hc1 hc := hc
    cases hq with
    | var hf' => have ⟨_, ih⟩ := ihf hc wfp.1 hf' wfq; simp [Pattern.inter, ih]
    | @app _ _ _ _ _ _ c' rargs' _ hf' ha' =>
      obtain ⟨_, ihf⟩ := ihf hc wfp.1 hf' wfq.1
      obtain ⟨rfl, hc'⟩ : c = c' ∧ List.Forall₂ WShape.Compat rargs rargs' := by
        unfold WShape.ctor' at hc1; split at hc1 <;> [split at hc1; skip] <;> rename_i hn
        · simp [WShape.Compat, WShape.ctor, Shape.Compat, List.Forall₂.reverse] at hc1; exact hc1
        · have ⟨_, wf⟩ := ha'.head_wf wfq.2; simp [IsStruct, wf] at hn
        · have ⟨_, wf⟩ := ha.head_wf wfp.2; simp [IsStruct, wf] at hn
      have ⟨_, iha⟩ := iha hc' wfp.2 ha' wfq.2
      simp [Pattern.inter, ihf, iha]

theorem LE_Interp.Matches.compat_join {rargs rargs'}
    (hc : List.Forall₂ WShape.Compat rargs rargs')
    (hp : Matches (n := n) p c rargs m) (hp' : Matches (n := n) p c rargs' m')
    (wf : p.WF Params.classify b k) :
    (∀ x, (m x).Compat (m' x)) ∧
    Matches p c (rargs.zipWith WShape.join rargs') fun x => (m x).join (m' x) := by
  induction hp generalizing b k with
  | const => cases hp'; exact ⟨nofun, cast (by congr 1; ext ⟨⟩) Matches.const⟩
  | @var f c n rargs mf a _ ih =>
    let .cons hc1 hc := hc
    let .var (a := a') (mf := mf') hf' := hp'
    have ⟨ihC, ihM⟩ := ih hc hf' wf
    refine' ⟨(·.casesOn hc1.T ihC), cast ?_ ihM.var⟩; congr 1; ext ⟨⟩
    · exact WShape.T_join.symm
    · rfl
  | @app _ _ _ _ _ _ c₁ rargs _ hf ha ihf iha =>
    let .cons hc1 hc := hc; let .app (c' := c₂) (rargs' := rargs') hf' ha' := hp'
    obtain ⟨rfl, hc'⟩ : c₁ = c₂ ∧ List.Forall₂ WShape.Compat rargs rargs' := by
      unfold WShape.ctor' at hc1; split at hc1 <;> [split at hc1; skip] <;> rename_i hn
      · simp [WShape.Compat, WShape.ctor, Shape.Compat, List.Forall₂.reverse] at hc1; exact hc1
      · have ⟨_, wf⟩ := ha'.head_wf wf.2; simp [IsStruct, wf] at hn
      · have ⟨_, wf⟩ := ha.head_wf wf.2; simp [IsStruct, wf] at hn
    have ⟨ihfC, ihfM⟩ := ihf hc hf' wf.1
    have ⟨ihaC, ihaM⟩ := iha hc' ha' wf.2
    refine ⟨(·.casesOn ihfC ihaC), cast ?_ (ihfM.app ihaM)⟩; congr 1
    · simp [List.reverse_zipWith hc'.length_eq, ← WShape.ctor'_join (List.Forall₂.reverse.2 hc')]
    · ext ⟨⟩ <;> rfl

theorem LE_Interp.Matches.unique {p : Pattern} {c : Name} {n : Nat} {rargs : List (WShape n)}
    {m m' : p.Path → TShape}
    (wf : p.WF Params.classify b k)
    (H : Matches (n := n) p c rargs m) (H' : Matches (n := n) p c rargs m') : m = m' := by
  induction H generalizing b k with
  | const => cases H'; rfl
  | var _ ih =>
    let .var hf' := H'
    refine funext fun | none => rfl | some p => congrFun (ih wf hf') p
  | app _ ha ihf iha =>
    generalize eq' : WShape.ctor' .. = head_w at H'
    let .app hf' ha' := H'
    have ⟨_, wf_a⟩ := ha.head_wf wf.2
    have ⟨_, wf_a'⟩ := ha'.head_wf wf.2
    simp [WShape.ctor', IsStruct, wf_a, wf_a'] at eq'
    obtain ⟨rfl, eq⟩ := WShape.ctor.inj.1 eq'; cases List.reverse_inj.1 eq
    rw [ihf wf.1 hf', iha wf.2 ha']

theorem LE_Interp.RHS.compat_join
    {m₁ m₂} (hpm : ∀ x, (m₁ x).Compat (m₂ x))
    (hR_bot : ∀ {n e}, R (WShape.T (n := n) .bot) e)
    (hR'_bot : ∀ {n e}, R' (WShape.T (n := n) .bot) e)
    (hRR : ∀ {m₁ m₂ A}, R m₁ A → R' m₂ A → m₁.Compat m₂ ∧ R₃ (m₁.join m₂) A)
    (hR₃_mono : ∀ {a a' A}, a ≤ a' → R₃ a' A → R₃ a A)
    (H1 : RHS (p := p) ls m₁ R m r) (H2 : RHS ls m₂ R' m' r) :
    m.Compat m' ∧ RHS ls (fun x => (m₁ x).join (m₂ x)) R₃ (m.join m') r := by
  induction H1 generalizing m' with
  | bot =>
    refine ⟨.bot_l', ?_⟩
    cases H2 with
    | bot => (conv => arg 4; simp [TShape.join]); exact .bot
    | const h2 => exact .const (hRR hR_bot h2).2
    | var h2 =>
      conv => arg 4; simp [TShape.join]
      refine .var <| (TShape.lift_eqv (Nat.le_max_right ..)).1.trans ?_
      exact h2.trans (TShape.Join.mk (hpm _)).le.2
    | app hf' ha' h2 =>
      refine .mono ?_ ?_ <| .mono_l (fun p => (TShape.Join.mk (hpm p)).le.2) <| .app hf' ha' h2
      · exact (TShape.Join.mk .bot_l' _).2 ⟨TShape.bot_le', .rfl⟩
      · intro a a' A le hr
        have := hRR (@hR_bot 0 A) hr
        exact hR₃_mono (le.trans (TShape.Join.mk this.1).le.2) this.2
  | const h1 =>
    cases H2 with
    | bot => exact ⟨.bot_r', .const (hRR h1 hR'_bot).2⟩
    | const h2 => exact ⟨(hRR h1 h2).1, .const (hRR h1 h2).2⟩
  | var h1 => cases H2 with
    | bot =>
      refine ⟨.bot_r', ?_⟩
      conv => arg 4; simp [TShape.join]
      refine .var <| (TShape.lift_eqv (Nat.le_max_left ..)).1.trans ?_
      exact h1.trans (TShape.Join.mk (hpm _)).le.1
    | var h2 =>
      refine ⟨(hpm _).mono h1 h2, .var ?_⟩
      exact have ⟨a1, a2⟩ := (TShape.Join.mk (hpm _)).le
        (TShape.Join.mk ((hpm _).mono h1 h2) _).2 ⟨h1.trans a1, h2.trans a2⟩
  | @app n₁ f₁ _ _ _ a₁ hf ha h1 ihf iha => cases H2 with
    | bot =>
      refine ⟨.bot_r', ?_⟩
      refine .mono ?_ ?_ <| .mono_l (fun p => (TShape.Join.mk (hpm p)).le.1) <| .app hf ha h1
      · conv => lhs; simp [TShape.join]
        exact (TShape.lift_eqv (Nat.le_max_left ..)).1
      · intro a a' A le hr
        have := hRR hr (@hR'_bot 0 A)
        exact hR₃_mono (le.trans (TShape.Join.mk this.1).le.1) this.2
    | @app n f _ _ _ a hf' ha' h2 =>
      have ⟨cf, jf⟩ := ihf hf'
      have ⟨ca, ja⟩ := iha ha'
      refine have cM := .mono h1 h2 <| cf.app ca; ⟨cM, ?_⟩
      have hf := (TShape.Join.mk cf).le
      have ha := (TShape.Join.mk ca).le
      have le' := Nat.le_of_eq <| Nat.add_max_add_right n₁ n 1
      refine .mono (R := R₃) (R' := R₃) ((TShape.Join.mk cM _).2 ⟨?_, ?_⟩) hR₃_mono <|
        .app (jf.mono (R := R₃) (R' := R₃) (TShape.lift_eqv le').1 hR₃_mono) ja .rfl
      · exact h1.trans <| TShape.app_mono (hf.1.trans (TShape.lift_eqv le').2) ha.1
      · exact h2.trans <| TShape.app_mono (hf.2.trans (TShape.lift_eqv le').2) ha.2

theorem pat_arity (hP : Params.Pat p r) (h : Arity (.const c) n p) :
    Params.classify c = some (.symb n) := by
  suffices ∀ cl n k, p.WF cl true k → Arity (.const c) n p → cl c = some (.symb (n + k)) from
    this _ _ _ (Params.pat_wf hP) h
  clear r hP h; intro cl n k h1 h2
  induction h2 generalizing k with
  | refl => simpa only [Nat.zero_add]
  | var _ ih => simpa [Nat.succ_add, ← Nat.add_assoc] using ih _ h1
  | app _ ih => simpa [Nat.succ_add, ← Nat.add_assoc] using ih _ h1.1

theorem LE_Interp.Matches.lift (le : n ≤ n') (H : Matches (n := n) p c rargs m) :
    ∃ m', Matches p c (rargs.map (.lift n')) m' ∧ ∀ p, m p ≤ m' p ∧ m' p ≤ m p := by
  induction H generalizing n' with
  | const => exact ⟨_, .const, nofun⟩
  | var _ ih =>
    have ⟨m2', h1, h2⟩ := ih le; exact ⟨_, .var h1, (·.casesOn (TShape.lift_eqv le).symm h2)⟩
  | app _ _ ih1 ih2 =>
    have ⟨m2f, f1, f2⟩ := ih1 le; let n' + 1 := n'
    have ⟨m2a, a1, a2⟩ := ih2 (Nat.le_of_succ_le_succ le)
    refine ⟨Sum.elim m2f m2a, ?_, (·.casesOn f2 a2)⟩
    show Matches _ _ (WShape.lift (n'+1) (WShape.ctor' _ _) :: _) _
    rw [WShape.lift_ctor' (Nat.le_of_succ_le_succ le), List.map_reverse]
    exact f1.app a1

theorem LE_Interp.Const.lift (hn : n₁ ≤ n₂)
    (hR : ∀ {a a' A}, a ≤ a' → R a' A → R a A)
    (H : Const (n := n₁) c R rargs m) : Const c R (rargs.map (.lift n₂)) m := by
  induction H generalizing n₂ with
  | bot => exact .bot
  | @lam f rargs m h1 h2 ih =>
    refine .lam (f := f.lift n₂) (fun _ _ h => ?_) ?_
    · obtain ⟨x, y, h', rfl, rfl⟩ := (WShapeFun.mem_lift hn).1 h
      exact (ih _ _ h' hn).mono (TShape.lift_eqv hn).1 hR
    · exact WShape.lift_lam' hn ▸ h2.trans (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | ctor h1 h2 =>
    refine .ctor (by rw [List.length_map]; exact h1) (h2.trans ?_)
    rw [← List.map_reverse, ← WShape.lift_ctor' hn]
    exact (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | indTy h1 h2 =>
    refine .indTy (by rw [List.length_map]; exact h1) (h2.trans ?_)
    rw [← WShape.lift_indTy (n := n₁) (m := n₂)]
    exact (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | pat h1 h2 h3 =>
    have ⟨_, a1, a2⟩ := h2.lift hn
    exact .pat h1 a1 <| h3.mono_l (a2 · |>.1)

theorem LE_Interp.lift (le : m.1 ≤ n)
    (H : LE_Interp ρ m M) : LE_Interp ρ (m.2.lift n).T M := H.mono (TShape.lift_eqv le).1

theorem LE_Interp.RHS.closed
    (H : RHS m1 m2 R m r) : RHS m1 m2 (fun e A => A.ClosedN ∧ R e A) m r := by
  induction H with
  | bot => exact .bot
  | @const _ _ _ cl h1 => exact .const ⟨cl.mkS.instL, h1⟩
  | var h1 => exact .var h1
  | app hf ha h1 ih_f ih_a => exact .app ih_f ih_a h1

theorem LE_Interp.Const.closed
    (H : Const c R rargs m) : Const c (fun e A => A.ClosedN ∧ R e A) rargs m := by
  induction H with
  | bot => exact .bot
  | lam _ h2 ih => exact .lam ih h2
  | ctor h1 h2 => exact .ctor h1 h2
  | indTy h1 h2 => exact .indTy h1 h2
  | pat h1 h2 h3 => exact .pat h1 h2 h3.closed

theorem LE_Interp.closed (cl : ClosedN M k) (h : ∀ i < k, ρ i = ρ' i)
    (H : LE_Interp ρ m M) : LE_Interp ρ' m M := by
  induction H generalizing k ρ' with
  | bot => exact .bot
  | sort h1 => exact .sort h1
  | bvar h1 => exact .bvar ((h _ cl).symm ▸ h1)
  | app hf ha h1 ih_f ih_a =>
    exact .app (ih_f cl.1 h) (ih_a cl.2 h) h1
  | lam ha hdom hbody h1 ih_a ih_body =>
    refine .lam (ih_a cl.1 h) hdom (fun x hx => ih_body x hx cl.2 ?_) h1
    intro | 0, _ => rfl | j+1, hi => exact h j (Nat.lt_of_succ_lt_succ hi)
  | forallE hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b cl.1 h) (ih_b' cl.1 h) hdom (fun x hx => ih_body x hx cl.2 ?_) h1
    intro | 0, _ => rfl | i+1, hi => exact h i (Nat.lt_of_succ_lt_succ hi)
  | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
    refine .const h1 h2 h3 h4 (ih1 ?_ h) h6.closed fun m e ⟨a1, a2⟩ => ?_
    · exact (Params.henv.closedC h1).mkS.instL.mono (Nat.zero_le _)
    · exact ih2 m e a2 (a1.mono (Nat.zero_le _)) h

theorem LE_Interp.closed_iff {M : SExpr} (cl : ClosedN M)
    {ρ ρ' : Valuation} {m : TShape} : LE_Interp ρ m M ↔ LE_Interp ρ' m M :=
  ⟨closed cl nofun, closed cl nofun⟩

theorem LE_Interp.weak'_iff (l : Lift) (h : ∀ i, ρ i = ρ' (l.liftVar i)) :
    LE_Interp ρ' m (M.lift' l) ↔ LE_Interp ρ m M := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · generalize eq : M.lift' l = M' at H
    induction H generalizing M ρ l with first
      | subst eq | cases M <;> cases eq
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f _ h rfl) (ih_a _ h rfl) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b _ h rfl) (ih_b' _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ h6.closed ?_
      · exact ih1 _ h <| (Params.henv.closedC h1).mkS.instL.lift'_eq .zero
      · rintro m A ⟨a1, a2⟩; exact ih2 _ _ a2 _ h <| a1.lift'_eq .zero
  · induction H generalizing ρ' l with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f l h) (ih_a l h) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b l h) (ih_b' l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ h6.closed ?_
      · exact (Params.henv.closedC h1).mkS.instL.lift'_eq .zero ▸ ih1 _ h
      · rintro m A ⟨a1, a2⟩; exact a1.lift'_eq .zero ▸ ih2 _ _ a2 _ h

theorem LE_Interp.weak_iff : LE_Interp (ρ.push x) m M.lift ↔ LE_Interp ρ m M :=
  LE_Interp.weak'_iff (.skip .refl) (fun _ => rfl)

theorem LE_Interp.weak (H : LE_Interp ρ m M) : LE_Interp (ρ.push x) m M.lift :=
  weak_iff.2 H

theorem LE_Interp.Const.compat_mismatch {rargs1 rargs2 : List (WShape n)} {m : TShape}
    (h_len : rargs2.length < rargs1.length) (H1 : Const c R rargs1 m)
    (H2 : Params.classify c = some (.ctor rargs2.length) ∨
      (∃ rel, Params.classify c = some (.indTy rargs2.length rel)) ∨
      ∃ p r m, Params.Pat p r ∧ Matches p c rargs2 m) :
    m ≤ .bot := by
  induction H1 with
  | bot => exact TShape.bot_eqv.1
  | @lam f _ _ he m_le ih =>
    by_cases hf : f.NonZero
    · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
      have := ih _ t (WShapeFun.mem_val hxy) (by simp; omega)
      cases hn <| WShape.LE.T_iff.1 <| this.trans TShape.bot_eqv.2
    · have := WShape.lam'_le_lam'.2 <| NonZero.not_iff.1 hf
      exact m_le.trans <| (WShape.lam'_bot ▸ this).T.trans TShape.bot_eqv.1
  | ctor hct m_le_ctor =>
    obtain hct' | ⟨_, hct'⟩ | ⟨p, r, m, hP, hM⟩ := H2
    · generalize rargs2.length = n at hct' h_len
      cases hct.symm.trans hct'; cases Nat.lt_irrefl _ h_len
    · cases hct.symm.trans hct'
    · cases hct.symm.trans <| pat_arity hP hM.arity
  | indTy hct _ =>
    obtain hct' | ⟨_, hct'⟩ | ⟨_, _, _, hP', hM'⟩ := H2
    · cases hct.symm.trans hct'
    · generalize rargs2.length = n at hct' h_len
      cases hct.symm.trans hct'; cases Nat.lt_irrefl _ h_len
    · cases hct.symm.trans <| pat_arity hP' hM'.arity
  | pat hP hM hR =>
    obtain hct' | ⟨_, hct'⟩ | ⟨_, _, _, hP', hM'⟩ := H2
    · cases hct'.symm.trans <| pat_arity hP hM.arity
    · cases hct'.symm.trans <| pat_arity hP hM.arity
    · have := pat_arity hP' hM'.arity
      generalize rargs2.length = n at h_len this
      cases (pat_arity hP hM.arity).symm.trans this; cases Nat.lt_irrefl _ h_len

theorem LE_Interp.Const.compat_join
    {rargs1 rargs2} (hc : List.Forall₂ WShape.Compat rargs1 rargs2)
    (H1 : Const (n := n) c R rargs1 m) (H2 : Const c R' rargs2 m')
    (hR_bot : ∀ {n} {e}, R (WShape.T (n := n) .bot) e)
    (hR'_bot : ∀ {n} {e}, R' (WShape.T (n := n) .bot) e)
    (hR₃_mono : ∀ {a a' A}, a ≤ a' → R₃ a' A → R₃ a A)
    (hRR : ∀ {m₁ m₂ A}, R m₁ A → R' m₂ A → m₁.Compat m₂ ∧ R₃ (m₁.join m₂) A) :
    m.Compat m' ∧ Const c R₃ (rargs1.zipWith WShape.join rargs2) (m.join m') := by
  have hRR_c : ∀ {m₁ m₂ A}, R m₁ A → R' m₂ A → m₁.Compat m₂ := fun h1 h2 => (hRR h1 h2).1
  have bot_r {n n' m rargs rargs2} (H : Const (n := n) c R rargs m)
      (hc : List.Forall₂ WShape.Compat rargs rargs2) :
      TShape.Compat m (WShape.bot (n := n')).T ∧
      Const c R₃ (List.zipWith WShape.join rargs rargs2) (m.join (WShape.bot (n := n')).T) := by
    refine have hbc := .bot_r'; ⟨hbc, .mono ?_ (fun h1 h2 => ?_) (H.mono_l ?_)⟩
    · exact (TShape.Join.mk hbc _).2 ⟨.rfl, TShape.bot_le'⟩
    · have ⟨a1, a2⟩ := hRR h2 (hR'_bot (n := 0))
      exact hR₃_mono (h1.trans (TShape.Join.mk a1).le.1) a2
    · exact (WShape.le_zipWith_join hc).1
  induction H1 generalizing rargs2 m' with
  | bot =>
    refine have hbc := .bot_l'; ⟨hbc, .mono ?_ (fun h1 h2 => ?_) (H2.mono_l ?_)⟩
    · exact (TShape.Join.mk hbc _).2 ⟨TShape.bot_le', .rfl⟩
    · have ⟨a1, a2⟩ := hRR (hR_bot (n := 0)) h2
      exact hR₃_mono (h1.trans (TShape.Join.mk a1).le.2) a2
    · exact (WShape.le_zipWith_join hc).2
  | @lam f rargs m he m_le ih =>
    cases H2 with
    | bot => exact bot_r (.lam he m_le) hc
    | @lam f' _ k' he' m_le' =>
      have hfc : WShapeFun.Compat f f' := by
        simp only [WShapeFun.Compat.def, Prod.forall]
        intro x y h1 x' y' h2 hc'
        exact WShape.Compat.T_iff.2 (ih _ _ h1 (hc.cons hc') (he' _ _ h2)).1
      refine have hmc := .mono m_le m_le' (WShape.Compat.lam'_lam' hfc).T; ⟨hmc, ?_⟩
      have hJ_lam : WShape.Join (.lam' f) (.lam' f') (.lam' (f.join f')) :=
        WShape.Join.lam'.2 (.mk hfc)
      refine .lam (f := f.join f') ?_ <|
        (TShape.Join.mk hmc _).2 ⟨m_le.trans hJ_lam.le.1.T, m_le'.trans hJ_lam.le.2.T⟩
      simp only [WShapeFun.mem_join hfc]
      rintro _ _ ⟨⟨x, y⟩, h1, ⟨x', y'⟩, h2, hc', rfl, rfl⟩; dsimp only at *
      have ⟨x₁, le, a1⟩ := f.app_eq (x.join x')
      have ⟨x₂, le', a2⟩ := f'.app_eq (x.join x')
      have hxc := hfc.app_l (x.join x')
      have hxc' := WShape.Compat.iff.2 ⟨_, le, le'⟩
      have ⟨hyc, ih⟩ := ih _ _ a1 (hc.cons hxc') (he' _ _ a2)
      rw [WShape.T_join] at ih
      exact ih.mono_l <| .cons ((WShape.Join.mk hxc' _).2 ⟨le, le'⟩) <| .rfl fun _ _ => .rfl
    | ctor hct' m_le' =>
      unfold WShape.lam' at m_le; split at m_le <;> rename_i hf
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
        have h_const := he s t (f.mem_val hxy)
        have hL : rargs.length = rargs2.length := hc.length_eq
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        exact compat_mismatch (rargs2 := rargs2) (by simp; omega) h_const <| .inl hct'
      · refine have hmc := .mono (m_le.trans TShape.bot_eqv.1) .rfl .bot_l; ⟨hmc, ?_⟩
        refine .ctor ?_ (List.reverse_zipWith hc.length_eq ▸ (TShape.Join.mk hmc _).2 ⟨?_, ?_⟩)
        · rw [List.length_zipWith, hc.length_eq, Nat.min_self, hct']
        · exact m_le.trans TShape.bot_le'
        · refine m_le'.trans (WShape.ctor'_le_ctor' ?_).T
          exact (WShape.le_zipWith_join (List.Forall₂.reverse.2 hc)).2
    | pat hP hM hR =>
      unfold WShape.lam' at m_le; split at m_le <;> rename_i hf
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
        have h_const := he _ _ (f.mem_val hxy)
        have hL : rargs.length = rargs2.length := hc.length_eq
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        exact compat_mismatch (by simp; omega) h_const <| .inr <| .inr ⟨_, _, _, hP, hM⟩
      · refine have hmc := .mono (m_le.trans TShape.bot_eqv.1) .rfl .bot_l; ⟨hmc, ?_⟩
        have h_le : m.join m' ≤ m' := (TShape.Join.mk hmc _).2 ⟨m_le.trans TShape.bot_le', .rfl⟩
        refine .mono h_le (fun le hr => ?_) <| .mono_l (WShape.le_zipWith_join hc).2 (.pat hP hM hR)
        have hc := hRR (hR_bot (n := 0)) hr
        exact hR₃_mono (le.trans (TShape.Join.mk hc.1).le.2) hc.2
    | indTy hct' m_le' =>
      unfold WShape.lam' at m_le; split at m_le <;> rename_i hf
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
        have h_const := he _ _ (f.mem_val hxy)
        have hL : rargs.length = rargs2.length := hc.length_eq
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        exact compat_mismatch (by simp; omega) h_const <| .inr <| .inl ⟨_, hct'⟩
      · refine have hmc := .mono (m_le.trans TShape.bot_eqv.1) .rfl .bot_l; ⟨hmc, ?_⟩
        have h_le : m.join m' ≤ m' := (TShape.Join.mk hmc _).2 ⟨m_le.trans TShape.bot_le', .rfl⟩
        exact .mono h_le hR₃_mono <| .mono_l (WShape.le_zipWith_join hc).2 (.indTy hct' m_le')
  | @ctor m rargs hct m_le =>
    cases H2 with
    | bot => exact bot_r (.ctor hct m_le) hc
    | lam he' m_le' =>
      unfold WShape.lam' at m_le'; split at m_le' <;> rename_i hf'
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf'
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        have h_const := he' _ _ (WShapeFun.mem_val hxy)
        have hL := hc.length_eq
        exact compat_mismatch (by simp; omega) h_const (.inl hct)
      · refine have hmc := .mono .rfl (m_le'.trans TShape.bot_eqv.1) .bot_r; ⟨hmc, ?_⟩
        refine .ctor ?_ (List.reverse_zipWith hc.length_eq ▸ (TShape.Join.mk hmc _).2 ⟨?_, ?_⟩)
        · rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, hct]
        · refine m_le.trans (WShape.ctor'_le_ctor' ?_).T
          exact (WShape.le_zipWith_join (List.Forall₂.reverse.2 hc)).1
        · exact m_le'.trans TShape.bot_le'
    | ctor _ m_le' =>
      refine have hc_rev := List.Forall₂.reverse.2 hc
        have hc' := (WShape.Compat.ctor'_ctor' hc_rev).T.mono m_le m_le'; ⟨hc', ?_⟩
      refine .ctor ?_ (List.reverse_zipWith hc.length_eq ▸ (TShape.Join.mk hc' _).2 ⟨?_, ?_⟩)
      · rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, hct]
      · exact m_le.trans (WShape.ctor'_le_ctor' (WShape.le_zipWith_join hc_rev).1).T
      · exact m_le'.trans (WShape.ctor'_le_ctor' (WShape.le_zipWith_join hc_rev).2).T
    | pat hP hM hR => cases hct.symm.trans <| pat_arity hP hM.arity
    | indTy hct' _ => cases hct.symm.trans hct'
  | @indTy _ _ rargs hct m_le =>
    cases H2 with
    | bot => exact bot_r (.indTy hct m_le) hc
    | lam he' m_le' =>
      unfold WShape.lam' at m_le'; split at m_le' <;> rename_i hf'
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf'
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        have h_const := he' _ _ (WShapeFun.mem_val hxy)
        have hL := hc.length_eq
        exact compat_mismatch (rargs2 := rargs) (by simp; omega) h_const <| .inr <| .inl ⟨_, hct⟩
      · refine have hmc := .mono .rfl (m_le'.trans TShape.bot_eqv.1) .bot_r; ⟨hmc, ?_⟩
        refine .indTy ?_ ((TShape.Join.mk hmc _).2 ⟨m_le, m_le'.trans TShape.bot_le'⟩)
        rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, hct]
    | ctor hct' m_le' => cases hct.symm.trans hct'
    | pat hP hM hR => cases hct.symm.trans <| pat_arity hP hM.arity
    | indTy hct' m_le' =>
      -- Both sides classify the *same* head constant, so `Classification.indTy`'s sort
      -- boolean agrees.  This is the payoff of parameterising `.indTy`: `Compat` alone
      -- never gave it.
      injection Option.some.inj (hct.symm.trans hct') with h_len h_rel
      subst h_rel
      refine have hc' := TShape.Compat.def'.2 ⟨_, m_le, m_le'⟩; ⟨hc', ?_⟩
      refine .indTy ?_ ((TShape.Join.mk hc' _).2 ⟨m_le, m_le'⟩)
      rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, hct]
  | @pat _ _ rargs _ _ m hP hM hR =>
    cases H2 with
    | bot => exact bot_r (.pat hP hM hR) hc
    | lam he' m_le' =>
      unfold WShape.lam' at m_le'; split at m_le' <;> rename_i hf'
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf'
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        have h_const := he' _ _ (WShapeFun.mem_val hxy)
        have hL := hc.length_eq
        exact compat_mismatch (by simp; omega) h_const <| .inr <| .inr ⟨_, _, _, hP, hM⟩
      · refine have hmc := .mono .rfl (m_le'.trans TShape.bot_eqv.1) .bot_r; ⟨hmc, ?_⟩
        have h_le : m.join m' ≤ m := (TShape.Join.mk hmc _).2 ⟨.rfl, m_le'.trans TShape.bot_le'⟩
        refine .mono h_le (fun le hr => ?_) <| .mono_l (WShape.le_zipWith_join hc).1 (.pat hP hM hR)
        have hc := hRR hr (hR'_bot (n := 0))
        exact hR₃_mono (le.trans (TShape.Join.mk hc.1).le.1) hc.2
    | ctor hct' => cases hct'.symm.trans <| pat_arity hP hM.arity
    | indTy hct' _ => cases hct'.symm.trans <| pat_arity hP hM.arity
    | pat hP' hM' hR' =>
      have ⟨_, hi⟩ := hM.matches_inter hc (Params.pat_wf hP) hM' (Params.pat_wf hP')
      obtain ⟨rfl, -, ⟨⟩⟩ := Params.pat_uniq hP' hP .refl hi
      have ⟨hc, hj⟩ := hM.compat_join hc hM' (Params.pat_wf hP)
      -- **OPEN, and it is the whole residue of the per-leaf level-list change.**
      -- `Const.pat` binds its level map `lsm : p.LPath → List SLevel` existentially, because
      -- the map's TYPE depends on `p`, which that rule binds -- so `Const` has nowhere to
      -- record it.  Here the two `Const`s describe the same term, so their maps agree; but
      -- `Const` does not say so, and `RHS.compat_join` needs one shared `lsm`.
      -- Closing it means recording the map in `Const` -- i.e. `LE_Interp.Const` (and
      -- `LE_Interp.Matches`, which carries no levels at all) indexed by `LPath`.  Everything
      -- else the change touches is already green: this is the ONE obligation it leaves.
      have ⟨a1, a2⟩ := hR.compat_join hc hR_bot hR'_bot hRR hR₃_mono hR'
      exact ⟨a1, .pat hP hj a2⟩

theorem LE_Interp.compat_join {m₁ m₂ : TShape}
    (hρ : ρ'.LE ρ) (H1 : LE_Interp ρ' m₁ M) (H2 : LE_Interp ρ m₂ M) :
    m₁.Compat m₂ ∧ LE_Interp ρ (m₁.join m₂) M := by
  have mk {m₁ m₂ m ρ M} (H1 : m₁ ≤ m) (H2 : m₂ ≤ m) (H : LE_Interp ρ m M) :
      m₁.Compat m₂ ∧ LE_Interp ρ (m₁.join m₂) M :=
    have := TShape.Compat.def'.2 ⟨_, H1, H2⟩
    ⟨this, H.mono ((TShape.Join.mk this _).2 ⟨H1, H2⟩)⟩
  have bot_r {m₁ n₂ ρ' ρ M} (hρ : ρ'.LE ρ) (H : LE_Interp ρ' m₁ M) :
      m₁.Compat (WShape.bot (n := n₂)).T ∧ LE_Interp ρ (m₁.join (WShape.bot (n := n₂)).T) M :=
    mk .rfl TShape.bot_le' (H.mono_l hρ)
  induction H1 generalizing ρ m₂ with
  | bot => exact mk TShape.bot_le' .rfl H2
  | sort h1 =>
    cases H2 with | bot => exact bot_r hρ (.sort h1) | sort h2
    exact mk h1 (h2.trans TShape.sort_eqv.2) (.sort .rfl)
  | bvar h1 =>
    cases H2 with | bot => exact bot_r hρ (.bvar h1) | bvar h2
    exact mk (h1.trans (hρ _)) h2 .bvar'
  | app hf ha h1 ih_f ih_a =>
    cases H2 with | bot => exact bot_r hρ (.app hf ha h1) | app hf' ha' h1'
    have ⟨cf, jf⟩ := ih_f hρ hf'
    have ⟨ca, ja⟩ := ih_a hρ ha'
    have hf := (TShape.Join.mk cf).le
    have ha := (TShape.Join.mk ca).le
    refine have le' := Nat.add_max_add_right .. ▸ Nat.le_refl _; mk ?_ ?_ ((jf.lift le').app' ja)
    · exact h1.trans <| TShape.app_mono (hf.1.trans (TShape.lift_eqv le').2) ha.1
    · exact h1'.trans <| TShape.app_mono (hf.2.trans (TShape.lift_eqv le').2) ha.2
  | lam ha hdom he h1 ih_a ih_f =>
    cases H2 with | bot => exact bot_r hρ (.lam ha hdom he h1) | lam ha' hdom' he' h1'
    rename_i ρ' n₁ a₁ A f₁ F m₁ n₂ a₂ f₂
    have ⟨ca, ia⟩ := ih_a hρ ha'
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom' x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he' x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      refine mk ?_ ?_ hle'
      · exact (WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1
      · exact (WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : WShapeFun.Compat (f₁.lift (max n₁ n₂)) (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom' := (WShape.HasDom.lift le₂).2 hdom'
    have ca_w : WShape.Compat (a₁.lift _) (a₂.lift _) := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h1'.trans ?_) <| .lam' ia (hdom.join cf ca_w hdom') fun x hx => ?_
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 <|
        WShape.lift_lam' le₁ ▸ WShape.lam'_le_lam'.2 jf.le.1
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 <|
        WShape.lift_lam' le₂ ▸ WShape.lam'_le_lam'.2 jf.le.2
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    have oy_c := WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩
    exact (ja _).2 (WShape.Join.mk oy_c).le |>.T
  | forallE hb ha hdom he h1 ih_b ih_a ih_f =>
    cases H2 with
    | bot => exact bot_r hρ (.forallE hb ha hdom he h1) | forallE hb2 ha2 hdom2 he2 h12
    rename_i ρ' n₁ b₁ B b₁' f₁ F m₁ n₂ b₂ b₂' f₂
    have ⟨cb, ib⟩ := ih_b hρ hb2
    have ⟨ca, ia⟩ := ih_a hρ ha2
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom2 x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he2 x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      exact mk ((WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1)
        ((WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2) hle'
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : (f₁.lift (max n₁ n₂)).Compat (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have cb_w := (TShape.Compat.def le₁ le₂).1 cb
    have jb := WShape.Join.mk cb_w; have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom2 := (WShape.HasDom.lift le₂).2 hdom2
    have ca_w := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h12.trans ?_) <|
      .forallE' ib ia (hdom.join cf ca_w hdom2) fun x hx => ?_
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 ?_
      exact WShape.lift_forallE le₁ ▸ WShape.forallE_le_forallE.2 ⟨jb.le.1, jf.le.1⟩
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 ?_
      exact WShape.lift_forallE le₂ ▸ WShape.forallE_le_forallE.2 ⟨jb.le.2, jf.le.2⟩
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    exact (ja _).2 (WShape.Join.mk <| WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩).le |>.T
  | @const _ _ _ _ _ _ _ _ R₁ h1 h2 h3 h4 h5 h6 h7 ih1 ih2 =>
    cases H2 with | @const _ _ _ _ _ _ _ _ R₂ a1 a2 a3 a4 a5 a6 a7 => ?_ | bot =>
      exact bot_r hρ (.const h1 h2 h3 h4 h5 h6 h7)
    cases h1.symm.trans a1
    let Rd (R : TShape → SExpr → Prop) m e := m ≤ .bot ∨ ∃ m', m ≤ m' ∧ R m' e
    have h6' := h6.mono (R' := Rd R₁) .rfl (fun le hr => Or.inr ⟨_, le, hr⟩)
    have a6' := a6.mono (R' := Rd R₂) .rfl (fun le hr => Or.inr ⟨_, le, hr⟩)
    have mono {R a a' A} (le : a ≤ a') : Rd R a' A → Rd R a A :=
      .imp (by exact le.trans) fun ⟨_, le', hr⟩ => by exact ⟨_, le.trans le', hr⟩
    have ⟨hc1, hj1⟩ := (h6'.lift (Nat.le_max_left ..) mono).compat_join
        (R₃ := LE_Interp ρ) .nil (a6'.lift (Nat.le_max_right ..) mono)
        (.inl TShape.bot_le') (.inl TShape.bot_le') .mono <| by
      rintro m₁ m₂ A (hb1 | ⟨m₁', le1, hr1⟩) (hb2 | ⟨m₂', le2, hr2⟩)
      · exact mk hb1 hb2 .bot
      · exact mk (hb1.trans TShape.bot_le') le2 (a7 m₂' A hr2)
      · exact mk le1 (hb2.trans TShape.bot_le') ((h7 m₁' A hr1).mono_l hρ)
      · have ⟨c, lej⟩ := ih2 m₁' A hr1 hρ (a7 m₂' A hr2)
        exact mk (le1.trans (TShape.Join.mk c).le.1) (le2.trans (TShape.Join.mk c).le.2) lej
    have ⟨ac, alej⟩ := ih1 hρ a5
    have ⟨b1, b2⟩ := (TShape.Join.mk hc1).le
    have ⟨b3, b4⟩ := (TShape.Join.mk ac).le
    refine have hc := .mono h3 a3 hc1; ⟨hc, ?_⟩
    refine .const h1 h2 ?_ ?_ alej hj1 fun _ _ => id
    · exact (TShape.Join.mk hc _).2 ⟨h3.trans b1, a3.trans b2⟩
    · have aty := h4.isType.join ac a4.isType
      exact .join hc1 (aty.mono_r b3 h4) (aty.mono_r b4 a4)

theorem LE_Interp.compat (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) : m₁.Compat m₂ :=
  (compat_join .rfl H1 H2).1

/-- **Co-realizing the same term does NOT give a common sort.**  This refutes the
`LE_Interp`-relative repair of the join family in its naive form.

The escape is `LE_Interp.bvar : m <= rho i -> LE_Interp rho m (.bvar i)`, which puts no
condition on `rho` at all.  `cxA.Compat cxA'` holds, so `WShape.Compat.iff` hands us an upper
bound -- their join -- and setting `rho i` to it makes *both* realize `.bvar i` under the
*same* valuation.  The join is classified by no sort, so `IsType.common_of_le` does not apply
and no common sort exists.

The co-realizability argument recorded in the banner (both shapes must factor through
`Const.indTy` at the same head constant, forcing one boolean to two values) is correct *for
`.indTy` shapes reached through `Const`*.  It does not reach `bvar`, where the shape comes
from the valuation and nothing forces it through `Const` at all.

**The defect is that `compat_join` quantifies over an arbitrary `rho` with no
well-formedness hypothesis** -- the same shape of defect as `SExpr.IsDefEq.strong`'s missing
`Ctx.WF` and `VEnv.Params.pat_wf`'s missing `OnCtx`, now on valuations rather than contexts.
`rho i := cxA.join cxA'` is a shape that has no type at all; `Valuation.Fits` never produces
one, but `compat_join` does not ask for `Fits`. -/
private theorem le_interp_common_fails :
    ¬ ∀ {n : Nat} {ρ : Valuation} {A : SExpr} {a a' : WShape n},
        LE_Interp ρ a.T A → LE_Interp ρ a'.T A → a.IsType → a'.IsType →
        ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r) := by
  intro H
  have hC : WShape.Compat (⟨cxA, cxA_wf⟩ : WShape 2) ⟨cxA', cxA'_wf⟩ := by
    show Shape.Compat cxA cxA' = true; rfl
  have hJ := WShape.Join.mk hC
  have := H (ρ := fun _ => (WShape.join ⟨cxA, cxA_wf⟩ ⟨cxA', cxA'_wf⟩).T) (A := .bvar 0)
    (.bvar (WShape.LE.T hJ.le.1)) (.bvar (WShape.LE.T hJ.le.2))
    ⟨false, by show Shape.hasType cxA (.sort false) = true; rfl⟩
    ⟨true, by show Shape.hasType cxA' (.sort true) = true; rfl⟩
  obtain ⟨r, h1, h2⟩ := this
  simp only [WShape.HasType, WShape.sort] at h1 h2
  cases r
  · exact Bool.noConfusion h2
  · exact Bool.noConfusion h1

theorem LE_Interp.join' (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ (m₁.join m₂) M :=
  (compat_join .rfl H1 H2).2

theorem LE_Interp.join (J : m₁.Join m₂ m) (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ m M :=
  (H1.join' H2).mono ((J _).2 (TShape.Join.mk (H1.compat H2)).le)

theorem LE_Interp.subst : LE_Interp ρ m (M.subst σ) ↔
    ∃ ρ', LE_Interp ρ' m M ∧ ∀ i, LE_Interp ρ (ρ' i) (σ i) := by
  refine ⟨fun H => ?_, ?_⟩
  · suffices ∀ {ρ m N}, LE_Interp ρ m N → ∀ (M : SExpr) (σ : Subst), M.subst σ = N →
        ∃ ρ', LE_Interp ρ' m M ∧ ∀ i, LE_Interp ρ (ρ' i) (σ i) from this H M σ rfl
    intro ρ m N H M σ eq
    have bvar {ρ : Valuation} {m N} {σ : Subst} {j} (hσj : σ j = N) (hN : LE_Interp ρ m N) :
        ∃ ρ', LE_Interp ρ' m (.bvar j) ∧ ∀ i, LE_Interp ρ (ρ' i) (σ i) := by
      refine ⟨fun k => if k = j then m else ⟨0, .bot⟩, .bvar (if_pos rfl ▸ .rfl), fun k => ?_⟩
      dsimp; split <;> rename_i ek
      · subst ek; exact hσj ▸ hN
      · exact .bot
    induction H generalizing M σ with
    | bot => exact ⟨.nil, .bot, fun _ => .bot⟩
    | sort h1 =>
      cases M with | bvar => exact bvar eq (.sort h1) | sort => ?_ | _ => cases eq
      cases eq; exact ⟨.nil, .sort h1, fun _ => .bot⟩
    | bvar h1 => cases M with | bvar => exact bvar eq (.bvar h1) | _ => cases eq
    | app hf ha h1 ih_f ih_a =>
      cases M with | bvar => exact bvar eq (.app hf ha h1) | app F' A' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ₁, hF, h₁⟩ := ih_f F' σ rfl
      have ⟨ρ₂, hA, h₂⟩ := ih_a A' σ rfl
      have hc : ρ₁.Compat ρ₂ := fun i => (h₁ i).compat (h₂ i)
      have ⟨hj1, hj2⟩ := hc.le_join
      refine ⟨ρ₁.join ρ₂, .app (hF.mono_l hj1) (hA.mono_l hj2) h1, fun i => ?_⟩
      exact (h₁ i).join' (h₂ i)
    | @lam ρ n₁ a A f F m_orig ha hdom hbody h1 ih_a ih_body =>
      cases M with | bvar => exact bvar eq (.lam ha hdom hbody h1) | lam A' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', LE_Interp ρ' a.T A' ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
          ∀ x ∈ f, LE_Interp (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', ha', hρ, H⟩ := this
        refine ⟨ρ', .lam ha' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l (Valuation.LE.push.2 ⟨.rfl, a1.T⟩)
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρA, ha', hρA⟩ := ih_a A' σ rfl
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', LE_Interp ρ' a.T A' ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              LE_Interp (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with | nil => exact ⟨ρA, ha', hρA, nofun⟩ | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, ha₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, ha₂.mono_l hj2, fun i => (hρ₁' i).join' (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        exact hy.mono_l <| by
          rw [← (show ρ₁'.push (ρ₁ 0) = ρ₁ by funext i; cases i <;> rfl)]
          exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | @forallE ρ n₁ b B b' f F m_orig hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      cases M with
      | bvar => exact bvar eq (.forallE hb hb' hdom hbody h1) | forallE B' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', LE_Interp ρ' b.T B' ∧ LE_Interp ρ' b'.T B' ∧
          (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧ ∀ x ∈ f, LE_Interp (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', hb, hb', hρ, H⟩ := this
        refine ⟨ρ', .forallE hb hb' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.T⟩
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρ₁, hb₁, hρ₁⟩ := ih_b B' σ rfl
      have ⟨ρ₂, hb₂, hρ₂⟩ := ih_b' B' σ rfl
      have hc₀ : ρ₁.Compat ρ₂ := fun i => (hρ₁ i).compat (hρ₂ i)
      have ⟨hj1₀, hj2₀⟩ := hc₀.le_join
      let ρ₀ := ρ₁.join ρ₂
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', LE_Interp ρ' b.T B' ∧ LE_Interp ρ' b'.T B' ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              LE_Interp (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with
      | nil => exact ⟨ρ₀, hb₁.mono_l hj1₀, hb₂.mono_l hj2₀,
          fun i => (hρ₁ i).join' (hρ₂ i), fun _ h => absurd h List.not_mem_nil⟩
      | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, hb₂, hb'₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, hb₂.mono_l hj2, hb'₂.mono_l hj2,
        fun i => (hρ₁' i).join' (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        refine hy.mono_l ?_
        rw [← show ρ₁'.push (ρ₁ 0) = ρ₁ from by funext i; cases i <;> rfl]
        exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | const h1 h2 h3 h4 h5 h6 h7 ih1 ih2 =>
      cases M with
      | bvar => exact bvar eq (.const h1 h2 h3 h4 h5 h6 h7) | const => ?_ | _ => cases eq
      cases eq
      refine ⟨.nil, .const h1 h2 h3 h4 ?_ h6.closed fun m e ⟨a1, a2⟩ => ?_, fun _ => .bot⟩
      · exact (closed_iff (Params.henv.closedC h1).mkS.instL).1 h5
      · exact (closed_iff a1).1 (h7 m e a2)
  · rintro ⟨ρ', H, h⟩
    induction H generalizing ρ σ with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact (h _).mono h1
    | app hf ha h1 ih_f ih_a => exact .app (ih_f h) (ih_a h) h1
    | lam ha hdom hbody h1 ih_a ih_body =>
      refine .lam (ih_a h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | forallE hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b h) (ih_b' h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ h6.closed fun _ _ ⟨a1, a2⟩ => ?_
      · exact (Params.henv.closedC h1).mkS.instL.subst_eq .zero ▸ ih1 h
      · exact a1.subst_eq .zero ▸ ih2 _ _ a2 h

theorem LE_Interp.inst : LE_Interp ρ f (F.inst A) ↔
    ∃ a, LE_Interp (ρ.push a) f F ∧ LE_Interp ρ a A := by
  refine ⟨fun H => ?_, fun ⟨a, hF, hA⟩ => ?_⟩
  · have ⟨ρ', hF, hσ⟩ := LE_Interp.subst.1 H
    refine ⟨_, hF.mono_l ?_, hσ 0⟩
    intro | 0 => exact .rfl | i+1 => exact (bvar_iff.1 (hσ (i+1)) :)
  · exact (LE_Interp.subst (σ := .one A)).2 ⟨_, hF, fun | 0 => hA | _+1 => .bvar'⟩

theorem LE_Interp.forallE_inv {b} {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    LE_Interp ρ b.T B ∧ ∀ {{X x}}, LE_Interp ρ x.T X → LE_Interp ρ (f.app x).T (F.inst X) := by
  let .forallE (n := n') (f := f₁) hb₁ hb₂ hd hiB le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have ⟨hle_b, hle_f⟩ := TShape.LE.forallE_decomp le
  refine ⟨hb₁.mono ((TShape.LE.def le₁ le₂).2 hle_b), fun X x hx => ?_⟩
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _
    (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    show (x₁w.lift _).1 ≤ (x'.lift _).1
    rw [WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have le2_T : x₁w.T ≤ x'.T := (TShape.LE.def le₂ le₁).2 le2_w
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiB x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans le2_T⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono ?_
  show (f.app x).T ≤ (f₁.app x₁w).T
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    change ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem LE_Interp.forallE_inv' {b} {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    LE_Interp ρ b.T B ∧ ∀ x, LE_Interp (ρ.push x.T) (f.app x).T F := by
  refine ⟨H.forallE_inv.1, fun x => ?_⟩
  have := (LE_Interp.weak (x := x.T) H).forallE_inv.2 .bvar0
  rwa [SExpr.inst, SExpr.subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

theorem LE_Interp.lam_inv {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.lam' f)) (.lam B F))
    {{X x}} (hx : LE_Interp ρ x.T X) : LE_Interp ρ (f.app x).T (F.inst X) := by
  unfold WShape.lam' at H; split at H <;> rename_i hn; rotate_left
  · by_cases hl : f.app x ≤ .bot; · exact .mono hl.T .bot
    have ⟨_, _, h⟩ := f.app_eq x; exact absurd ⟨_, h, hl⟩ hn
  let .lam (n := n') (f := f₁) _ hd hiF le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have hle_f : f.lift (max n n') ≤ f₁.lift (max n n') := by
    rw [WShape.lam_eq_lam' (hl := hn)] at le; exact le.lam'_decomp
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _ (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    rw [WShape.LE.def, WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiF x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans ((TShape.LE.def le₂ le₁).2 le2_w)⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono (?_ : (f.app x).T ≤ (f₁.app x₁w).T)
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    show ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem LE_Interp.lam_inv' {f : WShapeFun n} {hl : f.NonZero} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (WShape.lam f hl)) (.lam B F)) (x : WShape n) :
    LE_Interp (ρ.push x.T) (f.app x).T F := by
  have := (WShape.lam_eq_lam' ▸ LE_Interp.weak (x := x.T) H).lam_inv .bvar0
  rwa [SExpr.inst, SExpr.subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

inductive Valuation.Fits : (Γ Δ : List SExpr) → Valuation → Prop
  | nil : Valuation.Fits Γ Γ .nil
  | cons : Valuation.Fits Γ Δ ρ →
    (∀ {a}, LE_Interp ρ a A → ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.IsType) →
    LE_Interp ρ a A → x.HasType a →
    Valuation.Fits Γ (A::Δ) (ρ.push x)

def InterpTyped (ρ : Valuation) (m : TShape) (M A : SExpr) :=
  ∃ m' a, m ≤ m' ∧ LE_Interp ρ m' M ∧ LE_Interp ρ a A ∧ m'.HasType a

theorem InterpTyped.bot : InterpTyped ρ (WShape.T (n := n) .bot) M A := by
  refine ⟨WShape.T (n := n) .bot, WShape.T (n := n) .bot, TShape.bot_le', .bot, .bot, ?_⟩
  exact WShape.HasType.T_iff.2 <| WShape.HasType.bot_iff.2 ⟨true,
    WShape.HasType.bot_iff.2 ⟨true, WShape.HasType.sort⟩⟩

theorem InterpTyped.mk (le : m ≤ m') (h_m : LE_Interp ρ m' M) (h_a : LE_Interp ρ a A)
    (h_type : m'.HasType a) : InterpTyped ρ m M A := ⟨_, _, le, h_m, h_a, h_type⟩

theorem InterpTyped.out (H : InterpTyped ρ m M A) :
    ∃ n', ∃ m' : WShape n', ∃ a : WShape n', m.1 ≤ n' ∧ m ≤ m'.T ∧
      LE_Interp ρ m'.T M ∧ LE_Interp ρ a.T A ∧ m'.HasType a := by
  obtain ⟨m', a, hle, hm, ha, hty⟩ := H
  let k := max m.1 (max m'.1 a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  refine ⟨k, m'.2.lift k, a.2.lift k, hk.1, ?_, hm.lift hk.2.1, ha.lift hk.2.2, ?_⟩
  · exact hle.trans (TShape.lift_eqv hk.2.1).2
  · exact (TShape.HasType.def hk.2.1 hk.2.2).1 hty

theorem InterpTyped.hsort' {ρ A U}
    (H : ∀ {a}, LE_Interp ρ a A → InterpTyped ρ a A (.sort U))
    {a} (h : LE_Interp ρ a A) :
    ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType (.sort (U ≠ .zero)) :=
  have ⟨_, _, h1, h2, h3, h4⟩ := H h; ⟨_, h1, h2, .mono_r h3.le_sort .sort h4⟩

theorem InterpTyped.hsort {ρ A U}
    (H : ∀ {a}, LE_Interp ρ a A → InterpTyped ρ a A (.sort U))
    {a} (h : LE_Interp ρ a A) : ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.IsType :=
  have ⟨a', h1, h2, h3⟩ := hsort' H h; ⟨a', h1, h2, _, h3⟩

/-- **The true form of `IsType.common`, and the one a call site can actually discharge.**

`cx_refutes` kills the `Compat`-only form and `le_interp_common_fails` kills the
"both realize the same term" form.  What works is neither: the common sort comes from the
TERM'S UNIVERSE, not from the shapes and not from a common upper bound.

`InterpTyped.hsort'` gives, for *each* shape realizing `A`, an upper bound classified at
`.sort (U <> .zero)` -- and that boolean is a function of `U`, the universe `A` lives at, so
it is the SAME for both shapes.  `HasType.retype` then pulls the classification back down each
bound separately.  No join is taken, so there is no circularity: the earlier plan of joining
the two shapes and asking `hsort'` for a bound above the join needs `LE_Interp.join'`, which
is `compat_join.2` and therefore one of the broken sites. -/
theorem LE_Interp.common_sort {ρ A U} {a a' : WShape n}
    (H : ∀ {b}, LE_Interp ρ b A → InterpTyped ρ b A (.sort U))
    (h : LE_Interp ρ a.T A) (h' : LE_Interp ρ a'.T A)
    (ha : a.IsType) (ha' : a'.IsType) :
    ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r) := by
  have ⟨_, le₁, _, hz₁⟩ := InterpTyped.hsort' H h
  have ⟨_, le₂, _, hz₂⟩ := InterpTyped.hsort' H h'
  have ⟨_, hr₁⟩ := ha
  have ⟨_, hr₂⟩ := ha'
  exact ⟨_,
    TShape.HasType.sort_r.1 (TShape.HasType.retype (TShape.HasType.sort_r.2 hr₁) hz₁ le₁),
    TShape.HasType.sort_r.1 (TShape.HasType.retype (TShape.HasType.sort_r.2 hr₂) hz₂ le₂)⟩

theorem LE_Interp.sound_bot :
    (LE_Interp ρ (WShape.T (n := n) .bot) M ↔ LE_Interp ρ (WShape.T (n := n) .bot) N) ∧
    (LE_Interp ρ (WShape.T (n := n) .bot) M → InterpTyped ρ (WShape.T (n := n) .bot) M A) :=
  ⟨⟨fun _ => .bot, fun _ => .bot⟩, fun _ => .bot⟩

theorem LE_Interp.sound_app
    (H1 : ∀ {m}, LE_Interp ρ m F → InterpTyped ρ m F (.forallE A B))
    (H2 : ∀ {b}, LE_Interp ρ b (B.inst X) →
      ∃ b', b ≤ b' ∧ LE_Interp ρ b' (B.inst X) ∧ b'.IsType)
    (h1 : LE_Interp ρ m (F.app X)) : InterpTyped ρ m (F.app X) (B.inst X) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => exact .bot | app h1 h2 h3
  rename_i nf f_shape a_sh
  have ⟨f_ts, s_ts, le_f, a2, a3, a4⟩ := H1 h1
  have hf : ¬f_ts ≤ .bot := fun h => by
    rw [show f_shape = .bot from TShape.le_bot.1 (le_f.trans h), WShape.bot_app] at h3
    exact hm (h3.trans TShape.bot_le')
  have hs : ¬s_ts ≤ .bot := fun h => hf (a4.bot_r' h)
  cases a3 with | bot => cases hs TShape.bot_le' | forallE b1 b2 b3 b4 b5
  rename_i npi b_pi b_pi' f_pi
  cases b5.le_forall with | bot b5 => cases hs b5 | @forallE m _ _ _ _ b5 b6
  obtain c1 | ⟨n₂, g_lam, rfl, c1⟩ := a4.ty_forallE_inv; · cases hf (c1 ▸ .rfl)
  let k := max (max n₂ m) (max npi nf)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have a3' := LE_Interp.forallE b1 b2 b3 b4 (TShape.lift_eqv (Nat.succ_le_succ hk.2.1)).1
  rw [WShape.lift_forallE hk.2.1] at a3'
  have h_Binst := a3'.forallE_inv.2 (h2.lift hk.2.2)
  have ⟨a', le', g1, g2⟩ := H2 h_Binst
  have c1 := (TShape.HasTypeLam.def hk.1.1 hk.1.2).1 c1
  have c1_d := WShape.HasDom.iff.1 c1.2.1
  have c1_f := (WShape.HasTypeLam.iff.1 c1).2.2
  have ⟨_, e1, e2, e3⟩ := c1_d (a_sh.lift k)
  refine ⟨_, a', ?_, .app' (a2.lift (Nat.succ_le_succ hk.1.1)) (h2.lift hk.2.2), g1, ?_⟩
  · refine h3.trans <| TShape.app_mono ?_ (TShape.lift_eqv hk.2.2).2
    exact le_f.trans (TShape.lift_eqv (Nat.succ_le_succ hk.1.1)).2
  · have b6 := (TShapeFun.LE.def hk.1.2 hk.2.1).1 b6
    rw [WShape.lift_lam' hk.1.1, WShape.lam'_app]
    have ⟨_, g2'⟩ := g2
    refine g2'.mono_r ((WShapeFun.app_mono_l b6 _).trans (WShapeFun.app_mono_r e1) |>.T.trans le') ?_
    exact (WShape.HasTypeLam.iff.1 c1).2.2 _ e2 |>.mono_l (WShapeFun.app_mono_r e1) e3 |>.T

theorem LE_Interp.sound_lam
    (H1 : ∀ {m}, LE_Interp ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp ρ a' A ∧ a'.IsType)
    (H2 : ∀ {a x}, LE_Interp ρ a A → x.HasType a →
      ∀ {e}, LE_Interp (ρ.push x) e F → InterpTyped (ρ.push x) e F B)
    (h1 : LE_Interp ρ m (A.lam F)) : InterpTyped ρ m (A.lam F) (A.forallE B) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @lam _ n a _ f _ _ h1 h2 h3 h4
  have ⟨a', a1, a2, a3⟩ := H1 h1
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ LE_Interp (ρ.push p.1.T) p.2.T F) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' b : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (a.lift k) ∧ WShape.HasDom b (a.lift k) ∧
        (∀ x, x.HasType (a.lift k) → LE_Interp (ρ.push x.T) (f'.app x).T F) ∧
        (∀ x, x.HasType (a.lift k) → LE_Interp (ρ.push x.T) (b.app x).T B) ∧
        (∀ x, x.HasType (a.lift k) → (f'.app x).HasType (b.app x)) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h2 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h3 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', b, hsingle, hd1, hd2, hi1, hi2, hi3⟩ := H _ (Nat.le_refl _)
    have h1' := h1.lift le
    refine ⟨_, _, ?_, .lam' h1' hd1 hi1, .forallE' h1' h1' hd2 hi2, ?_⟩
    · refine h4.trans <| (TShape.LE.lift_l (Nat.succ_le_succ le)).2 (WShape.lift_lam' le ▸ ?_)
      refine WShape.lam'_le_lam'.2 <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 (hsingle _ (WShapeFun.mem_elems.2 h₀))
    · exact WShape.HasType.T <| .lam <| WShape.HasTypeLam.iff.2
        ⟨WShape.HasTypePi.iff.2 ⟨hd2, fun x h => (hi3 x h).isType⟩, hd1, hi3⟩
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    have ha : (a.lift k).IsType :=
      have ⟨r, hr⟩ := WShape.HasDom.isType h2
      ⟨r, WShape.lift_sort.symm ▸ (WShape.HasType.lift hk).2 hr⟩
    refine ⟨.bot, .bot, nofun, .bot ha, .bot ha, fun x h => ?_, fun x h => ?_, fun x h => ?_⟩
    · exact WShapeFun.bot_app ▸ .bot
    · exact WShapeFun.bot_app ▸ .bot
    · simp [WShapeFun.bot_app]; exact .bot_bot
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h2 p.1
    have ⟨e', b', le_e, he', hb', heb'⟩ := H2 h1 (WShape.HasType.T hx') (h3 x' hx')
    let m' := max e'.1 b'.1; have ⟨lf, lb⟩ := Nat.max_le.1 (Nat.le_refl m')
    refine ⟨k₁.max m', Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk : n ≤ k := Nat.le_trans le1 le₁
    have le_ek := Nat.le_trans lf le₂; have le_bk := Nat.le_trans lb le₂
    have ⟨f₁, b₁, hsingle₁, hd1₁, hd2₁, hi1₁, hi2₁, hi3₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (e'.2.lift k)
    let sb := WShapeFun.single (x'.lift k) (b'.2.lift k)
    have hi1_any z : LE_Interp (ρ.push z.T) (f₁.app z).T F :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
    have hi2_any z : LE_Interp (ρ.push z.T) (b₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd2₁ z
      (hi2₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
    have he'_at_x' : LE_Interp (ρ.push (x'.lift k).T) (e'.2.lift k).T F :=
      (he'.lift le_ek).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩)
    have hb'_at_x' : LE_Interp (ρ.push (x'.lift k).T) (b'.2.lift k).T B :=
      (hb'.lift le_bk).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩)
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = e'.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have hcb : b₁.Compat sb := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sb_app : sb.app z = b'.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sb_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi2_any z).compat (sb_app ▸ hb'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    have jb := WShapeFun.Join.mk hcb
    refine ⟨f₁.join sf, b₁.join sb, ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le_ek).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine hd2₁.join' ?_ jb (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine LE_Interp.join (jb.app_l x).T (hi2_any x) (WShapeFun.single_app ▸ ?_); split
      · exact hb'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · have hT1 := hi3₁ x hx
      have hT2 : (sf.app x).HasType (sb.app x) := by
        rw [WShapeFun.single_app, WShapeFun.single_app]; split
        · exact (TShape.HasType.def le_ek le_bk).1 heb'
        · exact .bot_bot
      have jb_x := jb.app_l x
      have := hT1.isType.join' jb_x hT2.isType
      exact (this.mono_r jb_x.le.1 hT1).join' (jf.app_l x) (this.mono_r jb_x.le.2 hT2)

theorem LE_Interp.sound_forallE
    (H1 : ∀ {m}, LE_Interp ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType (.sort (u ≠ .zero)))
    (H2 : ∀ {a x}, LE_Interp ρ a A → x.HasType a →
      ∀ {e}, LE_Interp (ρ.push x) e B → InterpTyped (ρ.push x) e B (.sort v))
    (h1 : LE_Interp ρ m (A.forallE B)) :
    InterpTyped ρ m (A.forallE B) (.sort (.imax u v)) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @forallE _ n b₀ _ b f _ _ h1 h2 h3 h4 h5
  have ⟨a', a1, a2, a3⟩ := H1 h2
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ LE_Interp (ρ.push p.1.T) p.2.T B) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (b.lift k) ∧
        (∀ x, x.HasType (b.lift k) → LE_Interp (ρ.push x.T) (f'.app x).T B) ∧
        (∀ x, x.HasType (b.lift k) → (f'.app x).HasType (.sort (v ≠ .zero))) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h3 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h4 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', hsingle, hd1, hi1, hi2⟩ := H _ (Nat.le_refl _)
    have hJ := WShape.Join.mk <| WShape.Compat.T_iff.2 <| h1.compat h2
    have ⟨b₂, c1, c2, c3⟩ := H1 (h1.join hJ.T h2)
    let k := max n' b₂.1; have ⟨le₂, le₁⟩ := Nat.max_le.1 (Nat.le_refl k)
    have b2' := (WShape.HasDom.lift le₂).2 hd1
    refine ⟨((b₂.2.lift k).forallE (f'.lift k)).T, _, h5.trans ?_, ?_, .sort .rfl, ?_⟩
    · rw [TShape.LE.lift_l (Nat.succ_le_succ (Nat.le_trans le le₂)),
        WShape.lift_forallE (Nat.le_trans le le₂)]
      refine WShape.forallE_le_forallE.2 ⟨?_, WShapeFun.lift_lift (.inl le) ▸ ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.1.T.trans c1)
      refine WShapeFun.lift_mono le₂ <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 <| hsingle _ (WShapeFun.mem_elems.2 h₀)
    · refine .forallE' (c2.lift le₁) ((h2.lift le).lift le₂) b2' fun x h => ?_
      have ⟨x', d1, dmem⟩ := (f'.lift k).app_eq x
      refine .mono (WShapeFun.app_of_mem dmem).2.T ?_
      obtain ⟨z₀, -, -, rfl, -⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1 z₀
      refine WShapeFun.lift_app le₂ ▸ .lift (m := (f'.app _).T) le₂ ?_
      refine hi1 _ z'ht |>.mono z'app.T |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
      exact z'le.T.trans <| (TShape.LE.lift_l le₂).2 d1
    · apply (TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _)).2
      simp only [WShape.lift_self, TShape.sort, WShape.lift_sort, ne_eq, SLevel.imax_eq_zero]
      have b2' := WShape.lift_lift (.inl le) ▸ b2'
      have := (TShape.HasType.def le₁ (Nat.zero_le k)).1 c3
      refine .forallE <| WShape.HasTypePi.iff.2 ⟨b2'.mono_r ?_ this, fun x hx => ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.2.T.trans c1)
      have ⟨x', _, dmem⟩ := (f'.lift k).app_eq x
      obtain ⟨x', y', e1, rfl, eq⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨e2, e3⟩ := WShapeFun.app_of_mem e1
      refine eq ▸ WShape.lift_sort.symm ▸ (WShape.HasType.lift le₂).2 (.mono_l e2 e3 ?_)
      have ⟨y, d1, d2, d3⟩ := WShape.HasDom.iff.1 hd1 x'
      exact (hi2 _ d2).mono_l (WShapeFun.app_mono_r d1) d3
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    refine ⟨.bot, nofun, .bot ?_, fun x h => WShapeFun.bot_app ▸ .bot, fun x h => ?_⟩
    · have ⟨r, hr⟩ := WShape.HasDom.isType h3
      exact ⟨r, by simpa [WShape.lift_sort] using (WShape.HasType.lift hk).2 hr⟩
    · simp [WShapeFun.bot_app]; exact .bot' .sort
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h3 p.1
    have ⟨f'x, _, le_e, he', hb', heb'⟩ := H2 h2 hx'.T (h4 x' hx')
    replace heb' : f'x.HasType (.sort (v ≠ .zero)) := .mono_r hb'.le_sort .sort heb'
    refine ⟨k₁.max f'x.1, Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk := Nat.le_trans le1 le₁
    have ⟨f₁, hsingle₁, hd1₁, hi1₁, hi2₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (f'x.2.lift k)
    have hi1_any z : LE_Interp (ρ.push z.T) (f₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T z'le⟩)
    have he'_at_x' : LE_Interp (ρ.push (x'.lift k).T) (f'x.2.lift k).T B :=
      (he'.lift le₂).mono_l <| Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = f'x.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    refine ⟨f₁.join sf, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le₂).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine (hi2₁ x hx).join' (jf.app_l x) (WShapeFun.single_app ▸ ?_); split
      · exact (TShape.HasType.def le₂ (Nat.zero_le k)).1 heb'
      · exact .bot' .sort

def SoundEq (Γ : List SExpr) (M N : SExpr) : Prop :=
  ∀ {{Γ₀ ρ}}, Valuation.Fits Γ₀ Γ ρ → ∀ {m}, LE_Interp ρ m M ↔ LE_Interp ρ m N
def SoundTy (Γ : List SExpr) (M A : SExpr) : Prop :=
  ∀ {{Γ₀ ρ}}, Valuation.Fits Γ₀ Γ ρ → ∀ {m}, LE_Interp ρ m M → InterpTyped ρ m M A

mutual
inductive StrongSound : List SExpr → SExpr → SExpr → Prop where
  | mk : Γ ⊢ M : A → SoundTy Γ M A →
    StrongSoundCore Γ M A' → SoundEq Γ A' A → StrongSound Γ M A

inductive StrongSoundCore : List SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → StrongSoundCore Γ (.bvar i) A
  | sort : StrongSoundCore Γ (.sort l) (.sort (.succ l))
  | lam : SoundTy Γ A (.sort u) →
    StrongSound (A::Γ) e B → StrongSoundCore Γ (.lam A e) (.forallE A B)
  | const : Params.env.constants c = some ci → ls.length = ci.uvars →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, SoundEq Γ ((SExpr.mk ci.type).instL ls) ((F cl).rhs ls)) →
    (∀ cl, StrongSound Γ ((F cl).rhs ls) (.sort (F cl).u)) →
    StrongSoundCore Γ (.const c ls) ((SExpr.mk ci.type).instL ls)
  | app : SoundTy Γ A (.sort u) →
    StrongSound Γ f (.forallE A B) → StrongSound Γ a A →
    StrongSoundCore Γ (.app f a) (B.inst a)
  | forallE : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) →
    StrongSoundCore Γ (.forallE A B) (.sort (.imax u v))
end
structure StrongSoundEq (Γ : List SExpr) (M N A : SExpr) : Prop where
  defeq : Γ ⊢ M ≡ N : A
  sound : SoundEq Γ M N
  left : StrongSound Γ M A
  right : StrongSound Γ N A

protected theorem SoundEq.rfl : SoundEq Γ M M := fun _ _ _ _ => .rfl
theorem SoundEq.symm : SoundEq Γ M N → SoundEq Γ N M := fun H _ _ W _ => (H W).symm
theorem StrongSoundEq.hasType : StrongSoundEq Γ M N A → StrongSound Γ M A ∧ StrongSound Γ N A
  | ⟨_, _, h1, h2⟩ => ⟨h1, h2⟩
theorem StrongSoundEq.symm : StrongSoundEq Γ M N A → StrongSoundEq Γ N M A
  | ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h2.symm, h4, h3⟩
theorem StrongSound.defeq : StrongSound Γ M A → Γ ⊢ M : A
  | ⟨h, _, _, _⟩ => h
theorem StrongSound.sound : StrongSound Γ M A → SoundTy Γ M A
  | ⟨_, h, _, _⟩ => h
theorem StrongSoundEq.rfl (H : StrongSound Γ M A) : StrongSoundEq Γ M M A :=
  ⟨H.defeq, .rfl, H, H⟩
theorem SoundEq.trans (H1 : SoundEq Γ M N) (H2 : SoundEq Γ N P) : SoundEq Γ M P :=
  fun _ _ W _ => (H1 W).trans (H2 W)
theorem StrongSoundEq.trans :
    StrongSoundEq Γ M N A → StrongSoundEq Γ N P A → StrongSoundEq Γ M P A
  | ⟨a1, a2, a3, _⟩, ⟨b1, b2, _, b4⟩ => ⟨.trans a1 b1, a2.trans b2, a3, b4⟩
theorem SoundTy.defeq_l (H1 : SoundEq Γ M N) (H : SoundTy Γ M A) : SoundTy Γ N A := fun _ _ W _ h =>
  have ⟨_, _, a1, a2, a3, a4⟩ := H W ((H1 W).2 h); ⟨_, _, a1, (H1 W).1 a2, a3, a4⟩
theorem SoundTy.defeq_r (H1 : SoundEq Γ A B) (H : SoundTy Γ M A) : SoundTy Γ M B := fun _ _ W _ h =>
  have ⟨_, _, a1, a2, a3, a4⟩ := H W h; ⟨_, _, a1, a2, (H1 W).1 a3, a4⟩

theorem StrongSoundEq.mk' (h1 : Γ ⊢ M ≡ N : A)
    (h2 : StrongSoundCore Γ M A₁) (h2' : SoundEq Γ A₁ A)
    (h3 : StrongSoundCore Γ N A₂) (h3' : SoundEq Γ A₂ A)
    (h4 : ∀ {{Γ₀ ρ}}, Valuation.Fits Γ₀ Γ ρ → ∀ {m},
      (LE_Interp ρ m M ↔ LE_Interp ρ m N) ∧ (LE_Interp ρ m M → InterpTyped ρ m M A)) :
    StrongSoundEq Γ M N A := by
  refine have ha := ?_; have ht := ?_
    ⟨h1, ha, ⟨h1.hasType.1, ht, h2, h2'⟩, h1.hasType.2, ht.defeq_l ha, h3, h3'⟩
  · exact fun _ _ W _ => (h4 W).1
  · exact fun _ _ W _ => (h4 W).2

theorem SoundEq.inst (ht : SoundTy Γ X A) (hA : SoundTy Γ A (.sort u))
    (H : SoundEq (A::Γ) M N) : SoundEq Γ (M.inst X) (N.inst X) := fun _ ρ W m => by
  suffices ∀ M N, SoundEq (A::Γ) M N → LE_Interp ρ m (M.inst X) → LE_Interp ρ m (N.inst X) from
    ⟨this _ _ H, this _ _ H.symm⟩
  simp only [LE_Interp.inst]; intro M N H ⟨x, h1, h2⟩
  have ⟨x', a, a1, a2, a3, a4⟩ := ht W h2
  refine ⟨_, (H (W.cons (InterpTyped.hsort (hA W)) a3 a4)).1 ?_, a2⟩
  exact h1.mono_l <| Valuation.LE.push.2 ⟨.rfl, a1⟩

theorem SoundEq.sort : SoundEq Γ (.sort u) (.sort v) ↔ (u ≠ .zero ↔ v ≠ .zero) := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · injection congrArg (·.1) <| WShape.sort_le.1 <| ((H .nil).1 .sort').le_sort' with eq
    exact decide_eq_decide.1 eq
  · intro _ ρ W m
    suffices ∀ {u v}, (u ≠ .zero ↔ v ≠ .zero) →
        LE_Interp ρ m (SExpr.sort u) → LE_Interp ρ m (SExpr.sort v) from ⟨this H, this H.symm⟩
    intro u v H h; exact .mono (decide_eq_decide.2 H ▸ h.le_sort) .sort'

theorem SoundEq.forallE (hA : SoundTy Γ A (.sort u))
    (H1 : SoundEq Γ A A') (H2 : SoundEq (A::Γ) B B') :
    SoundEq Γ (.forallE A B) (.forallE A' B') := by
  intro _ ρ W m
  suffices ∀ {A₁ A₂ B₁ B₂}, SoundEq Γ A A₁ → SoundEq Γ A A₂ → SoundEq (A::Γ) B₁ B₂ →
      LE_Interp ρ m (.forallE A₁ B₁) → LE_Interp ρ m (.forallE A₂ B₂) from
    ⟨this .rfl H1 H2, this H1 .rfl H2.symm⟩
  intro A₁ A₂ B₁ B₂ H1 H2 H3 h
  cases h with | bot => exact .bot | forallE h1 h2 h3 h4 h5
  have HA := H1.symm.trans H2
  refine .forallE ((HA W).1 h1) ((HA W).1 h2) h3 (fun _ h' => ?_) h5
  exact (H3 (W.cons (InterpTyped.hsort (hA W)) ((H1 W).2 h2) h'.T)).1 (h4 _ h')

theorem SoundEq.forallE_inv (H : SoundEq Γ (.forallE A B) (.forallE A' B'))
    (hA : SoundTy Γ A (.sort u)) (hA' : SoundTy Γ A' (.sort u')) :
    SoundEq Γ A A' ∧ SoundEq (A::Γ) B B' := by
  refine have hAA _ ρ W m := ?_; ⟨hAA, fun Γ₀ ρ W m => ?_⟩
  · suffices ∀ {A A' B B' u}, SoundEq Γ (.forallE A B) (.forallE A' B') → SoundTy Γ A (.sort u) →
        LE_Interp ρ m A → LE_Interp ρ m A' from ⟨this H hA, this H.symm hA'⟩
    intro A A' B B' u H hA h
    have ⟨_, a1, a2, a3⟩ := InterpTyped.hsort (hA W) h
    have ⟨_, a3'⟩ := a3
    refine (H W).1 (.forallE' a2 a2 (.bot ⟨_, TShape.HasType.sort_r.1 a3'⟩) ?_)
      |>.forallE_inv.1.mono a1
    intro x _; simpa using .bot
  · suffices ∀ {A₁ A₂ B₁ B₂}, SoundEq Γ (.forallE A₁ B₁) (.forallE A₂ B₂) →
        SoundEq Γ A A₁ → LE_Interp ρ m B₁ → LE_Interp ρ m B₂ from ⟨this H .rfl, this H.symm hAA⟩
    intro A A' B B' H hAA h
    cases W with
    | nil =>
      have := (H .nil).1 <| .forallE' (f := .single .bot m.2) .bot .bot (WShape.HasDom.iff.2 ?_) ?_
      · have := this.forallE_inv'.2 .bot
        simp [WShapeFun.single_app] at this
        refine this.mono_l ?_; rintro ⟨⟩ <;> exact TShape.bot_eqv.1
      · refine fun _ => ⟨_, WShape.bot_le, .bot_bot, ?_⟩
        simpa [WShapeFun.single_app] using .rfl
      · intro x h'; cases h'.bot_r
        simpa [WShapeFun.single_app, show m.2.T = m from rfl] using
          h.mono_l fun _ => TShape.bot_le'
    | @cons Γ ρ A a x b1 b2 b3 b4 =>
      let k := max (max x.1 m.1) a.1
      have hk := Nat.max_le.1 (Nat.le_refl k); simp [Nat.max_le] at hk
      have b4' := (TShape.HasType.def hk.1.1 hk.2).1 b4
      have := (hAA b1).1 (b3.lift hk.2)
      have := (H b1).1 <| .forallE' (f := .single (x.2.lift k) (m.2.lift k))
        this this (WShape.HasDom.iff.2 ?_) ?_
      · have := this.forallE_inv'.2 (x.2.lift k)
        simp [WShapeFun.single_app, WShape.LE.rfl] at this
        exact this.mono (TShape.lift_eqv hk.1.2).2 |>.mono_l <|
          Valuation.LE.push.2 ⟨.rfl, (TShape.lift_eqv hk.1.1).1⟩
      · intro x'; simp [WShapeFun.single_app]
        split <;> [rename_i h; exact ⟨_, WShape.bot_le, .bot_iff.2 b4'.isType, WShape.bot_le⟩]
        refine ⟨_, h, b4', if_pos ?_ ▸ .rfl⟩; exact .rfl
      · intro x' h1; simp [WShapeFun.single_app]; split <;> [rename_i h2; exact .bot]
        refine h.mono (TShape.lift_eqv hk.1.2).1 |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
        exact (TShape.LE.lift_l hk.1.1).2 h2

theorem StrongSound.uniq_of_core
    (H : ∀ {A B}, StrongSoundCore Γ M A → StrongSoundCore Γ M B → SoundEq Γ A B) :
    StrongSound Γ M A → StrongSound Γ M B → SoundEq Γ A B
  | ⟨_, _, a3, a4⟩, ⟨_, _, b3, b4⟩ => a4.symm.trans <| (H a3 b3).trans b4

theorem StrongSound.uniq : StrongSound Γ M A → StrongSound Γ M B → SoundEq Γ A B := by
  induction M generalizing Γ A B with refine uniq_of_core fun {A B} H1 H2 => ?_
  | bvar => let .bvar a1 := H1; let .bvar b1 := H2; exact a1.uniq b1 ▸ .rfl
  | sort => let .sort := H1; let .sort := H2; exact .rfl
  | const => let .const a1 .. := H1; let .const b1 .. := H2; cases a1.symm.trans b1; exact .rfl
  | app _ _ ihf =>
    let .app a1 a2 a3 := H1; let .app b1 b2 b3 := H2
    exact .inst a3.sound a1 ((ihf a2 b2).forallE_inv a1 b1).2
  | lam _ _ _ ihe => let .lam a1 a2 := H1; let .lam b1 b2 := H2; exact .forallE a1 .rfl (ihe a2 b2)
  | forallE _ _ ihA ihB =>
    let .forallE a1 a2 := H1; let .forallE b1 b2 := H2
    simp only [SoundEq.sort, ne_eq, SLevel.imax_eq_zero]
    exact SoundEq.sort.1 (ihB a2 b2)

theorem LE_Interp.apps_realize_inv (W : Valuation.Fits Γ₀ Γ ρ)
    (h_env : Params.env.constants c = some ci)
    (h_intr_defeq : SoundEq Γ ((SExpr.mk ci.type).instL ls) (List.foldr .forallE body Ts))
    (h_k_eq : List.length srev + k = Ts.length)
    (hTy : StrongSound Γ (srev.foldr (fun A acc => acc.app A) (.const c ls)) T)
    (H : LE_Interp (srev.length.repeat (·.push .bot) ρ) m
      ((Ts.drop srev.length).foldr .forallE body)) :
    LE_Interp ρ m T := by
  induction srev generalizing k m T with | cons a rest ih => ?_ | nil =>
    cases (Nat.zero_add _).symm.trans h_k_eq
    have ⟨_, _, hTy, h_T_eq_intr⟩ := hTy; have .const h_env' .. := hTy
    cases h_env'.symm.trans h_env
    exact (h_T_eq_intr.symm.trans h_intr_defeq W).2 H
  have ⟨_, _, hTy, h_T_eq⟩ := hTy; have .app _ h_fun_ty _ := hTy
  have h_k_rest : rest.length + (k + 1) = Ts.length := by
    simp only [List.length_cons] at h_k_eq; omega
  have h_lt : rest.length < Ts.length := by omega
  have h_app := ih (k := k + 1) (m := WShape.T (n := _+1) (.forallE .bot (.single .bot m.2)))
    h_k_rest h_fun_ty ?_ |>.forallE_inv.2 (X := a) .bot
  · rw [WShapeFun.single_app, if_pos .rfl] at h_app
    exact (h_T_eq W).1 h_app
  · rw [List.drop_eq_getElem_cons h_lt, List.foldr_cons]
    refine .forallE' .bot .bot ?_ ?_
    · exact WShape.HasDom.single.2 (.inl .bot_bot)
    · intro x hx; cases hx.bot_r; simp [WShapeFun.single_app]
      exact H.mono_l <| Valuation.LE.push.2 ⟨.rfl, TShape.bot_eqv.2⟩

theorem LE_Interp.apps_realize (W : Valuation.Fits Γ₀ Γ ρ)
    (mty : m'.HasType a) (ha : LE_Interp ρ a T)
    (hTy_lhs : StrongSound Γ (rAs.foldr (fun A acc => acc.app A) (.const c ls)) T)
    (hargs : List.Forall₂ (LE_Interp ρ ·.T) (rargs : List (WShape n)) rAs)
    (hC : Const c (LE_Interp ρ) rargs m') :
    LE_Interp ρ m' (rAs.foldr (fun A acc => acc.app A) (.const c ls)) := by
  generalize h_len : rargs.length = k
  induction k generalizing m' a T rAs n with | succ k ih => ?_ | zero =>
    let .nil := hargs
    have ⟨_, _, hTy, hType⟩ := hTy_lhs; have .const h1 h2 .. := hTy
    exact .const h1 h2 .rfl mty ((hType W).2 ha) hC fun _ _ => id
  let .cons (a := arg) (b := A) (l₁ := rest_r) (l₂ := rest_s) h_arg h_rest := hargs
  cases h_len
  have ⟨_, _, hTy, hC_inst⟩ := hTy_lhs; have .app _ hMf hMa := hTy
  obtain ⟨y, hya, hy⟩ := LE_Interp.inst.1 ((hC_inst W).2 ha)
  obtain ⟨n', arg', aT, _, jle, h_LE, ha', harg'⟩ := (hMa.sound W (h_arg.join' hy)).out
  let k := max (max n m'.1) (max n' a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  let arg'' := arg'.lift k; let m'' := m'.2.lift k
  let m2 : WShape (k+1) := .lam' (.single arg'' m'')
  suffices LE_Interp ρ m2.T (rest_s.foldr (fun A acc => acc.app A) (.const c ls)) by
    have h_arg'_T : LE_Interp ρ arg''.T A := h_LE.lift hk.2.1
    have h_app := this.app' h_arg'_T
    simp only [m2, WShape.lam'_app, WShapeFun.single_app, WShape.LE.rfl, ↓reduceIte] at h_app
    exact h_app.mono (TShape.lift_eqv hk.1.2).2
  have hJ := TShape.Join.mk (h_arg.compat hy)
  let aT' := aT.lift k; let a' := a.2.lift k
  let a2 : WShape (k+1) := .forallE aT' (.single arg'' a')
  have h_argw_typed : arg''.HasType aT' := (WShape.HasType.lift hk.2.1).2 harg'
  refine ih (a := a2.T) (rargs := rest_r.map (WShape.lift k)) ?_ ?_ hMf ?_ ?_ (by simp)
  · have h_m_typed := (TShape.HasType.def hk.1.2 hk.2.2).1 mty
    refine WShape.HasType.T <| .lam <| WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
    · have ⟨r, hr⟩ := WShape.HasType.isType h_m_typed
      refine ⟨r, WShape.HasTypePi.def.2
        ⟨WShape.HasDom.single.2 (.inl h_argw_typed), fun x y h => ?_⟩⟩
      obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ := WShapeFun.mem_single.1 h
      · exact hr
      · exact .bot' .sort
    · exact WShape.HasDom.single.2 (.inl h_argw_typed)
    · simp only [WShapeFun.single_app]; split <;> [exact h_m_typed; exact .bot_bot]
  · refine .forallE' (ha'.lift hk.2.1) (ha'.lift hk.2.1)
      (WShape.HasDom.single.2 (.inl h_argw_typed)) fun x _ => ?_
    rw [WShapeFun.single_app]; split <;> [rename_i h1; exact .bot]
    refine .lift hk.2.2 <| hya.mono_l (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
    exact (hJ.le.2.trans jle).trans (TShape.lift_eqv hk.2.1).2 |>.trans h1.T
  · exact List.forall₂_map_left_iff.2 <| h_rest.imp fun _ _ h => h.mono (TShape.lift_eqv hk.1.1).1
  · refine Const.lam (fun x y hmem => ?_) .rfl
    obtain ⟨⟨⟩⟩ | ⟨_, ⟨⟩⟩ := WShapeFun.mem_single.1 hmem <;> [skip; exact .bot]
    refine hC.lift hk.1.1 .mono |>.mono_l ?_ |>.mono (TShape.lift_eqv hk.1.2).1 .mono
    exact .cons ((TShape.LE.def hk.1.1 hk.2.1).1 (hJ.le.1.trans jle)) <| .rfl fun _ _ => .rfl

theorem LE_Interp.RHS.le_applyS
    (hpath : ∀ path, LE_Interp ρ (m1 path) (m2 path))
    (hR_sound : ∀ m e, R m e → LE_Interp ρ m e)
    (hRHS : LE_Interp.RHS ls m1 R m r) :
    LE_Interp ρ m (r.applyS ls m2) := by
  induction hRHS with
  | bot => exact .bot
  | const h1 => exact hR_sound _ _ h1
  | var h1 => exact (hpath _).mono h1
  | app _ _ h3 ihf iha => exact .app ihf iha h3

theorem LE_Interp.RHS.of_applyS {r : Pattern.RHS p} (hLE : LE_Interp ρ m (r.applyS ls m2)) :
    ∃ m1, (∀ path, LE_Interp ρ (m1 path) (m2 path)) ∧ LE_Interp.RHS ls m1 (LE_Interp ρ) m r := by
  induction r generalizing m with
  | fixed e cl => exact ⟨fun _ => .bot, fun _ => .bot, .const hLE⟩
  | var path =>
    classical
    refine ⟨fun p' => if p' = path then m else .bot, fun p' => ?_, ?_⟩
    · dsimp; split <;> [simpa [*]; exact .bot]
    · exact .var (by simp [TShape.LE.rfl])
  | app r_f r_a ih_f ih_a =>
    cases hLE with | bot => exact ⟨fun _ => .bot, fun _ => .bot, .bot⟩ | app hLE_f hLE_a hle_app
    obtain ⟨mf, hf, rf⟩ := ih_f hLE_f
    obtain ⟨ma, ha, ra⟩ := ih_a hLE_a
    refine ⟨fun path => (mf path).join (ma path), fun path => ?_, ?_⟩
    · exact (hf path).join' (ha path)
    · refine .app (rf.mono_l fun path => ?_) (ra.mono_l fun path => ?_) hle_app
      · exact (TShape.Join.mk ((hf path).compat (ha path))).le.1
      · exact (TShape.Join.mk ((hf path).compat (ha path))).le.2

theorem LE_Interp.Matches.of_matchesS (a2 : p.MatchesS M ls m2)
    (hWF : p.WF Params.classify top n_off) (hLE : LE_Interp ρ x M) :
    ∃ n', ∀ k, n' ≤ k → ∃ c rargs m' m_arg,
      LE_Interp.Matches (n := k) p c rargs m' ∧
      (∀ path, LE_Interp ρ (m' path) (m2 path)) ∧
      x ≤ m_arg ∧ Const c (LE_Interp ρ) rargs m_arg := by
  induction a2 generalizing x top n_off with
  | const =>
    cases hLE with | @const n _ _ _ _ _ _ _ _ _ _ hle _ _ hConst hR => ?_ | bot =>
      exact ⟨0, fun _ _ => ⟨_, [], nofun, _, .const, nofun, .rfl, .bot⟩⟩
    refine ⟨n, fun k hk => ⟨_, [], nofun, _, .const, nofun, hle, ?_⟩⟩
    exact hConst.mono (R' := LE_Interp ρ) .rfl (fun le hr => (hR _ _ hr).mono le) |>.lift hk .mono
  | var hMinner ih =>
    cases hLE with
    | bot =>
      obtain ⟨n', ih'⟩ := ih (x := .bot) hWF .bot
      refine ⟨n', fun k hk => ?_⟩
      obtain ⟨_, rargs, m', m_arg, hMatch, hpath, _⟩ := ih' k hk
      exact ⟨_, _, _, _, hMatch.var, (·.casesOn .bot hpath), TShape.bot_eqv.1, .bot⟩
    | @app _ n f _ _ _ x_arg hLE_f hLE_a hle_app
    obtain ⟨n', ih'⟩ := ih hWF hLE_f
    refine ⟨max (n + 1) n', fun k hk => ?_⟩
    have ⟨hk_app, hk⟩ := Nat.max_le.1 hk
    obtain ⟨_, rargs, m', m_arg, hMatch, hpath, hle, hConst⟩ := ih' k hk
    have hk_n : n ≤ k := Nat.le_of_succ_le hk_app
    refine ⟨_, _, _, _, hMatch.var,
      (·.casesOn (hLE_a.mono (TShape.lift_eqv hk_n).1) hpath), hle_app, ?_⟩
    cases hConst with
    | bot =>
      have hf_bot : f.T ≤ .bot := hle.trans TShape.bot_eqv.1
      have h_app_bot : (f.app x_arg).T ≤ .bot := by
        have : f = .bot := TShape.le_bot.1 hf_bot
        rw [this]; simp; exact TShape.bot_eqv.1
      refine TShape.le_bot'.1 h_app_bot ▸ .bot
    | ctor h =>
      cases top
      · injection h ▸ hMatch.head_wf_eq hWF with h_eq; injection h_eq; omega
      · cases h ▸ hMatch.head_wf_eq hWF
    | indTy h => cases top <;> cases h ▸ hMatch.head_wf_eq hWF
    | pat hP hM =>
      cases top
      · cases pat_arity hP hM.arity ▸ hMatch.head_wf_eq hWF
      · injection pat_arity hP hM.arity ▸ hMatch.head_wf_eq hWF with h_eq
        injection h_eq; omega
    | @lam f_const _ _ hRec hle_lam
    let x_arg' : WShape k := x_arg.lift k
    obtain ⟨x', hx'_le, hx'_mem⟩ := WShapeFun.app_eq f_const x_arg'
    refine hRec x' (f_const.app x_arg') hx'_mem
      |>.mono_l (.cons hx'_le <| .rfl fun _ _ => .rfl) |>.mono ?_ .mono
    rw [← WShape.lam'_app (f := f_const) (x := x_arg')]
    exact TShape.app_mono (hle.trans hle_lam) (TShape.lift_eqv hk_n).2
  | @app p_f E_f _ g_f p_a E_a _ g_a hMf hMa ihf iha =>
    cases hLE with | @app _ _ f _ _ _ x_arg hLE_f hLE_a hle_app => ?_ | bot =>
      obtain ⟨n'_f, ihf'⟩ := ihf (x := .bot) hWF.1 .bot
      obtain ⟨n'_a, iha'⟩ := iha (x := .bot) hWF.2 .bot
      refine ⟨max 1 (max n'_f (n'_a + 1)), fun k hk => ?_⟩
      have ⟨hk_one, hk_rest⟩ := Nat.max_le.1 hk
      have ⟨hk_f, hk_a_plus⟩ := Nat.max_le.1 hk_rest
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 :=
        ⟨k - 1, (Nat.sub_add_cancel hk_one).symm⟩
      have hk_a : n'_a ≤ k' := Nat.le_of_succ_le_succ hk_a_plus
      obtain ⟨_, rargs_f, mf', _, hMatch_f, hpath_f, _⟩ := ihf' (k' + 1) hk_f
      obtain ⟨_, rargs_a, ma', _, hMatch_a, hpath_a, _⟩ := iha' k' hk_a
      refine ⟨_, WShape.ctor' _ rargs_a.reverse :: rargs_f,
        Sum.elim mf' ma', _, hMatch_f.app hMatch_a, (·.casesOn hpath_f hpath_a),
        TShape.bot_eqv.1, .bot⟩
    obtain ⟨n'_f, ihf'⟩ := ihf hWF.1 hLE_f
    obtain ⟨n'_a, iha'⟩ := iha hWF.2 hLE_a
    refine ⟨max n'_f n'_a + 1, fun k hk => ?_⟩
    let k' + 1 := k; have hk := Nat.max_le.1 (Nat.le_of_succ_le_succ hk)
    let ⟨_, rargs_f, mf', _, hMatch_f, hpath_f, hle_f, hConst_f⟩ := ihf' _ (Nat.le_succ_of_le hk.1)
    let ⟨c_a, rargs_a, ma', _, hMatch_a, hpath_a, hle_a, hConst_a⟩ := iha' k' hk.2
    refine ⟨_, WShape.ctor' _ rargs_a.reverse :: rargs_f,
      Sum.elim mf' ma', (f.app x_arg).T, hMatch_f.app hMatch_a,
      (·.casesOn hpath_f hpath_a), hle_app, ?_⟩
    cases hConst_f with
    | bot =>
      have hf_bot : f.T ≤ .bot := hle_f.trans TShape.bot_eqv.1
      have h_app_bot : (f.app x_arg).T ≤ .bot := by
        simp [show f = .bot from TShape.le_bot.1 hf_bot]; exact TShape.bot_eqv.1
      exact TShape.le_bot'.1 h_app_bot ▸ .bot
    | ctor h_classify =>
      cases top
      · injection h_classify ▸ hMatch_f.head_wf_eq hWF.1 with h_eq; injection h_eq; omega
      · cases h_classify ▸ hMatch_f.head_wf_eq hWF.1
    | indTy h => cases top <;> cases h ▸ hMatch_f.head_wf_eq hWF.1
    | pat hP hM =>
      cases top
      · cases pat_arity hP hM.arity ▸ hMatch_f.head_wf_eq hWF.1
      · injection pat_arity hP hM.arity ▸ hMatch_f.head_wf_eq hWF.1 with h_eq
        injection h_eq; omega
    | @lam f' _ _ hRec hle_lam
    let arg : WShape (k' + 1) := .ctor' c_a rargs_a.reverse
    obtain ⟨x', hx'_le, hx'_mem⟩ := WShapeFun.app_eq f' arg
    refine hRec x' (f'.app arg) hx'_mem
      |>.mono_l (.cons hx'_le <| .rfl fun _ _ => .rfl) |>.mono ?_ .mono
    refine WShape.lam'_app ▸ TShape.app_mono (hle_f.trans hle_lam) (hle_a.trans ?_)
    cases hConst_a with
    | bot => exact TShape.bot_eqv.1.trans TShape.bot_le'
    | ctor _ h_bound => exact h_bound
    | pat hP hM => cases pat_arity hP hM.arity ▸ hMatch_a.head_wf_eq hWF.2
    | indTy h => cases h ▸ hMatch_a.head_wf_eq hWF.2
    | lam hRec hle_lam
    refine hle_lam.trans ?_ |>.trans TShape.bot_le
    rw [WShape.lam']; split <;> [rename_i hf; exact TShape.bot_eqv.1]
    obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
    refine hn (WShape.LE.T_iff.1 (.trans ?_ TShape.bot_eqv.2)) |>.elim
    refine (hRec s t hxy).compat_mismatch (rargs2 := rargs_a) (by simp) <| .inl ?_
    simpa using hMatch_a.head_wf_eq hWF.2

theorem LE_Interp.build_spine {m1 : p.Path → TShape} {m2}
    {ls : p.LPath → List SLevel} (a2 : p.MatchesS LHS ls m2)
    (W : Valuation.Fits Γ₀ Γ ρ) (hTy : StrongSound Γ LHS A)
    (p_wf : p.WF Params.classify top extra)
    (hpath : ∀ path, LE_Interp ρ (m1 path) (m2 path)) :
    ∃ n', ∀ k, n' ≤ k → ∃ c rargs m' rAs,
      Matches (n := k) p c rargs m' ∧ (∀ path, m1 path ≤ m' path) ∧
      List.Forall₂ (LE_Interp ρ ·.T) rargs rAs ∧
      rAs.foldr (fun A acc => .app acc A) (.const c (ls (.head p))) = LHS := by
  induction a2 generalizing A top extra with
  | const => exact ⟨0, fun k _ => ⟨_, [], nofun, [], .const, nofun, .nil, rfl⟩⟩
  | @var _ _ _ _ X _ ih =>
    have ⟨_, _, hTy, _⟩ := hTy; have .app _ hTy_inner _ := hTy
    obtain ⟨n', ih⟩ := ih hTy_inner p_wf (hpath <| .some ·)
    refine ⟨max n' (m1 none).1, fun k hk => ?_⟩
    have ⟨hk_inner, hk_none⟩ := Nat.max_le.1 hk
    obtain ⟨_, _, m', spine, hMatch, hpath', forall2, foldr_eq⟩ := ih _ hk_inner
    let a_top : WShape k := (m1 none).2.lift k
    exact ⟨_, _, _, _, hMatch.var, (·.casesOn (TShape.lift_eqv hk_none).2 hpath'),
      .cons ((hpath none).mono (TShape.lift_eqv hk_none).1) forall2, congrArg (·.app X) foldr_eq⟩
  | @app _ _ _ _ _ M_a f2 _ _ _ ihf iha =>
    have ⟨_, _, hTy, _⟩ := hTy; have .app (A := B) hB hTy_f hTy_a := hTy
    obtain ⟨nf, ihf'⟩ := ihf hTy_f p_wf.1 (hpath <| .inl ·)
    obtain ⟨na, iha'⟩ := iha hTy_a p_wf.2 (hpath <| .inr ·)
    refine ⟨max nf (na + 1), fun k hk => ?_⟩
    rw [Nat.max_le] at hk; let k' + 1 := k; simp at hk
    obtain ⟨_, rargs_f, mf', Fs, hMatch_f, hpath_f, forall2_f, foldr_eq_f⟩ := ihf' _ hk.1
    obtain ⟨c_a, rargs_a, ma', As, hMatch_a, hpath_a, forall2_a, foldr_eq_a⟩ := iha' _ hk.2
    have hTy_at_foldr := foldr_eq_a ▸ hTy_a
    have h_ctor_head := by simpa using hMatch_a.head_wf_eq (k := 0) p_wf.2
    obtain ⟨ci, h_env, h_uvars, I, Ts, args, _, rel, hTs, hI, hrel, heq, hcit⟩ :
        ∃ ci, Params.env.constants c_a = some ci ∧ (f2 (.head _)).length = ci.uvars ∧
          ∃ I Ts args u rel,
          Ts.length = rargs_a.length ∧
          Params.classify I = some (.indTy args.length rel) ∧ (rel = true ↔ u ≠ .zero) ∧
          let e := List.foldr .forallE
            (List.foldr (fun A acc => acc.app A) (.const I (f2 (.head _))) args) Ts
          SoundEq Γ ((SExpr.mk ci.type).instL (f2 (.head _))) e ∧
            StrongSound Γ e (.sort u) := by
      clear forall2_a hTy_f hTy_a foldr_eq_a hB
      induction As generalizing B with have ⟨_, _, hTy, _⟩ := hTy_at_foldr
      | nil =>
        have .const h1 h2 F h3 h4 := hTy
        have cl : CtorBundle.IsCtor c_a := ⟨_, h_ctor_head, rfl⟩
        unfold CtorBundle.rhs at h3
        have cl1 := Option.some.inj <| cl.cl.2.1.symm.trans h_ctor_head
        exact ⟨_, h1, h2, _, _, _, _, _, (cl1 ▸ (F cl).hlen :), (F cl).hclI, (F cl).hrel,
          h3 cl, h4 cl⟩
      | cons A rest ih => have .app _ hMf _ := hTy; exact ih _ hMf
    have h_classify' := forall2_a.length_eq ▸ h_ctor_head
    refine ⟨_, _, _, _, hMatch_f.app hMatch_a, (·.casesOn hpath_f hpath_a),
      .cons ?_ forall2_f, congrArg (·.app M_a) foldr_eq_f⟩
    refine foldr_eq_a ▸ .apps_realize W (WShape.HasType.T_iff.2 (.ctor' (r := rel)))
      ?_ hTy_at_foldr forall2_a (.ctor h_ctor_head .rfl)
    refine LE_Interp.apps_realize_inv (k := 0) W h_env heq
      (hTs.trans forall2_a.length_eq).symm hTy_at_foldr ?_
    let e := args.foldr (fun A acc => acc.app A) (SExpr.const I f2)
    -- The telescope's sort is `.zero` exactly when the body's is (`imax x y = 0 ↔ y = 0`).
    -- The old version propagated only the `≠ .zero` direction, which is all `hu0` supported;
    -- the `rel` parameterisation needs the equivalence, and it is available on both sides.
    have {Ts Γ ρ u} (W : Valuation.Fits Γ₀ Γ ρ)
        (h_intr : StrongSound Γ (List.foldr .forallE e Ts) (.sort u)) :
        ∃ Γ' u', (u' = .zero ↔ u = .zero) ∧ (Ts.length.repeatTR (·.push .bot) ρ).Fits Γ₀ Γ' ∧
          StrongSound Γ' e (.sort u') := by
      induction Ts generalizing Γ ρ u with | nil => exact ⟨_, _, .rfl, W, h_intr⟩ | cons T Ts ih
      have ⟨_, _, h_intr, h_imax_defeq⟩ := h_intr
      have .forallE (u := u₁) (v := v) h1 h2 := h_intr
      have key : v = .zero ↔ u = .zero := by
        constructor
        · intro h_zero
          have h_LE_zero : LE_Interp ρ (.sort false) (.sort (u₁.imax v)) :=
            .sort (by simp [TShape.LE.rfl, SLevel.imax_eq_zero, h_zero])
          have := WShape.sort_le.1 <| .of_T ((h_imax_defeq W).1 h_LE_zero).le_sort
          injection congrArg (·.1) this with eq; simpa using eq
        · intro h_zero
          have h_LE_zero : LE_Interp ρ (.sort false) (.sort u) :=
            .sort (by simp [TShape.LE.rfl, h_zero])
          have := WShape.sort_le.1 <| .of_T ((h_imax_defeq W).2 h_LE_zero).le_sort
          injection congrArg (·.1) this with eq
          simpa [SLevel.imax_eq_zero] using eq
      obtain ⟨Γ'', u'', hiff, W', h'⟩ :=
        ih (W.cons (InterpTyped.hsort (h1.sound W)) .bot .bot_bot) h2
      exact ⟨Γ'', u'', hiff.trans key, W', h'⟩
    obtain ⟨Γ', u_body, hu_iff, W, h_body_typed⟩ := this W hcit
    have hrel' : rel = true ↔ u_body ≠ .zero := hrel.trans (not_congr hu_iff).symm
    have hdec : decide (u_body ≠ .zero) = rel :=
      Bool.eq_iff_iff.2 ⟨fun h => hrel'.2 (of_decide_eq_true h),
        fun h => decide_eq_true (hrel'.1 h)⟩
    rw [← Nat.repeat_eq_repeatTR] at W; simp [← forall2_a.length_eq, ← hTs]
    refine .apps_realize (rargs := .replicate args.length (.bot (n := k'+1)))
      W (WShape.HasType.T_iff.2 (.indTy (r := rel))) ?_ h_body_typed ?_ ?_
    · exact .sort (by rw [hdec]; exact TShape.sort_eqv.1)
    · clear hI h_body_typed hcit this heq hrel hrel' hdec
      induction args with | nil => exact .nil | cons _ _ ih => exact .cons .bot ih
    · simpa only [List.map_replicate, WShape.lift_bot] using
        Const.indTy (rargs := .replicate args.length .bot) (List.length_replicate ▸ hI) .rfl
          |>.lift k'.le_succ .mono

variable [ParamsExtra] in
theorem LE_Interp.strongSoundS (H : IsDefEqStrong Γ M N A) : StrongSoundEq Γ M N A := by
  induction H with
  | @bvar _ i A _ h h2 ih =>
    refine .rfl ⟨.bvar h, fun _ _ W _ h => ?_, .bvar h, .rfl⟩; clear h2 ih
    generalize eq : SExpr.bvar i = M at h
    induction h with cases eq | bot => exact .mk .rfl .bot .bot .bot_bot | bvar a1
    induction W generalizing i A with | cons _ h1 h2 h3 ih => ?_ | nil =>
      exact TShape.le_bot'.1 a1 ▸ .mk .rfl .bot .bot .bot_bot
    cases h with simp [Valuation.push] at a1
    | zero => exact ⟨_, _, a1, .bvar .rfl, h2.weak, h3⟩
    | succ h => have ⟨_, _, le, h1, h2, h3⟩ := ih h a1; exact ⟨_, _, le, h1.weak, h2.weak, h3⟩
  | symm _ ih => exact ih.symm
  | trans H _ _ _ ih1 ih2 => exact ih1.trans ih2
  | trans' _ _ ih1 ih2 =>
    have ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ih1; have ⟨b1, b2, _, b4, b5, b6, b7⟩ := ih2
    have := ih2.left.uniq ih1.right
    refine ⟨.trans' a1 b1, a2.trans b2, a3, ?_, b5.defeq_r this, b6, b7.trans this⟩
    exact ((a1.symm.trans' a1).trans' b1).symm.trans' b1
  | @sort _ l =>
    refine .rfl ⟨.sort, fun _ _ W _ h => ?_, .sort, .rfl⟩
    generalize eq : SExpr.sort l = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot .bot_bot
    | sort h1 => exact .mk h1 (.sort .rfl) (.sort .rfl) (by simpa using .sort)
  | @const c _ _ ls _ a1 a2 a3 F a4 ih1 ih2 =>
    refine .rfl ⟨.const a1 a2, fun _ _ W _ h => ?_,
      .const a1 a2 F (fun h => (ih2 h).sound) (fun h => (ih2 h).right), .rfl⟩
    generalize eq : SExpr.const c ls = M at h
    induction h with cases eq | const b1 b2 b3 b4 b5 b6 b7 => ?_ | bot =>
      exact .mk .rfl .bot .bot .bot_bot
    cases a1.symm.trans b1; exact .mk b3 (.const b1 b2 .rfl b4 b5 b6 b7) b5 b4
  | appDF _ _ _ _ ihA ih1 ih2 ih3 =>
    refine .mk' (.appDF ih1.defeq ih2.defeq)
      (.app ihA.left.sound ih1.left ih2.left) .rfl
      (.app ihA.left.sound ih1.right ih2.right) ih3.sound.symm fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_app (ih1.left.sound W) (InterpTyped.hsort (ih3.left.sound W))⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | app h1 h2 h3
    · exact .app ((ih1.sound W).1 h1) ((ih2.sound W).1 h2) h3
    · exact .app ((ih1.sound W).2 h1) ((ih2.sound W).2 h2) h3
  | lamDF _ _ _ _ ih1 _ ih2 ih3 =>
    refine .mk' (.lamDF ih1.defeq ih2.defeq)
      (.lam ih1.left.sound ih2.left) .rfl
      (.lam ih1.right.sound ih3.right)
      (.symm <| .forallE ih1.left.sound ih1.sound .rfl) fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_lam (InterpTyped.hsort (ih1.left.sound W)) fun h1 h2 =>
      (ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2))⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | lam h1 h2 h3 h4
    · refine .lam ((ih1.sound W).1 h1) h2 (fun _ h => ?_) h4
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h.T)).1 (h3 _ h)
    · refine .lam ((ih1.sound W).2 h1) h2 (fun _ h => ?_) h4
      refine (ih2.sound (W.cons ?_ ((ih1.sound W).2 h1) h.T)).2 (h3 _ h)
      exact InterpTyped.hsort (ih1.left.sound W)
  | forallEDF _ _ _ ih1 ih2 ih3 =>
    refine .mk' (.forallEDF ih1.defeq ih2.defeq)
      (.forallE ih1.left ih2.left) .rfl (.forallE ih1.right ih3.right) .rfl fun _ _ W m => ?_
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_forallE (InterpTyped.hsort' (ih1.left.sound W)) fun h1 h2 =>
      (ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2))⟩ <;>
      try cases h with | bot => cases hm TShape.bot_le' | forallE h1 h2 h3 h4 h5
    · refine .forallE ((ih1.sound W).1 h1) ((ih1.sound W).1 h2) h3 (fun _ h => ?_) h5
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h2 h.T)).1 (h4 _ h)
    · refine .forallE ((ih1.sound W).2 h1) ((ih1.sound W).2 h2) h3 (fun _ h => ?_) h5
      refine (ih2.sound (W.cons ?_ ((ih1.sound W).2 h2) h.T)).2 (h4 _ h)
      exact InterpTyped.hsort (ih1.left.sound W)
  | defeqDF h1 h2 ih1 ih2 =>
    have ⟨a1, a2, a3, a4⟩ := ih2.left
    have ⟨b1, b2, b3, b4⟩ := ih2.right
    have hd := h1.defeq.defeqDF h2.defeq
    refine ⟨hd, ih2.sound, ?_, ?_⟩
    · exact ⟨hd.hasType.1, a2.defeq_r ih1.sound, a3, a4.trans ih1.sound⟩
    · exact ⟨hd.hasType.2, ih2.right.sound.defeq_r ih1.sound, b3, b4.trans ih1.sound⟩
  | beta _ _ _ _ ih1 ih2 ih3 ih4 =>
    refine ⟨.beta ih1.defeq ih2.defeq, fun _ _ W m => ?_, ih3.left, ih4.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with | bot => cases hm TShape.bot_le' | @app _ n₁ _ _ _ _ a h1 h2 h3
      cases h1 with | bot => cases hm (h3.trans TShape.bot_eqv.1) | @lam _ n₂ _ _ f' _ _ h4 h5 h6 h7
      let k := max n₂ n₁; have hk := Nat.max_le.1 (Nat.le_refl k)
      have ⟨_, _, a1, a2, a3, a4⟩ := ih2.left.sound W h2
      obtain ⟨_, b1, b2⟩ := WShapeFun.app_eq (f'.lift k) (a.lift k)
      obtain ⟨a', y', b2', rfl, yb_eq⟩ := (WShapeFun.mem_lift hk.1).1 b2
      obtain ⟨bx', bxle, bx_ht, bapp⟩ := WShape.HasDom.iff.1 h5 a'
      refine LE_Interp.inst.2 ⟨_, ?_, (h2.lift hk.2).mono b1.T⟩
      refine .mono_l (Valuation.LE.push.2 ⟨.rfl, bxle.T.trans (TShape.lift_eqv hk.1).2⟩) ?_
      refine (h6 bx' bx_ht).mono <| h3.trans <| .trans ?_ bapp.T
      rw [TShape.LE.def hk.2 hk.1, WShape.lift_app hk.2]
      have h7' := (TShape.LE.def (Nat.succ_le_succ hk.2) (Nat.succ_le_succ hk.1)).1 h7
      refine (WShape.app_mono_l h7' _).trans ?_
      rw [WShape.lift_lam' hk.1, WShape.lam'_app, yb_eq]
      exact WShape.lift_mono hk.1 (WShapeFun.app_of_mem b2').2
    · have ⟨_, h1, h2⟩ := LE_Interp.inst.1 h
      have ⟨e, a, a1, a2, a3, a4⟩ := ih2.left.sound W h2
      let k := max m.1 (max e.1 a.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
      have := (WShape.HasDom.single (y := m.2.lift k)).2 <| .inl <|
        (TShape.HasType.def hk.2.1 hk.2.2).1 a4
      refine .mono ?_ <| .app' (.lam' (a3.lift hk.2.2) this fun _ hx => ?_) (a2.lift hk.2.1)
      · rw [WShape.lam'_app, WShapeFun.single_app, if_pos .rfl]; exact (TShape.lift_eqv hk.1).2
      · simp [WShapeFun.single_app]; split <;> [rename_i h; exact .bot]
        refine (h1.lift hk.1).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.trans ?_⟩
        exact (TShape.LE.lift_l hk.2.1).2 h
  | @eta _ F _ _ _ _ ih1 ih2 =>
    refine ⟨.eta ih1.defeq, fun _ ρ W m => ?_, ih2.left, ih1.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have ⟨e, t, h1, h2, h3, h4⟩ := ih2.left.sound W h
      have ht : ¬t ≤ .bot := fun h => hm (h1.trans (h4.bot_r' h))
      cases h2 with
      | bot => cases hm (h1.trans TShape.bot_le')
      | @lam _ n _ _ f' _ _ h2a h2d h2f h2le
      cases h3 with | bot => cases ht TShape.bot_le' | forallE b1 b2 b3 b4 b5
      cases b5.le_forall with | bot b5 => cases ht b5 | forallE b5 b6
      obtain rfl | ⟨n₂, g, rfl, c1⟩ := h4.ty_forallE_inv; · cases hm (h1.trans TShape.bot_le')
      have key {x y} (hmem : (x, y) ∈ f') :
          LE_Interp ρ (WShape.T (n := n+1) (.lam' (WShapeFun.single x y))) F := by
        by_cases hy : y ≤ .bot
        · refine .mono (WShape.LE.T (?_ : _ ≤ .bot)) .bot
          rw [← WShape.lam'_bot, WShape.lam'_le_lam', WShapeFun.single_le]
          exact ⟨_, _, by simp [WShapeFun.mem_bot], WShape.bot_le, hy⟩
        rw [WShape.le_bot] at hy
        obtain ⟨x', x'le, x'ht, x'app⟩ := WShape.HasDom.iff.1 h2d x
        have := (h2f x' x'ht)
          |>.mono_l (Valuation.LE.push.2 ⟨.rfl, x'le.T⟩)
          |>.mono (WShape.LE.T <| (WShapeFun.app_of_mem hmem).2.trans x'app)
        cases this with | bot => cases hy rfl | @app _ n' f _ _ _ a' c1 c2 c3
        cases f using WShape.casesOn' with
        | lam g => ?_
        | _ => cases hy (TShape.le_bot.1 (c3.trans TShape.bot_le'))
        obtain ⟨x'', hle, mem⟩ := WShapeFun.app_eq g a'
        have le₁ := Nat.le_max_left n' n; have le₂ := Nat.le_max_right n' n
        refine (LE_Interp.weak_iff.1 c1).mono ?_
        refine (TShape.LE.def (Nat.succ_le_succ le₂) (Nat.succ_le_succ le₁)).2 ?_
        rw [WShape.lift_lam' le₂, WShapeFun.lift_single le₂, WShape.lam_eq_lam',
          WShape.lift_lam' le₁, WShape.lam'_le_lam', WShapeFun.single_le]
        exact ⟨_, _, (WShapeFun.mem_lift le₁).2 ⟨_, _, mem, rfl, rfl⟩,
          hle.T.trans (LE_Interp.bvar_iff.1 c2), (TShape.LE.def le₂ le₁).1 c3⟩
      have main (l : List (WShape n × WShape n)) (H : ∀ p, p ∈ l → p ∈ f') :
          ∃ g, (∀ z : WShapeFun n, g ≤ z ↔ ∀ x ∈ l, .single x.1 x.2 ≤ z) ∧
            LE_Interp ρ (WShape.T (.lam' g)) F := by
        induction l with | nil => exact ⟨.bot, by simp, WShape.lam'_bot ▸ .bot⟩ | cons p l ih
        obtain ⟨x, y⟩ := p; simp only [List.mem_cons, forall_eq_or_imp] at H
        have ⟨g, a1, a2⟩ := ih H.2
        have hc := (key H.1).compat a2
        have hJ := WShapeFun.Join.mk <| WShape.Compat.lam'.1 <| WShape.Compat.T_iff.2 hc
        refine ⟨_, fun z => (hJ _).trans <| .trans ?_ List.forall_mem_cons.symm, ?_⟩
        · exact and_congr_right' (a1 _)
        · exact (key H.1).join (WShape.Join.lam'.2 hJ).T a2
      have ⟨g, a1, a2⟩ := main f'.elems fun _ => WShapeFun.mem_elems.1
      refine a2.mono (h2le.trans (WShape.lam'_le_lam'.2 ?_).T) |>.mono h1
      refine WShapeFun.LE.def'.2 fun x' y' hmem => WShapeFun.single_le.1 ?_
      exact (a1 _).1 .rfl _ (WShapeFun.mem_elems.2 hmem)
    · have ⟨m', f, a1, a2, a3, a4⟩ := ih1.left.sound W h
      have hm' : ¬m' ≤ .bot := fun h => hm (a1.trans h)
      have hf : ¬f ≤ .bot := fun h => hm' (a4.bot_r' h)
      cases a3 with | bot => cases hf TShape.bot_le' | forallE b1 b2 b3 b4 b5
      cases b5.le_forall with | bot b5 => cases hf b5 | @forallE m _ _ _ _ b5 b6
      obtain rfl | ⟨n₂, g, rfl, c1⟩ := a4.ty_forallE_inv; · cases hm' TShape.bot_le'
      have le_k := Nat.le_max_left n₂ m; have le_m := Nat.le_max_right n₂ m
      refine .mono (WShape.lift_lam' le_k ▸ a1.trans (TShape.lift_eqv (Nat.succ_le_succ le_k)).2) <|
        .lam' ((b1.mono b5).lift (Nat.le_max_right ..)) c1.2.1 fun _ _ => ?_
      simpa only [WShape.lift_lam' le_k, WShape.lam'_app] using
        (a2.lift (Nat.succ_le_succ le_k)).weak.app' .bvar0
  | @proofIrrel _ p h h' _ _ _ ih1 ih2 ih3 =>
    refine ⟨.proofIrrel ih1.defeq ih2.defeq ih3.defeq, fun _ ρ W m => ?_, ih2.left, ih3.left⟩
    suffices ∀ {h h'}, InterpTyped ρ m h p → LE_Interp ρ m h → LE_Interp ρ m h' from
      ⟨fun h => this (ih2.left.sound W h) h, fun h => this (ih3.left.sound W h) h⟩
    refine fun ⟨_, _, a1, a2, a3, a4⟩ h1 => .mono (?_ : m ≤ .bot) .bot
    have ⟨_, _, b1, b2, b3, b4⟩ := ih1.left.sound W a3
    have b4' := TShape.HasType.mono_r (by simpa using b3.le_sort) .sort b4
    exact a1.trans (b4'.proofIrrel (b4'.mono_r b1 a4))
  | extra h1 h2 hTy_lhs hTy_rhs ih1 ih2 =>
    refine ⟨.extra h1 h2, fun Γ₀ ρ W m => ?_, ih1.left, ih2.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    obtain ⟨Δ, L, R, p, r, m1, m2, dfs, hL, hR, a1, a2, a3, a4, a5⟩ :=
      ParamsExtra.extra_pat Γ₀ h1 h2
    rw [hL, hR]
    -- **OPEN, and honest.**  `ParamsExtra.extra_pat` is now λ-peeled -- its unpeeled form is
    -- UNSATISFIABLE, see `SExpr.unpeeled_extra_pat_unsatisfiable` and `SExpr.iota_lhs_lam` --
    -- so both sides are `mkLams Δ _` and the matched redex is the BODY `L`.  The
    -- argument below is the one for a bare redex.  Running it under `Δ` needs
    --   (a) a congruence "`LE_Interp` respects the body of a `.lam`" (a short `cases` on the
    --       `lam`/`bot` rules -- the binder `A` is shared by both sides), and
    --   (b) the two IHs and `W` transported under the telescope, which needs `StrongSound`
    --       inversion through `lam`.
    -- BEFORE THE PEEL THIS CASE WAS PROVABLE ONLY BECAUSE `ParamsExtra` WAS UNSATISFIABLE,
    -- and `strongSoundS` carries `[ParamsExtra]`, so it -- and everything downstream of it --
    -- was vacuous.  The two errors here are the price of making it honest.
    refine a5 ▸ ⟨fun hLE => ?_, fun hLE => ?_⟩
    · obtain ⟨_, built⟩ := Matches.of_matchesS a2 (Params.pat_wf a1) hLE
      obtain ⟨_, rargs, m_path, m_head, hMatch, hpath, hle, hConst⟩ := built _ (Nat.le_refl _)
      cases hConst with
      | bot => cases hm (hle.trans TShape.bot_eqv.1)
      | lam hRec hle_lam =>
        refine hm ((hle.trans hle_lam).trans ?_) |>.elim
        rw [WShape.lam']; split <;> [rename_i hf; exact TShape.bot_eqv.1]
        obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
        refine (hn (WShape.LE.T_iff.1 (.trans ?_ TShape.bot_eqv.2))).elim
        exact (hRec s t hxy).compat_mismatch (by simp) <| .inr <| .inr ⟨_, _, _, a1, hMatch⟩
      | ctor h | indTy h =>
        obtain ⟨_, h_symb⟩ := hMatch.head_wf (Params.pat_wf a1)
        cases h ▸ h_symb
      | pat hP hM hRHS'
      obtain ⟨_, hi⟩ := hM.matches_inter (.rfl fun _ _ => .rfl)
        (Params.pat_wf hP) hMatch (Params.pat_wf a1)
      obtain ⟨rfl, -, ⟨⟩⟩ := Params.pat_uniq a1 hP .refl hi
      exact .mono hle <| RHS.le_applyS hpath (fun _ _ => id) <|
        Matches.unique (Params.pat_wf a1) hM hMatch ▸ hRHS'
    · have ⟨_, _, a, hm_lvl, hm_le_typed, h_LE_m_typed_R, ha, h_m_typed_HT⟩ :=
        (ih2.left.sound W (a5.symm ▸ hLE)).out
      obtain ⟨m_path_T, hpath, hRHS⟩ := RHS.of_applyS (a5 ▸ h_LE_m_typed_R)
      obtain ⟨_, built⟩ := build_spine a2 W ih1.left (Params.pat_wf a1) hpath
      obtain ⟨c, rargs, m', rAs, hMatch, hbnd, h_per_arg, h_foldr_eq⟩ := built _ (Nat.le_refl _)
      exact .mono hm_le_typed <| h_foldr_eq ▸ apps_realize W h_m_typed_HT.T ha
        (h_foldr_eq ▸ ih1.left) h_per_arg (.pat a1 hMatch (hRHS.mono_l hbnd))

/-- Soundness from an already-established `StrongSoundEq`. Useful when the reflexive
instance `StrongSoundEq Γ M M A` is needed, which `StrongSoundEq.rfl` supplies from
`StrongSoundEq.left`/`.right` — `IsDefEqStrong` itself has no reflexivity lemma, because
its `trans` rule carries an extra `Γ ⊢ A : .sort u` premise that the `VExpr` analogue
does not. -/
theorem LE_Interp.soundSS (H : StrongSoundEq Γ M N A) (W : Valuation.Fits Γ₀ Γ ρ) {m} :
    (LE_Interp ρ m M ↔ LE_Interp ρ m N) ∧ (LE_Interp ρ m M → InterpTyped ρ m M A) :=
  ⟨H.sound W, H.left.sound W⟩

variable [ParamsExtra] in
/-- Soundness from a *decorated* derivation. This is the form used inside inductions on
`IsDefEqStrong`; it needs no context well-formedness hypothesis because the decorations
already carry the typing information. -/
theorem LE_Interp.soundS (H : IsDefEqStrong Γ M N A) (W : Valuation.Fits Γ₀ Γ ρ) {m} :
    (LE_Interp ρ m M ↔ LE_Interp ρ m N) ∧ (LE_Interp ρ m M → InterpTyped ρ m M A) :=
  ⟨(strongSoundS H).sound W, (strongSoundS H).left.sound W⟩

variable [ParamsExtra] in
theorem LE_Interp.strongSound (hΓ : Ctx.WF Γ) (H : Γ ⊢ M ≡ N : A) : StrongSoundEq Γ M N A :=
  strongSoundS (H.strong hΓ)

variable [ParamsExtra] in
theorem LE_Interp.sound (hΓ : Ctx.WF Γ) (H : Γ ⊢ M ≡ N : A) (W : Valuation.Fits Γ₀ Γ ρ) {m} :
    (LE_Interp ρ m M ↔ LE_Interp ρ m N) ∧ (LE_Interp ρ m M → InterpTyped ρ m M A) :=
  soundS (H.strong hΓ) W

structure LogRelBase (Γ : List SExpr) (n : Nat) where
  /-- Term validity: `M ≡ N : A` at element-shape `m` and type-shape `a`. -/
  DefEq (M N A : SExpr) (m a : WShape n) : Prop
  /-- Type validity: `A ≡ B` are valid types at type-shape `a`. -/
  TyDefEq (A B : SExpr) (a : WShape n) : Prop

structure LogRel (Γ : List SExpr) (n : Nat) extends LogRelBase Γ n where
  sort_iff : DefEq M N A (.sort r) (.sort r') ↔ ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  sort_iff_ty : TyDefEq M N (.sort r) ↔ ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  bot : a.IsType → DefEq M N A .bot a
  toType : DefEq M N A m (.sort r) → TyDefEq M N m
  left : DefEq M N A m a → DefEq M M A m a
  left_ty : TyDefEq M N m → TyDefEq M M m
  symm : DefEq M N A m a → DefEq N M A m a
  symm_ty : TyDefEq M N m → TyDefEq N M m
  trans : DefEq M₁ M₂ A m a → DefEq M₂ M₃ A m a → DefEq M₁ M₃ A m a
  trans' : DefEq A₁ A₂ (.sort u) a s → DefEq A₂ A₃ (.sort v) a (.sort r) → DefEq A₁ A₃ (.sort u) a s
  trans_ty : TyDefEq M₁ M₂ m → TyDefEq M₂ M₃ m → TyDefEq M₁ M₃ m
  conv : TyDefEq A B a → DefEq M N A m a → DefEq M N B m a
  mono_r_2 : a ≤ a' → m.HasType a → a'.IsType → DefEq M N A m a' → DefEq M N A m a
  mono_r_2_ty : a ≤ a' → a.IsType → a'.IsType → TyDefEq A B a' → TyDefEq A B a
  mono_r_1 : a ≤ a' → m.HasType a → m.HasType a' → TyDefEq A A a' → DefEq M N A m a → DefEq M N A m a'
  mono_l : m ≤ m' → m.HasType a → m'.HasType a → DefEq M N A m' a → DefEq M N A m a
  join_ty : m₁.Compat m₂ → m₁.IsType → m₂.IsType →
    TyDefEq A B m₁ → TyDefEq A B m₂ → TyDefEq A B (m₁.join m₂)
  whr : Γ ⊢ M ⤳* M' → Γ ⊢ N ⤳* N' → (DefEq M N A m a ↔ DefEq M' N' A m a)
  whr_ty : Γ ⊢ A ⤳* A' → Γ ⊢ B ⤳* B' → (TyDefEq A B m ↔ TyDefEq A' B' m)

theorem LogRelBase.TyDefEq.sort {R : LogRel Γ n} : R.TyDefEq (.sort u) (.sort u) (.sort r) :=
  R.toType (A := default) (r := default) (R.sort_iff.2 ⟨_, .rfl, .rfl⟩)

/-! #### Concrete definitions at level 0 -/

def LR0.TyDefEq (Γ : List SExpr) (M N : SExpr) : WShape 0 → Prop
  | ⟨.bot, _⟩ => True
  | ⟨.sort _, _⟩ => ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u

def LR0.DefEq (Γ : List SExpr) (M N : SExpr) (m a : WShape 0) : Prop :=
  match a.1 with
  | .bot => True
  | .sort _ => LR0.TyDefEq Γ M N m

def LR0 : LogRel Γ 0 where
  DefEq M N _ := LR0.DefEq Γ M N
  TyDefEq := LR0.TyDefEq Γ
  sort_iff := by simp [LR0.DefEq, LR0.TyDefEq, WShape.sort]
  sort_iff_ty := by simp [LR0.TyDefEq, WShape.sort]
  bot {_ _ _ _} _ := by simp only [LR0.DefEq, LR0.TyDefEq, WShape.bot]; split <;> trivial
  toType := id
  left {M N A m a} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  left_ty {M N m} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  symm {M N A m a} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  symm_ty {M N m} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, h1, h2⟩ ⟨u', h2', h3⟩
    cases h2.determ .sort h2' .sort; exact ⟨u, h1, h3⟩
  trans' {A₁ A₂ u a s A₃ v r} := by
    dsimp [LR0.DefEq]; split <;> [(intros; trivial); skip]
    dsimp [LR0.TyDefEq]; split <;> [(intros; trivial); skip]
    intro ⟨u, h1, h2⟩ ⟨u', h2', h3⟩
    cases h2.determ .sort h2' .sort; exact ⟨u, h1, h3⟩
  trans_ty {M₁ M₂ m M₃} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, h1, h2⟩ ⟨u', h2', h3⟩
    cases h2.determ .sort h2' .sort; exact ⟨u, h1, h3⟩
  conv _ := id
  mono_r_2 {a a' _ _ _ _} le _ _ := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;> simp [LR0.DefEq]; cases le
  mono_r_2_ty {a a' _ _} le _ _ := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;> simp [LR0.TyDefEq]; cases le
  mono_r_1 {a a' _ _ _ b} le h1 _ h2 := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;>
      (try exact id) <;> [cases h1.bot_r; cases le]; exact id
  mono_l {m m' M N A a} le _ _ := by
    simp only [LR0.DefEq]; split <;> [trivial; skip]
    obtain ⟨⟨⟩, _⟩ := m <;> obtain ⟨⟨⟩, _⟩ := m' <;>
      (try exact id) <;> [exact fun _ => trivial; cases le]
  join_ty {A B m₁ m₂} hC hm₁ hm₂ := by
    obtain ⟨⟨⟩, _⟩ := m₁ <;> obtain ⟨⟨⟩, _⟩ := m₂ <;>
      simp [LR0.TyDefEq, WShape.join, Shape.join, dif_pos hC]
    simp [WShape.Compat, Shape.Compat] at hC; subst hC; simp
    intro u h1 h2 _ h3 h4; exact ⟨u, h1, h2⟩
  whr {M M' N N' A m a} hM hN := by
    dsimp [LR0.DefEq]; split <;> [exact .rfl; skip]
    dsimp [LR0.TyDefEq]; split <;> [exact .rfl; skip]
    constructor <;> intro ⟨u, r1, r2⟩
    · exact ⟨u, hM.determ_l r1 .sort, hN.determ_l r2 .sort⟩
    · exact ⟨u, .trans hM r1, .trans hN r2⟩
  whr_ty {A A' B B' m} hA hB := by
    dsimp [LR0.TyDefEq]; split <;> [exact .rfl; skip]
    constructor <;> intro ⟨u, r1, r2⟩
    · exact ⟨u, hA.determ_l r1 .sort, hB.determ_l r2 .sort⟩
    · exact ⟨u, .trans hA r1, .trans hB r2⟩

/-! #### Concrete definitions at level n+1 -/

/-- Pi edge validity (merged `PiEdgeDefEq` / `PiEdgeEq2`).
For each argument `a ≡ b : A₁`, the substituted codomains are valid types.
For each argument `a : A₁`, the codomains `A₂[a]` and `B₂[a]` are equal types. -/
def LRS.PiDefEq (IH : LogRel Γ n)
    (B F₁ F₂ : SExpr) (b : WShape n) (f : WShapeFun n) : Prop :=
  (∀ {{a b' p}}, p.HasType b → Γ ⊢ a ≡ b' : B → IH.DefEq a b' B p b →
    IH.TyDefEq (F₁.inst a) (F₁.inst b') (f.app p) ∧
    IH.TyDefEq (F₂.inst a) (F₂.inst b') (f.app p)) ∧
  ∀ {{a p}}, p.HasType b → Γ ⊢ a : B → IH.DefEq a a B p b →
    IH.TyDefEq (F₁.inst a) (F₂.inst a) (f.app p)

theorem LRS.PiDefEq.left {IH : LogRel Γ n} :
    LRS.PiDefEq IH B F₁ F₂ b f → LRS.PiDefEq IH B F₁ F₁ b f := fun ⟨h1, _⟩ =>
  ⟨fun _ _ _ hp ha a1 => ⟨(h1 hp ha a1).1, (h1 hp ha a1).1⟩, fun _ _ hp ha a1 => (h1 hp ha a1).1⟩

def LRS.ValTyPi2 (IH : LogRel Γ n) (M₁ M₂ : SExpr) (b : WShape n) (f : WShapeFun n) : Prop :=
  ∃ B₁ F₁ B₂ F₂ u v,
    Γ ⊢ M₁ ⤳* .forallE B₁ F₁ ∧ Γ ⊢ M₂ ⤳* .forallE B₂ F₂ ∧
    Γ ⊢ B₁ ≡ B₂ : .sort u ∧ B₁::Γ ⊢ F₁ ≡ F₂ : .sort v ∧ IH.TyDefEq B₁ B₂ b ∧
    LRS.PiDefEq IH B₁ F₁ F₂ b f

def LRS.LamDefEq (IH : LogRel Γ n)
    (M N A₁ A₂ : SExpr) (m : WShapeFun n) (a₁ : WShape n) (a₂ : WShapeFun n) : Prop :=
  (∀ {{a b p}}, WShape.HasType p a₁ → Γ ⊢ a ≡ b : A₁ → IH.DefEq a b A₁ p a₁ →
    IH.DefEq (M.app a) (M.app b) (A₂.inst a) (m.app p) (a₂.app p) ∧
    IH.DefEq (N.app a) (N.app b) (A₂.inst a) (m.app p) (a₂.app p)) ∧
  (∀ {{a p}}, WShape.HasType p a₁ → Γ ⊢ a : A₁ → IH.DefEq a a A₁ p a₁ →
    IH.DefEq (M.app a) (N.app a) (A₂.inst a) (m.app p) (a₂.app p))

/-- Monotonicity of `LamDefEq` in the type-shape: increase. -/
theorem LRS.LamDefEq.mono_r_1 {IH : LogRel Γ n}
    (le₁ : a₁ ≤ a₁') (le₂ : a₂ ≤ a₂') (hm : WShape.HasTypeLam m a₁ a₂)
    (hm' : WShape.HasTypeLam m a₁' a₂') (piEV : LRS.PiDefEq IH A₁ A₂ A₂ a₁' a₂') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' := by
  have hm_d := WShape.HasDom.iff.1 hm.2.1
  have hm_f := WShape.HasTypeLam.iff.1 hm |>.2.2
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ x hx ha a1 => ?_, fun _ x hx ha a1 => ?_⟩
  all_goals
    have ⟨x', le', hax, h1⟩ := hm_d x
    have ⟨_, hx_is⟩ := WShape.HasType.isType hx
    have hax' := hx_is.mono_r le₁ hax
    have a1_x := IH.mono_l le' hax' hx a1
    have a1_down := IH.mono_r_2 le₁ hax hx.isType a1_x
    have hg_x := hm_f x' hax
    have hg_p := hg_x.mono_l (WShapeFun.app_mono_r le') h1
    have le_cod := (WShapeFun.app_mono_r le').trans (WShapeFun.app_mono_l le₂ _)
    have ⟨_, hm'_pi⟩ := hm'.1
    have ht_cod := (WShape.HasTypePi.iff.1 hm'_pi).2 x hx
    have hm_target := ht_cod.mono_r le_cod hg_p
  · have ⟨p1, p2⟩ := pav hax ha a1_down
    have tyA₂ := (piEV.1 hx ha.hasType.1 (IH.left a1)).1
    exact ⟨IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p1),
           IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p2)⟩
  · have q := pae hax ha a1_down
    have tyA₂ := piEV.2 hx ha a1
    exact IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x q)

/-- Type validity at element-shape `m` (merged `TyDefEq` / `EqTyDefEq`).
Non-trivial at `.forallE` (Pi injectivity) and `.sort` (sort injectivity). -/
def LRS.TyDefEq (IH : LogRel Γ n) (M N : SExpr) : WShape (n+1) → Prop
  | ⟨.bot, _⟩ | ⟨.lam _, _⟩ | ⟨.ctor _ _, _⟩ | ⟨.indTy _, _⟩ => True
  | ⟨.sort _, _⟩ => ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  | ⟨.forallE b f, wf⟩ => LRS.ValTyPi2 IH M N ⟨b, wf.1⟩ ⟨f, wf.2⟩

@[simp] theorem LRS.TyDefEq.bot : LRS.TyDefEq IH M N .bot := trivial
@[simp] theorem LRS.TyDefEq.sort_iff :
    LRS.TyDefEq (Γ := Γ) IH M N (.sort r) ↔ ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u := .rfl
@[simp] theorem LRS.TyDefEq.lam' : LRS.TyDefEq IH M N (.lam' f) := by
  unfold WShape.lam'; split <;> trivial
@[simp] theorem LRS.TyDefEq.ctor' : LRS.TyDefEq IH M N (.ctor' c l) := by
  unfold WShape.ctor'; split <;> trivial
@[simp] theorem LRS.TyDefEq.forallE_iff :
    LRS.TyDefEq (Γ := Γ) IH M N (.forallE b f) ↔ LRS.ValTyPi2 (Γ := Γ) IH M N b f := .rfl

theorem LRS.TyDefEq.left {IH : LogRel Γ n} :
    LRS.TyDefEq IH M N m → LRS.TyDefEq IH M M m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  · intro ⟨B₁, F₁, _, _, u, v, rM, _, hB, hF, hValB, hE⟩
    exact ⟨B₁, F₁, B₁, F₁, u, v, rM, rM, hB.hasType.1, hF.hasType.1, IH.left_ty hValB, hE.left⟩

theorem LRS.TyDefEq.symm {IH : LogRel Γ n} :
    LRS.TyDefEq IH M N m → LRS.TyDefEq IH N M m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  · intro ⟨_, _, _, _, _, _, rM, rN, hB, hF, hValB, hE1, hE2⟩
    have hValB' := IH.symm_ty hValB
    refine ⟨_, _, _, _, _, _, rN, rM, hB.symm, hB.defeqDF_l hF.symm,
      hValB', fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
    · exact (hE1 hp (hB.symm.defeqDF ha) (IH.conv hValB' a1)).symm
    · exact IH.symm_ty (hE2 hp (hB.symm.defeqDF ha) (IH.conv hValB' a1))

theorem LRS.TyDefEq.trans {IH : LogRel Γ n} :
    LRS.TyDefEq IH M₁ M₂ m → LRS.TyDefEq IH M₂ M₃ m → LRS.TyDefEq IH M₁ M₃ m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM₁, hM₂⟩ ⟨u', hM₂', hM₃⟩
    cases hM₂.determ .sort hM₂' .sort; exact ⟨u, hM₁, hM₃⟩
  · intro ⟨B₁, F₁, B₂, F₂, u, v, rM₁, rM₂, hB₁₂, hF₁₂, hValB₁₂, hE1⟩
          ⟨_, _, B₃, F₃, u', v', rM₂', rM₃, hB₂₃, hF₂₃, hValB₂₃, hE2⟩
    cases rM₂.determ .forallE rM₂' .forallE
    have hF₂₃' := hB₁₂.symm.defeqDF_l hF₂₃
    refine ⟨_, _, _, _, _, _, rM₁, rM₃, hB₁₂.trans' hB₂₃, hF₁₂.trans' hF₂₃',
      IH.trans_ty hValB₁₂ hValB₂₃, fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
    · exact ⟨(hE1.1 hp ha a1).1, (hE2.1 hp (hB₁₂.defeqDF ha) (IH.conv hValB₁₂ a1)).2⟩
    · exact IH.trans_ty (hE1.2 hp ha a1) (hE2.2 hp (hB₁₂.defeqDF ha) (IH.conv hValB₁₂ a1))

theorem LRS.LamDefEq.left {IH : LogRel Γ n} :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH M M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).1, (hP.1 hp ha a1).1⟩
  · exact (hP.1 hp ha a1).1

theorem LRS.LamDefEq.symm {IH : LogRel Γ n} :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH N M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).2, (hP.1 hp ha a1).1⟩
  · exact IH.symm (hP.2 hp ha a1)

theorem LRS.LamDefEq.trans {IH : LogRel Γ n} :
    LRS.LamDefEq IH M₁ M₂ B F m m₁ m₂ →
    LRS.LamDefEq IH M₂ M₃ B F m m₁ m₂ → LRS.LamDefEq IH M₁ M₃ B F m m₁ m₂ := by
  refine fun ⟨hP1, hP2⟩ ⟨hP1', hP2'⟩ => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP1 hp ha a1).1, (hP1' hp ha a1).2⟩
  · exact IH.trans (hP2 hp ha a1) (hP2' hp ha a1)

theorem LRS.PiDefEq.mono_r_2 {IH : LogRel Γ n}
    (le₁ : b ≤ b') (le₂ : f ≤ f')
    (htpi : WShape.HasTypePi f b r) (htpi' : WShape.HasTypePi f' b' r')
    (hValA₁ : IH.TyDefEq A₁ A₁ b') :
    LRS.PiDefEq IH A₁ A₂ B₂ b' f' → LRS.PiDefEq IH A₁ A₂ B₂ b f
  | ⟨h1, h2⟩ => by
    have htpi_w := WShape.HasTypePi.iff.1 htpi
    have htpi'_w := WShape.HasTypePi.iff.1 htpi'
    refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
    all_goals
      have ⟨_, hb'_is⟩ := WShape.HasDom.isType htpi'.1
      have hp' := WShape.HasType.mono_r le₁ hb'_is hp
      have a2 := IH.mono_r_1 le₁ hp hp' hValA₁ a1
      have hm_tgt := (htpi_w.2 _ hp).toIsType; have hm_src := (htpi'_w.2 _ hp').toIsType
    · let ⟨t1, t2⟩ := h1 hp' ha a2
      exact ⟨IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src t1,
             IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src t2⟩
    · exact IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src (h2 hp' ha a2)

theorem LRS.LamDefEq.mono_r_2 {IH : LogRel Γ n}
    (le₁ : a₁ ≤ a₁') (le₂ : a₂ ≤ a₂') (hm : WShape.HasTypeLam m a₁ a₂)
    (hValA₁ : IH.TyDefEq A₁ A₁ a₁') (htpi' : WShape.HasTypePi a₂' a₁' r') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  have hm_w := WShape.HasTypeLam.iff.1 hm
  have htpi'_w := WShape.HasTypePi.iff.1 htpi'
  intro ⟨h1, h2⟩
  refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
  all_goals
    have ⟨_, ha₁'_is⟩ := WShape.HasDom.isType htpi'.1
    have hp' := WShape.HasType.mono_r le₁ ha₁'_is hp
    have a1' := IH.mono_r_1 le₁ hp hp' hValA₁ a1
    have hm_tgt := hm_w.2.2 _ hp
    have ht_src := (htpi'_w.2 _ hp').toIsType
  · have ⟨d1, d2⟩ := h1 hp' ha a1'
    exact ⟨IH.mono_r_2 (WShapeFun.app_mono_l le₂ x) hm_tgt ht_src d1,
           IH.mono_r_2 (WShapeFun.app_mono_l le₂ x) hm_tgt ht_src d2⟩
  · have q := h2 hp' ha a1'
    exact IH.mono_r_2 (WShapeFun.app_mono_l le₂ _) hm_tgt ht_src q

/-- Monotonicity of `LamDefEq` in the element-shape: decrease. -/
theorem LRS.LamDefEq.mono_l {IH : LogRel Γ n}
    (le : m ≤ m') (hm : WShape.HasTypeLam m a₁ a₂)
    (hm' : WShape.HasTypeLam m' a₁ a₂) :
    LRS.LamDefEq IH M N A₁ A₂ m' a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  have hm_w := WShape.HasTypeLam.iff.1 hm
  have hm'_w := WShape.HasTypeLam.iff.1 hm'
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  all_goals
    have hm_tgt := hm_w.2.2 _ hp
    have hm_src := hm'_w.2.2 _ hp
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src d1,
           IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src d2⟩
  · have q := pae hp ha a1
    exact IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src q

/-- Join of `PiDefEq`: given edge validity at `(b₁, f₁)` and `(b₂, f₂)`,
produce edge validity at `(b₁.join b₂, f₁.join f₂)`.
Follows the same representative-based strategy as old `LRS.join`. -/
theorem LRS.PiDefEq.join {IH : LogRel Γ n}
    (htB₁ : b₁.IsType) (htB₂ : b₂.IsType)
    (hC_b : b₁.Compat b₂)
    (ht₁ : WShape.HasTypePi f₁ b₁ r₁) (ht₂ : WShape.HasTypePi f₂ b₂ r₂)
    (hC_f : WShapeFun.Compat f₁ f₂)
    (hE₁ : LRS.PiDefEq IH B₁ F₁ F₂ b₁ f₁)
    (hE₂ : LRS.PiDefEq IH B₁ F₁ F₂ b₂ f₂) :
    LRS.PiDefEq IH B₁ F₁ F₂ (b₁.join b₂) (f₁.join f₂) := by
  have hJ_b := WShape.Join.mk hC_b
  have htB_join := htB₁.join hC_b htB₂
  have hJ_f := WShapeFun.Join.mk hC_f
  have ht₁_w := WShape.HasTypePi.iff.1 ht₁
  have ht₂_w := WShape.HasTypePi.iff.1 ht₂
  have hd₁ := WShape.HasDom.iff.1 ht₁.1
  have hd₂ := WShape.HasDom.iff.1 ht₂.1
  refine ⟨fun _ _ p hp ha a1 => ?_, fun _ p hp ha a1 => ?_⟩
  all_goals
    obtain ⟨d_x, d_le, d_ht, d_app⟩ := hd₁ p
    have c2 := IH.mono_r_2 hJ_b.le.1 d_ht htB_join
      (IH.mono_l d_le (WShape.HasType.mono_r hJ_b.le.1 htB_join d_ht) hp a1)
    obtain ⟨e_x, e_le, e_ht, e_app⟩ := hd₂ p
    have c3 := IH.mono_r_2 hJ_b.le.2 e_ht htB_join
      (IH.mono_l e_le (WShape.HasType.mono_r hJ_b.le.2 htB_join e_ht) hp a1)
    have ht_f1 : (f₁.app p).IsType :=
      have ⟨_, _, hm⟩ := f₁.app_eq p; (ht₁.2 _ _ hm).toIsType
    have ht_f2 : (f₂.app p).IsType :=
      have ⟨_, _, hm⟩ := f₂.app_eq p; (ht₂.2 _ _ hm).toIsType
    have hJ_fp := hJ_f.app_l p
    have ⟨hC_fp, _, hC_fJ⟩ := WShape.Join.iff.1 hJ_fp
    have ht_fJ := ht_f1.join' hJ_fp ht_f2
    have ht_fJ' := ht_f1.join hC_fp ht_f2
    have cvt_d {A B} (h : IH.TyDefEq A B (f₁.app d_x)) : IH.TyDefEq A B (f₁.app p) :=
      IH.mono_r_2_ty d_app ht_f1 (ht₁_w.2 d_x d_ht).toIsType h
    have cvt_e {A B} (h : IH.TyDefEq A B (f₂.app e_x)) : IH.TyDefEq A B (f₂.app p) :=
      IH.mono_r_2_ty e_app ht_f2 (ht₂_w.2 e_x e_ht).toIsType h
  · constructor
    · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (cvt_d (hE₁.1 d_ht ha c2).1) (cvt_e (hE₂.1 e_ht ha c3).1)
    · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (cvt_d (hE₁.1 d_ht ha c2).2) (cvt_e (hE₂.1 e_ht ha c3).2)
  · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
      (cvt_d (hE₁.2 d_ht ha c2)) (cvt_e (hE₂.2 e_ht ha c3))

/-- Head reduction on M, N preserves `LamDefEq`. Uses `IH.whr` (with `WHRed.app`)
to transport the inner `IH.DefEq` terms. HasType is preserved trivially (doesn't mention M, N). -/
theorem LRS.LamDefEq.whr {IH : LogRel Γ n}
    (hM : Γ ⊢ M ⤳* M') (hN : Γ ⊢ N ⤳* N') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ ↔ LRS.LamDefEq IH M' N' A₁ A₂ m a₁ a₂ := by
  constructor <;> intro ⟨pav, pae⟩ <;> refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (.app hM) (.app hM)).1 d1, (IH.whr (.app hN) (.app hN)).1 d2⟩
  · exact (IH.whr (.app hM) (.app hN)).1 (pae hp ha a1)
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (.app hM) (.app hM)).2 d1, (IH.whr (.app hN) (.app hN)).2 d2⟩
  · exact (IH.whr (.app hM) (.app hN)).2 (pae hp ha a1)

/-- Term validity at `(m, a)`. -/
def LRS.DefEq (IH : LogRel Γ n) (M N A : SExpr) (m a : WShape (n+1)) : Prop :=
  match ha : a.1 with
  | .bot => True
  | .sort _ => LRS.TyDefEq IH M N m
  | .forallE a₁ a₂ =>
    have wfa1 := (ha ▸ a.2).1; have wfa2 := (ha ▸ a.2).2
    match hm : m.1 with
    | .bot => True
    | .lam mg =>
      ∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ ∧
      Γ ⊢ A₁ : .sort u ∧ IH.TyDefEq A₁ A₁ ⟨a₁, wfa1⟩ ∧ A₁::Γ ⊢ A₂ : sort v ∧
      LRS.PiDefEq IH A₁ A₂ A₂ ⟨a₁, wfa1⟩ ⟨a₂, wfa2⟩ ∧
      LRS.LamDefEq IH M N A₁ A₂ ⟨mg, (hm ▸ m.2).1⟩ ⟨a₁, wfa1⟩ ⟨a₂, wfa2⟩
    | _ => False
  | .indTy _ => True
  | _ => False

@[simp] theorem LRS.DefEq.bot_a : LRS.DefEq IH M N A m .bot = True := rfl
@[simp] theorem LRS.DefEq.sort_a : LRS.DefEq IH M N A m (.sort r) = LRS.TyDefEq IH M N m := rfl
@[simp] theorem LRS.DefEq.bot_m : LRS.DefEq IH M N A .bot (.forallE a₁ a₂) = True := rfl
@[simp] theorem LRS.DefEq.lam_forallE (IH : LogRel Γ n) :
    LRS.DefEq IH M N A (.lam f hf) (.forallE a₁ a₂) ↔
    (∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ ∧
      Γ ⊢ A₁ : .sort u ∧ IH.TyDefEq A₁ A₁ a₁ ∧ A₁::Γ ⊢ A₂ : sort v ∧
      LRS.PiDefEq IH A₁ A₂ A₂ a₁ a₂ ∧
      LRS.LamDefEq IH M N A₁ A₂ f a₁ a₂) := by
  show (∃ A₁ A₂ u v, _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ LRS.LamDefEq IH _ _ _ _ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩) ↔ _
  simp only [Subtype.eta]
@[simp] theorem LRS.DefEq.sort_forallE :
    LRS.DefEq IH M N A (.sort r) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.forallE_forallE :
    LRS.DefEq IH M N A (.forallE b g) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.ctor_forallE :
    LRS.DefEq IH M N A (.ctor c l h) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.indTy_forallE :
    LRS.DefEq IH M N A (.indTy r) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.lam_a : LRS.DefEq IH M N A m (.lam f hf) ↔ False := .rfl
@[simp] theorem LRS.DefEq.ctor_a {c l h} :
    LRS.DefEq (n := n) IH M N A m (.ctor c l h) ↔ False := .rfl
@[simp] theorem LRS.TyDefEq.lam_m : LRS.TyDefEq IH M N (.lam f hf) ↔ True := .rfl
@[simp] theorem LRS.TyDefEq.ctor_m {c l h} :
    LRS.TyDefEq (n := n) IH M N (.ctor c l h) ↔ True := .rfl
@[simp] theorem LRS.TyDefEq.indTy_m : LRS.TyDefEq (n := n) IH M N (.indTy r) ↔ True := .rfl
@[simp] theorem LRS.DefEq.indTy_a : LRS.DefEq (n := n) IH M N A m (.indTy r) ↔ True := .rfl

def LRS (IH : LogRel Γ n) : LogRel Γ (n+1) where
  DefEq := LRS.DefEq IH
  TyDefEq := LRS.TyDefEq IH
  sort_iff := .rfl
  sort_iff_ty := .rfl
  bot ha := by have ⟨_, ha⟩ := ha; cases ha.unfold <;> trivial
  left_ty := .left
  left {M N A m a} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact .left
    · cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.left⟩
  symm_ty := .symm
  symm {M N A m a} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact .symm
    · cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.symm⟩
  trans_ty := .trans
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact .trans
    · split <;> try trivial
      intro ⟨B, F, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ ⟨_, _, _, _, rA', _, _, _, _, hP'⟩
      cases rA.determ .forallE rA' .forallE
      exact ⟨_, _, _, _, rA, hA1, hA2, hA₂, hE, hP.trans hP'⟩
  trans' {A₁ A₂ u a s A₃ v r} := by
    dsimp [LRS.DefEq]; split <;> try intros; trivial
    · exact .trans
    · split <;> try intros; trivial
      intro ⟨_, _, _, _, rA, _⟩; cases WHNF.sort.whRedS rA
  conv {A A' a M N m} := by
    dsimp [LRS.TyDefEq]; dsimp [LRS.DefEq]; split <;> (try · simp); dsimp
    intro ⟨B, F, B', F', u, v, rA, rA', hBB', hFF', hValB, hEdge⟩
    cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
    intro ⟨_, _, _, v', rA₁, hA1, hValA, hA₂, hEdge₁, hP⟩
    cases rA.determ .forallE rA₁ .forallE
    refine ⟨_, _, _, _, rA', hBB'.hasType.2, IH.left_ty (IH.symm_ty hValB),
      hBB'.defeqDF_l hFF'.hasType.2, ?_, ?_⟩
    · refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;>
        have ha' := hBB'.symm.defeqDF ha
      · exact and_self_iff.2 (hEdge.1 hp ha' (IH.conv (IH.symm_ty hValB) a1)).2
      · exact (hEdge.1 hp ha' (IH.conv (IH.symm_ty hValB) a1)).2
    refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;> (
      have a2 := IH.conv (IH.symm_ty hValB) a1
      have ha' := hBB'.symm.defeqDF ha
      have c := hEdge.2 hp ha'.hasType.1 (IH.left a2))
    · have ⟨v1, v2⟩ := hP.1 hp ha' a2; exact ⟨IH.conv c v1, IH.conv c v2⟩
    · exact IH.conv c (hP.2 hp ha' a2)
  toType := id
  mono_r_2 {a a' M N A m} le hm ht h := by
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort => cases WShape.sort_le.1 le; exact h
    | forallE a₁ a₂ =>
      obtain ⟨a₁', a₂', le1, le2, rfl⟩ := WShape.forallE_le.1 le
      cases m using WShape.casesOn' with
      | bot => simp [LRS.DefEq.bot_m]
      | lam f hf =>
        simp only [LRS.DefEq.lam_forallE] at h ⊢
        have ⟨_, hm_is⟩ := WShape.HasType.isType hm
        have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 hm_is
        have ⟨_, ht_is⟩ := ht
        have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ht_is
        obtain ⟨g, hg, hm'⟩ := WShape.HasType.forallE_inv hm
        have hgf : g = f := by
          have := congrArg (·.1) hg; simp only [WShape.lam, WShape.lam'] at this
          split at this
          · injection this with this; exact WShapeFun.ext this.symm
          · cases this
        subst hgf
        let ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hEdge, hP⟩ := h
        have ht := (WShape.HasTypePi.iff.1 hp).1.isType
        have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
        refine ⟨A₁, A₂, u, v, rA, hA1, IH.mono_r_2_ty le1 ht ht' hA2, hA₂, ?_⟩
        exact ⟨hEdge.mono_r_2 le1 le2 hp hp' hA2, hP.mono_r_2 le1 le2 hm' hA2 hp'⟩
      | sort => simp [LRS.DefEq.sort_forallE] at h
      | forallE => simp [LRS.DefEq.forallE_forallE] at h
      | ctor => simp [LRS.DefEq.ctor_forallE] at h
      | indTy => simp [LRS.DefEq.indTy_forallE] at h
    | lam f hf => exact absurd (WShape.HasType.isType hm) WShape.IsType.not_lam
    | ctor => exact absurd (WShape.HasType.isType hm) WShape.IsType.not_ctor
    | indTy => simp [LRS.DefEq.indTy_a] at h ⊢
  mono_r_2_ty {a a' A B} le ha ha' h := by
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort => simp [LRS.TyDefEq] at h ⊢; cases WShape.sort_le.1 le; exact h
    | forallE a₁ a₂ =>
      simp [LRS.TyDefEq] at h ⊢
      obtain ⟨a₁', a₂', le1, le2, rfl⟩ := WShape.forallE_le.1 le
      have ⟨_, ha_is⟩ := ha
      have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 ha_is
      have ⟨_, ha'_is⟩ := ha'
      have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ha'_is
      let ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB', hFF', hValB, hEdge⟩ := h
      have ht := (WShape.HasTypePi.iff.1 hp).1.isType
      have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
      refine ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB', hFF', IH.mono_r_2_ty le1 ht ht' hValB, ?_⟩
      exact hEdge.mono_r_2 le1 le2 hp hp' (IH.left_ty hValB)
    | lam f hf => simp [LRS.TyDefEq.lam_m]
    | ctor => simp [LRS.TyDefEq.ctor_m]
    | indTy => simp [LRS.TyDefEq.indTy_m]
  mono_r_1 {a a' A M N m} le ha ha' hA h := by
    cases a' using WShape.casesOn' with
    | bot => simp only [LRS.DefEq.bot_a]
    | sort r =>
      obtain rfl | rfl := WShape.le_sort.1 le
      · have := ha.bot_r; subst this; simp only [LRS.DefEq.sort_a, LRS.TyDefEq.bot]
      · exact h
    | forallE a₁' a₂' =>
      obtain rfl | ⟨a₁, a₂, rfl, le1, le2⟩ := WShape.le_forallE_iff.1 le
      · have := ha.bot_r; subst this; simp only [LRS.DefEq.bot_m]
      · cases m using WShape.casesOn' with
        | bot => simp only [LRS.DefEq.bot_m]
        | lam f hf =>
          simp only [LRS.DefEq.lam_forallE] at h ⊢
          obtain ⟨g, hg, hm_lam⟩ := WShape.HasType.forallE_inv ha
          have hgf' : (WShape.lam f hf).1 = (WShape.lam' g).1 := congrArg (·.1) hg
          simp only [WShape.lam, WShape.lam'] at hgf'; split at hgf'
          · injection hgf' with hgf'
            have := WShapeFun.ext hgf'.symm; subst this  -- now f = g
            obtain ⟨g', hg', hm'_lam⟩ := WShape.HasType.forallE_inv ha'
            have hgf2 : (WShape.lam g hf).1 = (WShape.lam' g').1 := congrArg (·.1) hg'
            simp only [WShape.lam, WShape.lam'] at hgf2; split at hgf2
            · injection hgf2 with hgf2; have := WShapeFun.ext hgf2.symm; subst this
              let ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge_src, hP⟩ := h
              let ⟨B₁, F₁, B₂, F₂, u', v', rA', rA'', hBB_tgt, hFF_tgt, hValB_tgt, hEdge_tgt⟩ := hA
              cases rA.determ .forallE rA' .forallE
              cases rA.determ .forallE rA'' .forallE
              refine ⟨_, _, _, _, rA, hBB_tgt.hasType.1, hValB_tgt, hA₂, hEdge_tgt, ?_⟩
              exact hP.mono_r_1 le1 le2 hm_lam hm'_lam hEdge_tgt
            · cases hgf2
          · cases hgf'
        | sort => exact (LRS.DefEq.sort_forallE.1 h).elim
        | forallE => exact (LRS.DefEq.forallE_forallE.1 h).elim
        | ctor => exact (LRS.DefEq.ctor_forallE.1 h).elim
        | indTy => exact (LRS.DefEq.indTy_forallE.1 h).elim
    | lam f hf => exact absurd (WShape.HasType.isType ha') WShape.IsType.not_lam
    | ctor => exact absurd (WShape.HasType.isType ha') WShape.IsType.not_ctor
    | indTy => simp [LRS.DefEq.indTy_a]
  mono_l {m m' M N A a} le hm hm' h := by
    cases a using WShape.casesOn' with
    | bot => simp only [LRS.DefEq.bot_a]
    | sort r =>
      simp only [LRS.DefEq.sort_a] at h ⊢
      cases m using WShape.casesOn' with
      | bot => simp only [LRS.TyDefEq.bot]
      | sort => cases WShape.sort_le.1 le; exact h
      | forallE s f =>
        simp only [LRS.TyDefEq.forallE_iff] at ⊢
        obtain ⟨s', f', h1, h2, rfl⟩ := WShape.forallE_le.1 le
        simp only [LRS.TyDefEq.forallE_iff] at h ⊢
        have ⟨_, hm_pi, _⟩ := WShape.HasType.forallE_l.1 hm
        have ⟨_, hm'_pi, _⟩ := WShape.HasType.forallE_l.1 hm'
        let ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hBB', hFF', hValB, hEdge⟩ := h
        have ht := (WShape.HasTypePi.iff.1 hm_pi).1.isType
        have ht' := (WShape.HasTypePi.iff.1 hm'_pi).1.isType
        exact ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hBB', hFF', IH.mono_r_2_ty h1 ht ht' hValB,
          hEdge.mono_r_2 h1 h2 hm_pi hm'_pi (IH.left_ty hValB)⟩
      | lam => simp only [LRS.TyDefEq.lam_m]
      | ctor => simp only [LRS.TyDefEq.ctor_m]
      | indTy => simp only [LRS.TyDefEq.indTy_m]
    | forallE a₁ a₂ =>
      cases m using WShape.casesOn' with
      | bot => simp only [LRS.DefEq.bot_m]
      | lam f hf =>
        obtain ⟨g, hg, hm_lam⟩ := WShape.HasType.forallE_inv hm
        have hgf' : (WShape.lam f hf).1 = (WShape.lam' g).1 := congrArg (·.1) hg
        simp only [WShape.lam, WShape.lam'] at hgf'; split at hgf'
        · injection hgf' with hgf'; have := WShapeFun.ext hgf'.symm; subst this
          obtain ⟨g'', hg'', hm'_lam⟩ := WShape.HasType.forallE_inv hm'
          rw [hg''] at h
          by_cases hg''nz : g''.NonZero
          · rw [show WShape.lam' g'' = WShape.lam g'' hg''nz from
              (WShape.lam_eq_lam' (hl := hg''nz)).symm] at h
            simp only [LRS.DefEq.lam_forallE] at h ⊢
            rw [WShape.lam_eq_lam' (hl := hf), hg''] at le
            have le_g := WShape.lam'_le_lam'.1 le
            let ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ := h
            exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.mono_l le_g hm_lam hm'_lam⟩
          · simp only [WShape.lam', dif_neg hg''nz] at hg''
            cases WShape.le_bot.1 (hg'' ▸ le)
        · cases hgf'
      | _ => cases hm
    | indTy => simp only [LRS.DefEq.indTy_a]
    | _ =>
      exact absurd (WShape.HasType.isType hm)
        (by first | exact WShape.IsType.not_lam | exact WShape.IsType.not_ctor)
  join_ty {A B m₁ m₂} hC hm₁ hm₂ h1 h2 := by
    have ⟨_, hm₁⟩ := hm₁; have ⟨_, hm₂⟩ := hm₂
    cases hm₁.unfold with
    | bot h₁ => rwa [WShape.bot_join]
    | sort =>
      cases hm₂.unfold with
      | bot => rwa [WShape.join_bot]
      | sort =>
        simp only [WShape.sort_join_sort] at h1 h2 ⊢
        split <;> simp_all only [LRS.TyDefEq.sort_iff, WShape.Compat.sort_sort]
      | _ => cases hC
    | forallE hp₁ =>
      cases hm₂.unfold with | bot => rwa [WShape.join_bot] | forallE hp₂ => ?_ | _ => cases hC
      simp only [LRS.TyDefEq.forallE_iff] at h1 h2
      simp [WShape.Compat, WShape.forallE, Shape.Compat] at hC
      let ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB, hFF, hValB₁, hEdge₁⟩ := h1
      let ⟨_, _, _, _, u', v', rA', rB', hBB', hFF', hValB₂, hEdge₂⟩ := h2
      cases rA.determ .forallE rA' .forallE
      cases rB.determ .forallE rB' .forallE
      simp only [LRS.TyDefEq.forallE_iff, WShape.forallE_join_forallE hC.1 hC.2]
      have ht₁ := (WShape.HasTypePi.iff.1 hp₁).1.isType
      have ht₂ := (WShape.HasTypePi.iff.1 hp₂).1.isType
      refine ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB, hFF, IH.join_ty hC.1 ht₁ ht₂ hValB₁ hValB₂, ?_⟩
      exact .join ht₁ ht₂ hC.1 hp₁ hp₂ hC.2 hEdge₁ hEdge₂
    | indTy =>
      cases m₂ using WShape.casesOn' with
      | indTy => rw [WShape.indTy_join_indTy hC]; trivial
      | _ => trivial
  whr {M M' N N' A m a} hM hN := by
    cases a using WShape.casesOn' with
    | sort =>
      cases m using WShape.casesOn' with
      | sort =>
        constructor <;> intro ⟨u, r1, r2⟩
        · exact ⟨u, hM.determ_l r1 .sort, hN.determ_l r2 .sort⟩
        · exact ⟨u, .trans hM r1, .trans hN r2⟩
      | forallE =>
        constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, rest⟩
        · exact ⟨B₁, F₁, B₂, F₂, u, v, hM.determ_l rM .forallE, hN.determ_l rN .forallE, rest⟩
        · exact ⟨B₁, F₁, B₂, F₂, u, v, .trans hM rM, .trans hN rN, rest⟩
      | _ => rfl
    | forallE =>
      cases m using WShape.casesOn' with | lam => ?_ | _ => rfl
      constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, (LRS.LamDefEq.whr hM hN).1 hP⟩
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, (LRS.LamDefEq.whr hM hN).2 hP⟩
    | _ => rfl
  whr_ty {A A' B B' m} hA hB := by
    cases m using WShape.casesOn' with
    | sort =>
      constructor <;> intro ⟨u, r1, r2⟩
      · exact ⟨u, hA.determ_l r1 .sort, hB.determ_l r2 .sort⟩
      · exact ⟨u, .trans hA r1, .trans hB r2⟩
    | forallE =>
      constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, rest⟩
      · exact ⟨B₁, F₁, B₂, F₂, u, v, hA.determ_l rM .forallE, hB.determ_l rN .forallE, rest⟩
      · exact ⟨B₁, F₁, B₂, F₂, u, v, .trans hA rM, .trans hB rN, rest⟩
    | _ => rfl

def LR (Γ : List SExpr) : LogRel Γ n :=
  match n with
  | 0 => LR0
  | _+1 => LRS (LR Γ)

@[simp] theorem LR_zero : LR (n := 0) Γ = LR0 := rfl
@[simp] theorem LR_succ : LR (n := n+1) Γ = LRS (LR Γ) := rfl

private theorem LRS.PiDefEq.lift_aux
    {b : WShape n} {f : WShapeFun n} (le : n ≤ n') (htpi_a : WShape.HasTypePi f b r)
    (IH1 : ∀ {M N : SExpr} {m : WShape n}, WShape.IsType m →
      ((LR Γ).TyDefEq M N (m.lift n') ↔ (LR Γ).TyDefEq M N m))
    (IH2 : ∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      ((LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a)) :
    LRS.PiDefEq (LR Γ) B F₁ F₂ (b.lift n') (f.lift n') ↔
    LRS.PiDefEq (LR Γ) B F₁ F₂ b f := by
  have htpi_w := WShape.HasTypePi.iff.1 htpi_a
  constructor <;> intro hEdge
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (WShape.HasType.lift le).2 hp
      have v' := (IH2 hp).2 v)
    · have ⟨r1, r2⟩ := hEdge.1 hp' ha v'
      exact ⟨(IH1 (htpi_w.2 _ hp).toIsType).1 (WShapeFun.lift_app le ▸ r1),
             (IH1 (htpi_w.2 _ hp).toIsType).1 (WShapeFun.lift_app le ▸ r2)⟩
    · exact (IH1 (htpi_w.2 _ hp).toIsType).1 (WShapeFun.lift_app le ▸ hEdge.2 hp' ha v')
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      obtain ⟨q, d1, d2⟩ := WShapeFun.app_eq (f.lift n') _
      obtain ⟨q₀, y₀, d2₀, rfl, d3⟩ := (WShapeFun.mem_lift le).1 d2
      obtain ⟨qx', qy', d2₀', qxle, qyle, hq⟩ := WShape.HasDom.def.1 htpi_a.1 _ _ d2₀
      have v' := (IH2 hq).1 ((LR Γ).mono_l (((WShape.lift_le_lift le).2 qxle).trans d1)
        ((WShape.HasType.lift le).2 hq) hp v))
    · have ⟨r1, r2⟩ := hEdge.1 hq ha v'
      have ht_q0 := htpi_w.2 _ hq
      have ht_q := ht_q0.toIsType
      have ht_y₀0 : (y₀ : WShape n).HasType (WShape.sort r) := htpi_a.2 _ _ d2₀
      have y₀_le_fqx : y₀ ≤ f.app qx' := qyle.trans (f.app_of_mem d2₀').2
      have ht_q_l : ((f.app qx').lift n').IsType :=
        ⟨_, by have := (WShape.HasType.lift le).2 ht_q0; rwa [WShape.lift_sort] at this⟩
      have ht_y₀_l : (y₀.lift n').IsType :=
        ⟨_, by have := (WShape.HasType.lift le).2 ht_y₀0; rwa [WShape.lift_sort] at this⟩
      exact d3 ▸ ⟨
        (LR Γ).mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l ((IH1 ht_q).2 r1),
        (LR Γ).mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l ((IH1 ht_q).2 r2)⟩
    · have hq_body := hEdge.2 hq ha v'
      have ht_q0 := htpi_w.2 _ hq
      have ht_q := ht_q0.toIsType
      have ht_y₀0 : (y₀ : WShape n).HasType (WShape.sort r) := htpi_a.2 _ _ d2₀
      have y₀_le_fqx : y₀ ≤ f.app qx' := qyle.trans (f.app_of_mem d2₀').2
      have ht_q_l : ((f.app qx').lift n').IsType :=
        ⟨_, by have := (WShape.HasType.lift le).2 ht_q0; rwa [WShape.lift_sort] at this⟩
      have ht_y₀_l : (y₀.lift n').IsType :=
        ⟨_, by have := (WShape.HasType.lift le).2 ht_y₀0; rwa [WShape.lift_sort] at this⟩
      exact d3 ▸
        (LR Γ).mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l ((IH1 ht_q).2 hq_body)

private theorem LRS.LamDefEq.lift_aux
    {g : WShapeFun n} {a₁ a₂} (le : n ≤ n') (htm : WShape.HasTypeLam g a₁ a₂)
    (IH : ∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      ((LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a))
    (hEdge : LRS.PiDefEq (LR Γ) A₁ A₂ A₂ a₁ a₂) :
    LRS.LamDefEq (LR Γ) (n := n') M N A₁ A₂ (g.lift n') (a₁.lift n') (a₂.lift n') ↔
    LRS.LamDefEq (LR Γ) M N A₁ A₂ g a₁ a₂ := by
  have htm_w := WShape.HasTypeLam.iff.1 htm
  constructor <;> intro hP
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (WShape.HasType.lift le).2 hp
      have v' := (IH hp).2 v)
    · have ⟨r1, r2⟩ := hP.1 hp' ha v'
      refine ⟨(IH (htm_w.2.2 _ hp)).1 ?_, (IH (htm_w.2.2 _ hp)).1 ?_⟩
        <;> rw [WShapeFun.lift_app le, WShapeFun.lift_app le] <;> [exact r1; exact r2]
    · apply (IH (htm_w.2.2 _ hp)).1
      rw [WShapeFun.lift_app le, WShapeFun.lift_app le]
      exact hP.2 hp' ha v'
  · refine ⟨fun a' b' p hp ha v => ?_, fun a' p hp ha v => ?_⟩
    all_goals
      obtain ⟨_, dg1, dg2⟩ := WShapeFun.app_eq (g.lift n') p
      obtain ⟨_, da1, da2⟩ := WShapeFun.app_eq (a₂.lift n') p
      obtain ⟨qg, yg, dg2₀, rfl, dg3⟩ := (WShapeFun.mem_lift le).1 dg2
      obtain ⟨qa, ya, da2₀, rfl, da3⟩ := (WShapeFun.mem_lift le).1 da2
      have ⟨yg₁, yg₂⟩ := WShapeFun.app_of_mem dg2₀
      have ⟨ya₁, ya₂⟩ := WShapeFun.app_of_mem da2₀
      have ⟨qg', qg'le, hqg, qg'app⟩ := WShape.HasDom.iff.1 htm.2.1 qg
      have ⟨_, htm_pi⟩ := htm.1
      have ⟨qa', qa'le, hqa, qa'app⟩ := WShape.HasDom.iff.1 htm_pi.1 qa
      rw [dg3, da3]
      have v_lo := (IH hqg).1 <| (LR Γ).mono_l
        (((WShape.lift_le_lift le).2 qg'le).trans dg1) ((WShape.HasType.lift le).2 hqg) hp v
      have v_lo_qa := (IH hqa).1 <| (LR Γ).mono_l
        (((WShape.lift_le_lift le).2 qa'le).trans da1) ((WShape.HasType.lift le).2 hqa) hp v
      have ht_lo := htm_w.2.2 _ hqg
      have ⟨_, htm_w1⟩ := htm_w.1
      have htm_p := WShape.HasTypePi.iff'.1 htm_w1
      have vt_qa := hEdge.2 hqa ha.hasType.1 ((LR Γ).left v_lo_qa)
      have vt_qa' := (LR Γ).mono_r_2_ty qa'app (htm_p.2 qa).toIsType (htm_p.2 qa').toIsType vt_qa
      have ya_sort := (htm_p.2 qa).mono_l ya₁ ya₂
      have ht_yg_qg' : yg.HasType (a₂.app qg') :=
        ht_lo.mono_l (WShapeFun.app_mono_r qg'le |>.trans yg₁) (yg₂.trans qg'app)
      have le_a2_ya := by
        refine (a₂.app_mono_r qg'le).trans (.trans ?_ ya₁)
        rw [← WShape.lift_le_lift le, WShapeFun.lift_app le]
        exact (WShapeFun.app_mono_r dg1 (f := a₂.lift n')).trans <| da3 ▸ WShape.lift_mono le ya₂
      have ya_sort := (htm_p.2 qa).mono_l ya₁ ya₂
      have ht_yg := ya_sort.mono_r le_a2_ya ht_yg_qg'
      have vt_ya := (LR Γ).mono_r_2_ty ya₂ ya_sort.toIsType (htm_p.2 qa).toIsType vt_qa'
      have go {M N} (r : (LR Γ).DefEq M N (A₂.inst a') (g.app qg') (a₂.app qg')) :
          (LR Γ).DefEq M N (A₂.inst a') (yg.lift n') (ya.lift n') :=
        (IH ht_yg).2 <|
        (LR Γ).mono_r_1 le_a2_ya ht_yg_qg' ht_yg vt_ya <|
        (LR Γ).mono_l (yg₂.trans qg'app) ht_yg_qg' ht_lo r
    · have ⟨r1, r2⟩ := hP.1 hqg ha v_lo; exact ⟨go r1, go r2⟩
    · exact go (hP.2 hqg ha v_lo)

private theorem LR.lift_succ_aux :
    (∀ {M N : SExpr} {m : WShape n}, WShape.IsType m →
      (LRS.TyDefEq (n := n) (LR Γ) M N (m.lift _) ↔ (LR Γ).TyDefEq M N m)) ∧
    (∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      (LRS.DefEq (n := n) (LR Γ) M N A (m.lift _) (a.lift _) ↔ (LR Γ).DefEq M N A m a)) := by
  induction n with
  | zero =>
    refine ⟨fun {M N m} _ => ?_, fun {M N A m a} _ => ?_⟩
    · cases m using WShape.casesOn <;> trivial
    · cases m using WShape.casesOn <;> cases a using WShape.casesOn <;> trivial
  | succ k ih =>
    refine have h1 := ?_; ⟨h1, ?_⟩
    · intro M N m hmt
      cases m using WShape.casesOn' with
      | lam f hf => exact absurd hmt WShape.IsType.not_lam
      | ctor => exact absurd hmt WShape.IsType.not_ctor
      | forallE b f => ?_
      | _ => constructor <;> intro <;> trivial
      rw [WShape.lift_forallE (Nat.le_succ k)]
      have ⟨_, hmt_is⟩ := hmt
      have ⟨_, htpi, _⟩ := WShape.HasType.forallE_l.1 hmt_is
      constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, hValB, hE⟩ <;>
        refine ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, ?_, ?_⟩
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi).1.isType).1 hValB
      · exact (LRS.PiDefEq.lift_aux (Nat.le_succ k) htpi ih.1 ih.2).1 hE
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi).1.isType).2 hValB
      · exact (LRS.PiDefEq.lift_aux (Nat.le_succ k) htpi ih.1 ih.2).2 hE
    · intro M N A m a hma
      cases a using WShape.casesOn' with
      | bot | indTy => constructor <;> intro <;> trivial
      | sort => exact h1 hma.toIsType
      | forallE a₁ a₂ => ?_
      | _ =>
        exact absurd (WShape.HasType.isType hma)
          (by first | exact WShape.IsType.not_lam | exact WShape.IsType.not_ctor)
      have ⟨_, hma_is⟩ := WShape.HasType.isType hma
      have ⟨_, htpi_a, _⟩ := WShape.HasType.forallE_l.1 hma_is
      obtain ⟨g, rfl, htm⟩ := WShape.HasType.forallE_inv hma
      unfold WShape.lam'; split <;> [skip; (simp; trivial)]
      rw [WShape.lift_lam (Nat.le_succ k), WShape.lift_forallE (Nat.le_succ k)]
      simp only [LRS.DefEq.lam_forallE]
      constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge, hP⟩ <;>
        [ have hEdge' := (LRS.PiDefEq.lift_aux (Nat.le_succ k) htm.1.choose_spec ih.1 ih.2).1 hEdge;
          have hEdge' := (LRS.PiDefEq.lift_aux (Nat.le_succ k) htm.1.choose_spec ih.1 ih.2).2 hEdge ] <;>
        refine ⟨A₁, A₂, u, v, rA, hA1, ?_, hA₂, hEdge', ?_⟩
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).1 hValA
      · exact (LRS.LamDefEq.lift_aux (Nat.le_succ k) htm ih.2 hEdge').1 hP
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).2 hValA
      · exact (LRS.LamDefEq.lift_aux (Nat.le_succ k) htm ih.2 hEdge).2 hP

theorem LR.DefEq.lift {m a : WShape n} (le : n ≤ n') (hma : WShape.HasType m a) :
    (LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a := by
  induction le with | refl => simp [WShape.lift_self] | step le ih
  rw [(WShape.lift_lift (.inl le)).symm, (WShape.lift_lift (s := a) (.inl le)).symm]
  exact (LR.lift_succ_aux.2 ((WShape.HasType.lift le).2 hma)).trans ih

theorem LR.TyDefEq.lift {m : WShape n} (le : n ≤ n') (hmt : m.IsType) :
    (LR Γ).TyDefEq (n := n') M N (m.lift _) ↔ (LR Γ).TyDefEq M N m := by
  induction le with | refl => simp [WShape.lift_self] | step le ih
  rw [(WShape.lift_lift (.inl le)).symm]
  have ⟨r, hr⟩ := hmt
  have : WShape.IsType (m.lift _) :=
    ⟨r, by have := (WShape.HasType.lift le).2 hr; rwa [WShape.lift_sort] at this⟩
  exact (LR.lift_succ_aux.1 this).trans ih


def LR.Subst1 (Γ₀ : List SExpr) (x x' A₀ A A' : SExpr) (ρ : Valuation) (i := 0) : Prop :=
  Γ₀ ⊢ x ≡ x' : A ∧ ∀ {{n}} (a : WShape n), LE_Interp ρ a.T A₀ →
    (a.IsType → (∃ u, Γ₀ ⊢ A ≡ A' : .sort u) ∧ (LR Γ₀).TyDefEq A A' a) ∧
    ∀ {{m : WShape n}}, LE_Interp ρ m.T (.bvar i) → m.HasType a → (LR Γ₀).DefEq x x' A m a

inductive LR.SubstWF (Γ₀ : List SExpr) : Subst → Subst → List SExpr → Valuation → Prop where
  | id : LR.SubstWF Γ₀ .id .id Γ₀ .nil
  | cons : LR.SubstWF Γ₀ σ.tail σ'.tail Γ ρ →
    (∀ {a}, LE_Interp ρ a A →
      ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.IsType) →
    LE_Interp ρ a A → x.HasType a → Γ ⊢ A : .sort u →
    LR.Subst1 Γ₀ σ.head σ'.head A.lift (A.subst σ.tail) (A.subst σ'.tail) (ρ.push x) →
    LR.SubstWF Γ₀ σ σ' (A :: Γ) (ρ.push x)

theorem LR.SubstWF.fits : LR.SubstWF Γ₀ σ σ' Γ ρ → ρ.Fits Γ₀ Γ
  | .id => .nil
  | .cons W h1 h2 h3 _ _ => .cons W.fits h1 h2 h3

theorem LR.SubstWF.toSubstEq : LR.SubstWF Γ₀ σ σ' Γ ρ → Ctx.SubstEq Γ₀ σ σ' Γ
  | .id => .nil
  | .cons W _ _ _ hA h0 => .cons W.toSubstEq hA h0.1

theorem LR.SubstWF.left (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ h1 h2 h3 hA h0 ih =>
    refine .cons ih h1 h2 h3 hA ⟨h0.1.hasType.1, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, h2⟩ := (h0.2 a ha).1 ht; exact ⟨⟨_, h1.hasType.1⟩, (LR _).left_ty h2⟩
    · exact (LR _).left <| (h0.2 a ha).2 hM hmem

theorem LR.SubstWF.symm (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ' σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ h1 h2 h3 hA h0 ih =>
    refine .cons ih h1 h2 h3 hA ⟨?_, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, _⟩ := (h0.2 (n := 0) _ .bot).1 ⟨true, .bot .sort⟩
      exact h1.defeqDF h0.1.symm
    · exact let ⟨⟨u, h1⟩, h2⟩ := (h0.2 a ha).1 ht; ⟨⟨u, h1.symm⟩, (LR _).symm_ty h2⟩
    · let ⟨_, h2⟩ := (h0.2 a ha).1 hmem.isType
      exact (LR _).conv h2 ((LR _).symm ((h0.2 a ha).2 hM hmem))

section JoinSortProbe
/-! ## Is `join_sort` -- `IsType.common` relativised to `TyDefEq` -- true?

`cx_refutes` kills the `Compat`-only form; `le_interp_common_fails` kills the
"realize the same term" form.  The costed proposal was to relativise to `TyDefEq` at a common
`A B`, on the strength of `common_of_not_forallE` (`Compat` pins the sort in 35 of the 36
constructor pairs) plus "`ValTyPi2` supplies at `forallE`/`forallE` what `Compat` cannot".

**It does not.**  `piDefEq_cannot_see` already shows why: `PiDefEq`'s obligations are pointwise
in the key, and at every key typed at `cxB` at most one of `cxF`, `cxF'` has a non-`.bot`
value.  Below is the witness itself -- both counterexample shapes satisfy `TyDefEq` for one and
the same `A B`, so the relativisation is vacuous exactly where it was needed. -/

private def cxBW : WShape 1 := ⟨cxB, cxA_wf.1⟩
private def cxFW : WShapeFun 1 := ⟨cxF, cxA_wf.2⟩
private def cxFW' : WShapeFun 1 := ⟨cxF', cxA'_wf.2⟩

private theorem cxFW_val (p : WShape 1) :
    (cxFW.app p).1 = Shape.bot ∨ (cxFW.app p).1 = ShapeS.indTy false := by
  have ⟨x', _, hmem⟩ := cxFW.app_eq p
  rw [WShapeFun.mem_def] at hmem
  simp only [cxFW, cxF, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem ⊢
  rcases hmem with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]

private theorem cxFW'_val (p : WShape 1) :
    (cxFW'.app p).1 = Shape.bot ∨ (cxFW'.app p).1 = ShapeS.indTy true := by
  have ⟨x', _, hmem⟩ := cxFW'.app_eq p
  rw [WShapeFun.mem_def] at hmem
  simp only [cxFW', cxF', List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem ⊢
  rcases hmem with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]

/-- `LRS.TyDefEq` carries NO information at `.bot` or at `.indTy` -- both clauses are `True`.
That is the hole the witness walks through. -/
private theorem tyDefEq_of_val {Γ : List SExpr} {IH : LogRel Γ 0} {X Y : SExpr} {w : WShape 1}
    (h : w.1 = Shape.bot ∨ ∃ r, w.1 = ShapeS.indTy r) : LRS.TyDefEq IH X Y w := by
  obtain ⟨w, wf⟩ := w
  rcases h with h | ⟨r, h⟩ <;> subst h <;> trivial

private def cxM : SExpr := .forallE (.sort .zero) (.sort .zero)

/-- `ValTyPi2` holds for the counterexample domain and **either** codomain family, with one
and the same `A B`.  Every obligation is discharged without ever looking at a family value's
sort: the term-level fields are reflexivity at `.sort .zero`, and `PiDefEq`'s two components
land in `LRS.TyDefEq` at a `.bot`-or-`.indTy` shape, which is `True`. -/
private theorem cxValTyPi2 (f : WShapeFun 1)
    (hf : ∀ p : WShape 1, (f.app p).1 = Shape.bot ∨ ∃ r, (f.app p).1 = ShapeS.indTy r) :
    LRS.ValTyPi2 (Γ := []) (LR (n := 1) []) cxM cxM cxBW f := by
  refine ⟨.sort .zero, .sort .zero, .sort .zero, .sort .zero, .succ .zero, .succ .zero,
    .rfl, .rfl, .sort, .sort, ?_, ?_, ?_⟩
  · exact (LR (n := 1) []).sort_iff_ty.2 ⟨.zero, .rfl, .rfl⟩
  · intro a b' p _ _ _; exact ⟨tyDefEq_of_val (hf p), tyDefEq_of_val (hf p)⟩
  · intro a p _ _ _; exact tyDefEq_of_val (hf p)

/-- **`join_sort` is FALSE.**  Relativising `IsType.common` to `TyDefEq` at a common `A B` does
not recover it: `cx_refutes`'s two shapes both satisfy `TyDefEq` for the same `A B`, are
`Compat`, are each classified by a sort, and share none.

The mechanism is `piDefEq_cannot_see`: `PiDefEq` constrains a family pointwise in the key, and
the two families' disagreeing values sit at keys the other family does not reach.  So the
extra hypothesis is vacuous at exactly the one constructor pair where
`common_of_not_forallE` says it was needed. -/
private theorem join_sort_fails :
    ¬ ∀ {Γ : List SExpr} {A B : SExpr} {m₁ m₂ : WShape 2},
        m₁.Compat m₂ →
        LRS.TyDefEq (LR (n := 1) Γ) A B m₁ → LRS.TyDefEq (LR (n := 1) Γ) A B m₂ →
        m₁.IsType → m₂.IsType →
        ∃ r, m₁.HasType (.sort r) ∧ m₂.HasType (.sort r) := by
  intro H
  have h1 : LRS.TyDefEq (LR (n := 1) []) cxM cxM (WShape.forallE cxBW cxFW) :=
    cxValTyPi2 cxFW fun p => (cxFW_val p).imp id (⟨false, ·⟩)
  have h2 : LRS.TyDefEq (LR (n := 1) []) cxM cxM (WShape.forallE cxBW cxFW') :=
    cxValTyPi2 cxFW' fun p => (cxFW'_val p).imp id (⟨true, ·⟩)
  have hC : WShape.Compat (WShape.forallE cxBW cxFW) (WShape.forallE cxBW cxFW') := by
    show Shape.Compat cxA cxA' = true; rfl
  obtain ⟨r, hh1, hh2⟩ := H hC h1 h2
    ⟨false, by show Shape.hasType cxA (Shape.sort false) = true; rfl⟩
    ⟨true, by show Shape.hasType cxA' (Shape.sort true) = true; rfl⟩
  simp only [WShape.HasType, WShape.sort, WShape.forallE] at hh1 hh2
  cases r
  · exact Bool.noConfusion hh2
  · exact Bool.noConfusion hh1

end JoinSortProbe

section ExitProbes
/-! ## The two remaining section-7 exits, probed

Both were costed in the banner (section 10) and both were flagged "looks false".  These are
the probes.  Neither performs its exit; each isolates the one fact the exit destroys. -/

/-! ### Exit 1 -- give up `proofIrrel` at `Prop`-valued inductives -/

/-- **The obligation exit 1 drops is FALSE, and this is the mechanism.**

`strongSoundS`'s `proofIrrel` case must prove `LE_Interp rho m h <-> LE_Interp rho m h'` for
two proofs of the same `Prop`, with `rho` constrained only by `Valuation.Fits`.  Two proof
VARIABLES are the sharpest instance: `h := .bvar 0`, `h' := .bvar 1`.  `LE_Interp.bvar` reads
the shape straight off the valuation, so the two sides see `rho 0` and `rho 1` -- and
`LE_Interp` separates them the moment those differ and `m` is not `<= .bot`.

`Valuation.Fits.cons` pushes `x` with `x.HasType a` for an `a` realizing the variable's type.
When that type is a `Prop`-valued inductive, `a <= (.indTy false).T`, and section 7's gating
forces `x = .bot` (`WShape.HasType.indTy_false_bot`) -- so under the gating both entries are
`.bot`, `m <= .bot`, and the separation below cannot be instantiated.  **Exit 1 removes
exactly that**, `Fits` then admits a non-`.bot` proof shape, and this lemma applies. -/
private theorem exit1_bvar_separates {m : TShape} (hm : ¬ m ≤ TShape.bot) :
    LE_Interp ((Valuation.nil.push TShape.bot).push m) m (.bvar 0) ∧
    ¬ LE_Interp ((Valuation.nil.push TShape.bot).push m) m (.bvar 1) := by
  refine ⟨.bvar TShape.LE.rfl, fun h => ?_⟩
  cases h with
  | bot => exact hm TShape.bot_le'
  | bvar hle => exact hm hle

/-- ... and a non-`.bot` shape to instantiate it with. -/
private theorem exit1_witness :
    LE_Interp ((Valuation.nil.push TShape.bot).push (WShape.sort (n := 0) true).T)
        (WShape.sort (n := 0) true).T (.bvar 0) ∧
    ¬ LE_Interp ((Valuation.nil.push TShape.bot).push (WShape.sort (n := 0) true).T)
        (WShape.sort (n := 0) true).T (.bvar 1) :=
  exit1_bvar_separates fun h => by
    have := TShape.le_bot.1 h
    exact absurd (congrArg (·.1) this) (by simp [WShape.sort, WShape.bot, Shape.sort, Shape.bot])

/-! ### Exit 2(alpha) -- give the iota-pattern's constructor leaf a `.bot` shape

`Matches.unique`'s `app` case recovers the constructor and its argument list FROM the leaf
shape.  Read its proof: `head_wf` gives `classify c' = some (.ctor ..)`, hence
`IsStruct c' = false`, hence `WShape.ctor'` takes its `.ctor` branch, and then
`WShape.ctor.inj` + `List.reverse_inj` deliver `c'` and `rargs'`.  So `unique` rests on the
leaf being INJECTIVE, and exit 2(alpha) makes it constant on a `Prop`-valued head. -/

/-- The injectivity `Matches.unique` consumes.  It holds because `Pattern.WF` classifies a
constructor leaf as `.ctor`, never `.etaCtor`, so `IsStruct` is `false` there and the `.bot`
branch of `ctor'` is unreachable at exactly those positions. -/
private theorem ctor'_inj_of_not_struct {c : Name} (hc : IsStruct c = false)
    {l l' : List (WShape n)} (h : WShape.ctor' c l = WShape.ctor' c l') : l = l' := by
  have hg : ∀ l : List (WShape n), IsStruct c = true → WShape.ListNonZero l := by
    intro _ hs; exact absurd hs (by simp [hc])
  rw [WShape.ctor', dif_pos (hg l), WShape.ctor', dif_pos (hg l')] at h
  exact (WShape.ctor.inj.1 h).2

/-- A miniature of `Matches`' `app`/`var` interaction, parameterised by the LEAF-SHAPE
function so that exit 2(alpha) can be modelled without performing it.  The real `Matches.app`
builds `.ctor' c' rargs'.reverse` from an inner match whose argument list is otherwise free;
here `leaf z` stands for that index and `fun _ => z.T` for the path-map it determines. -/
private inductive ToyMatches (leaf : WShape 1 → WShape 2) : WShape 2 → (Unit → WShape 1) → Prop
  | mk (z : WShape 1) (idx : WShape 2) (h : idx = leaf z) : ToyMatches leaf idx (fun _ => z)

/-- With an injective leaf -- the situation today -- uniqueness holds. -/
private theorem toy_unique_of_inj {leaf : WShape 1 → WShape 2}
    (hinj : ∀ z z', leaf z = leaf z' → z = z') {idx m m'}
    (H : ToyMatches leaf idx m) (H' : ToyMatches leaf idx m') : m = m' := by
  cases H with | mk z _ hz => cases H' with | mk z' _ hz' =>
  cases hinj z z' (hz ▸ hz'); rfl

/-- **With a leaf that collapses, uniqueness is FALSE.**  Exit 2(alpha) gives a `Prop`-valued
constructor's leaf the shape `.bot` with its arguments UNCONSTRAINED, so the leaf is constant
there and the argument list is no longer recoverable. -/
private theorem toy_unique_fails :
    ¬ ∀ {idx m m'}, ToyMatches (fun _ => WShape.bot) idx m →
        ToyMatches (fun _ => WShape.bot) idx m' → m = m' := by
  intro H
  have heq := H (.mk WShape.bot WShape.bot rfl) (.mk (WShape.sort true) WShape.bot rfl)
  have := congrFun heq ()
  exact absurd (congrArg (·.1) this) (by simp [WShape.sort, WShape.bot, Shape.sort, Shape.bot])

/-! ### The re-indexing: is "the index carries the arguments" sufficient for `unique`? -/

/-- The same miniature, but with the matched datum in the INDEX rather than recoverable only
from the leaf shape.  The shape is still `leaf rec`, so it may collapse; what changed is that
`rec` is now an index of the relation. -/
private inductive ToyMatchesR (leaf : WShape 1 → WShape 2) :
    WShape 1 → WShape 2 → (Unit → WShape 1) → Prop
  | mk (z : WShape 1) : ToyMatchesR leaf z (leaf z) (fun _ => z)

/-- **Sufficient.**  Uniqueness holds for ANY `leaf`, injective or not. -/
private theorem toy_unique_of_record {leaf : WShape 1 → WShape 2} {rec idx m m'}
    (H : ToyMatchesR leaf rec idx m) (H' : ToyMatchesR leaf rec idx m') : m = m' := by
  cases H; cases H'; rfl

/-- ... and in particular for the collapsing leaf that `toy_unique_fails` refutes.  So the
re-indexing is the right shape of fix: `unique` stops needing the leaf to be injective. -/
private theorem toy_unique_of_record_bot {rec idx m m'}
    (H : ToyMatchesR (fun _ => WShape.bot) rec idx m)
    (H' : ToyMatchesR (fun _ => WShape.bot) rec idx m') : m = m' :=
  toy_unique_of_record H H'

end ExitProbes
