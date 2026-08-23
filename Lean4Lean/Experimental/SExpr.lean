/-
================================================================================
MIGRATION WIP -- HANDOFF NOTE.  READ ALL OF THIS BEFORE TOUCHING EITHER FILE.
================================================================================

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

### What that costs, over the 6-8 already reported

`compat_join` gains a `Fits`-style hypothesis, and its callers must supply it.  The blocker to
check first is `LE_Interp.subst`: it uses `.compat`/`.join'` EIGHT times, has no `Fits`, and
CONSTRUCTS the valuations it uses (`rho1.join rho2`, pointwise) -- so it would have to
establish the hypothesis for a joined valuation rather than assume it, and `Fits.join` does
not exist.  That is the next thing to test, and it is the join family's row zero.

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
-/

import Lean4Lean.Theory.Inductive.Decl
import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Pattern

namespace Lean4Lean
open Lean4Lean

inductive Classification where
  | ctor (arity : Nat)
  | etaCtor (params args : Nat)
  | symb (arity : Nat)
  /-- `rel` records whether the inductive is `Type`-valued (`true`) or `Prop`-valued
  (`false`). It is genuinely part of how a constant classifies, and it must live here rather
  than be looked up: `LE_Interp.Const.indTy` needs the shape's sort boolean to be a function
  of the *constant*, which is what makes two shapes over the same head unable to disagree
  about it -- see `docs/design-shape-lattice.md`. -/
  | indTy (arity : Nat) (rel : Bool)

def Classification.arity : Classification → Nat
  | .ctor k | .symb k | .indTy k _ => k
  | .etaCtor p a => p + a

def Pattern.WF (cl : Name → Option Classification) :
    Pattern → (top : Bool := true) → (extra : Nat := 0) → Prop
  | .const c, top, n => cl c = some (if top then .symb n else .ctor n)
  | .var p, top, n => WF cl p top (n + 1)
  | .app p p', top, n => WF cl p top (n + 1) ∧ WF cl p' false

class Params where
  env : VEnv
  henv : env.Ordered
  univs : Nat
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  classify : Name → Option Classification
  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_wf : Pat p r → p.WF classify
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  -- pat_wf : Pat p r → p.Matches e m1 m2 → HasType env univs Γ e A →
  --   r.2.OK (IsDefEqU env univs Γ) m1 m2 → IsDefEqU env univs Γ e (r.1.apply m1 m2)
  -- The mainline `VEnv.Params` also carries these three. They are deliberately *not* fields
  -- here: `WHRed.determ` was expected to need them and does not (see `not_of_matchesS`), so
  -- as fields they would be obligations on every `Params` instance with no consumer.
  -- Uncomment when something actually needs them.
  -- pat_app_l : Pat p r → Subpattern (.app p₁ p₂) p → ¬Subpattern (.app p₃ p₄) p₁
  -- pat_app_l_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none
  -- pat_app_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none
  -- pat_app_r_arity : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Arity (.const c) n p₂ → Arity (.const c) n' p₂' → n = n'
  -- extra_pat : env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
  --   ∃ p r m1 m2, Pat p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧ r.2.OK (IsDefEqU env univs Γ) m1 m2 ∧
  --   df.rhs.instL ls = r.1.apply m1 m2
open Params
variable [Params]

/-- A semantically quotiented version of `VLevel`. This avoids the need for some congruences.

The subtype condition is just "is the evaluation of *some* `VLevel`". It deliberately does
**not** ask for `VLevel.WF univs`: the levels occurring in a constant's type `ci.type` are
well-formed at `ci.uvars`, which has no relation to `univs`, and `SLevel.mk` must not lose
them — otherwise `SExpr.mk` fails to commute with `VExpr.instL` at constants and the
`const` rule of `SExpr.IsDefEq` stops being the image of `VEnv.IsDefEq.constDF`
(see `SExpr.mk_instL`). Well-formedness of the levels of a term is tracked on the `VExpr`
side by `VEnv.IsDefEq` itself, so nothing is lost by dropping it here. -/
def SLevel := { f : List Nat → Nat // ∃ l : VLevel, l.eval = f }

namespace SLevel

def zero : SLevel := ⟨_, .zero, rfl⟩

def mk (l : VLevel) : SLevel := ⟨_, l, rfl⟩

@[simp] theorem val_mk {l : VLevel} : (mk l).1 = l.eval := rfl

def succ (l : SLevel) : SLevel :=
  ⟨fun v => l.1 v + 1, let ⟨u, h2⟩ := l.2; ⟨u.succ, h2 ▸ rfl⟩⟩

def max (l₁ l₂ : SLevel) : SLevel :=
  ⟨fun v => (l₁.1 v).max (l₂.1 v),
    let ⟨u, h2⟩ := l₁.2; let ⟨v, h4⟩ := l₂.2; ⟨u.max v, h2 ▸ h4 ▸ rfl⟩⟩

def imax (l₁ l₂ : SLevel) : SLevel :=
  ⟨fun v => Lean.Nat.imax (l₁.1 v) (l₂.1 v),
    let ⟨u, h2⟩ := l₁.2; let ⟨v, h4⟩ := l₂.2; ⟨u.imax v, h2 ▸ h4 ▸ rfl⟩⟩

def inst (ls : List SLevel) (l : SLevel) : SLevel := by
  refine ⟨fun v => l.1 (ls.map (·.1 v)), ?_⟩
  simp [funext_iff]
  have ⟨ls', h3⟩ : ∃ ls' : List VLevel, ls'.Forall₂ (fun l' l => l'.eval = l.1) ls := by
    induction ls with
    | nil => exact ⟨_, .nil⟩
    | cons a l ih =>
      let ⟨l', h2⟩ := a.2; let ⟨ls', h3⟩ := ih
      exact ⟨l'::ls', .cons h2 h3⟩
  have ⟨l', h2⟩ := l.2
  refine ⟨l'.inst ls', fun v => ?_⟩
  simp [VLevel.eval_inst, ← h2]; congr 1
  rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h3.imp fun _ _ h => congrFun h _

end SLevel

inductive SExpr where
  | bvar (i : Nat)
  | sort (u : SLevel)
  | const (c : Name) (ls : List SLevel)
  | app (f a : SExpr)
  | lam (A e : SExpr)
  | forallE (A B : SExpr)

instance : Inhabited SExpr := ⟨.sort .zero⟩

namespace SExpr

@[simp] def lift' : SExpr → Lift → SExpr
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)

abbrev lift e := lift' e (.skip .refl)

theorem lift'_comp {e : SExpr} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [Lift.liftVar_comp, *]

theorem lift'_depth_zero {e : SExpr} (H : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [Lift.liftVar_depth_zero]

@[simp] theorem lift'_refl {e : SExpr} : e.lift' .refl = e := lift'_depth_zero rfl

def ClosedN : SExpr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ | .const .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩

theorem ClosedN.lift'_eq (self : ClosedN e k) (h : ρ.Fixes k) : lift' e ρ = e := by
  induction e generalizing k ρ with (simp [ClosedN] at self; simp [*])
  | bvar i => exact h.liftVar_eq self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩

theorem ClosedN.lift_eq (self : ClosedN e) : lift e = e := self.lift'_eq ⟨⟩

variable (ls : List SLevel) in
def instL : SExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (SLevel.inst ls))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL

theorem ClosedN.instL : ∀ {e}, ClosedN e k → ClosedN (e.instL ls) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.instL, h.2.instL⟩

def mk : VExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (.mk u)
  | .const c us => .const c (us.map .mk)
  | .app fn arg => .app (.mk fn) (.mk arg)
  | .lam ty body => .lam (.mk ty) (.mk body)
  | .forallE ty body => .forallE (.mk ty) (.mk body)

theorem _root_.Lean4Lean.VExpr.ClosedN.mkS : ∀ {e : VExpr}, e.ClosedN k → ClosedN (.mk e) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.mkS, h.2.mkS⟩

@[reducible] def Subst := Nat → SExpr

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

def Subst.Fixes (σ : Subst) (n : Nat) := ∀ i < n, σ i = .bvar i

theorem Subst.Fixes.zero : Fixes σ 0 := nofun

theorem Subst.Depth.add {σ : Subst} (H : σ.Depth n n') : σ.Depth (n + k) (n' + k) :=
  fun i => cast (by congr 2 <;> omega) <| H (k + i)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

theorem Subst.Depth.lift {σ : Subst} (H : σ.Depth n n') : σ.lift.Depth (n + 1) (n' + 1) :=
  fun i => by simp [Subst.lift, H i]; rfl

theorem Subst.Fixes.lift {σ : Subst} (H : σ.Fixes n) : σ.lift.Fixes (n + 1) := fun
  | 0, _ => rfl
  | n+1, h => by simp [Subst.lift, H _ (Nat.lt_of_succ_lt_succ h)]

def Subst.id : Subst := .bvar
def Subst.head (σ : Subst) : SExpr := σ 0
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl
theorem Subst.Depth.tail {σ : Subst} (H : σ.Depth n (n' + 1)) : σ.tail.Depth n n' := H

def Subst.cons (σ : Subst) (e : SExpr) : Subst
  | 0 => e
  | i+1 => σ i

theorem Subst.Depth.cons {σ : Subst} (H : σ.Depth n n') : (σ.cons e).Depth n (n' + 1) := H

abbrev Subst.one (e : SExpr) : Subst := .cons .id e

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

theorem Subst.Depth.trunc {σ : Subst} : (σ.trunc n n').Depth n n' := by
  intro i; simp [Subst.trunc]

def _root_.Lean4Lean.Lift.invS : Lift → Subst
  | .refl => .id
  | .skip ρ => ρ.invS.cons default
  | .cons ρ => ρ.invS.lift

theorem Subst.Depth.invS : ∀ (ρ : Lift), ρ.invS.Depth ρ.dom ρ.size
  | .refl => .id
  | .skip l => (invS l).cons
  | .cons l => (invS l).lift

@[simp] theorem Subst.head_cons : (cons σ e).head = e := rfl
@[simp] theorem Subst.tail_cons : (cons σ e).tail = σ := rfl

def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift_r, ← lift'_comp]

theorem lift_l_inv {ρ : Lift} : .lift_l ρ ρ.invS = Subst.id := by
  funext i; simp [Subst.lift_l, Subst.id]
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simp [Lift.invS, Subst.cons, ih]
  | cons ρ ih => cases i <;> simp [Lift.invS, Subst.lift, ih]

@[simp] theorem instL_lift' : (lift' e ρ).instL ls = lift' (e.instL ls) ρ := by
  cases e <;> simp [lift', instL, instL_lift']

def _root_.Lean4Lean.Lift.toSubst (ρ : Lift) : Subst := .lift_l ρ .id

theorem _root_.Lean4Lean.Lift.toSubst_apply (ρ : Lift) (i) : ρ.toSubst i = bvar (ρ.liftVar i) := rfl

theorem Subst.Depth.toSubst (ρ : Lift) : ρ.toSubst.Depth ρ.size ρ.dom := by
  intro i; simp [Lift.toSubst_apply]
  induction ρ <;> simp! [*] <;> omega

def subst : SExpr → Subst → SExpr
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, σ => .app (fn.subst σ) (arg.subst σ)
  | .lam ty body, σ => .lam (ty.subst σ) (body.subst σ.lift)
  | .forallE ty body, σ => .forallE (ty.subst σ) (body.subst σ.lift)

@[simp] theorem id_lift : Subst.id.lift = Subst.id := by funext i; cases i <;> rfl

@[simp] theorem subst_id {e : SExpr} : e.subst .id = e := by
  induction e <;> simp! [*]; rfl

theorem subst_lift' {e : SExpr} : (e.lift' ρ).subst σ = subst e (.lift_l ρ σ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_l_lift]; rfl

theorem lift'_subst {e : SExpr} : (e.subst σ).lift' ρ = subst e (.lift_r σ ρ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_r, Subst.lift_r_lift]

theorem lift'_inj {e e' : SExpr} {ρ : Lift} : e.lift' ρ = e'.lift' ρ ↔ e = e' :=
  ⟨(by simpa [subst_lift', lift_l_inv] using congrArg (·.subst ρ.invS) ·), (· ▸ rfl)⟩

theorem subst_toSubst {e : SExpr} : subst e ρ.toSubst = lift' e ρ := by
  simp [Lift.toSubst, ← subst_lift']

theorem subst_lift'_inv {e : SExpr} {ρ : Lift} : (e.lift' ρ).subst ρ.invS = e := by
  rw [subst_lift', lift_l_inv, subst_id]

nonrec def Subst.instL (ls : List SLevel) (σ : Subst) : Subst := instL ls ∘ σ

theorem Subst.instL_lift {σ : Subst} : (σ.instL ls).lift = σ.lift.instL ls := by
  funext i; obtain _|i := i <;> simp [Subst.instL, lift, SExpr.instL]

@[simp] theorem instL_subst : (subst e σ).instL ls = subst (e.instL ls) (σ.instL ls) := by
  cases e <;> simp [subst, instL, instL_subst, Subst.instL_lift] <;> simp [Subst.instL]

def Subst.comp (σ σ' : Subst) : Subst := fun x => (σ x).subst σ'

theorem Subst.comp_lift {σ σ' : Subst} : (σ.comp σ').lift = σ.lift.comp σ'.lift := by
  funext i; cases i <;> simp! [comp, SExpr.lift]
  rw [SExpr.lift, SExpr.lift, lift'_subst, subst_lift']; rfl

theorem subst_subst {e : SExpr} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

theorem lift_subst {e : SExpr} : e.lift.subst σ = e.subst σ.tail := by
  rw [lift, subst_lift', ← Subst.tail_eq_lift_l]

theorem lift_subst_cons {e : SExpr} : e.lift.subst (σ.cons t) = e.subst σ := by
  rw [lift_subst, Subst.tail_cons]

theorem Subst.lift_l_eq : Subst.lift_l ρ σ = Subst.comp ρ.toSubst σ := by
  funext; simp [lift_l, comp, Lift.toSubst_apply, SExpr.subst]

theorem Subst.lift_r_eq : Subst.lift_r σ ρ = Subst.comp σ ρ.toSubst := by
  funext i; simp [lift_r, comp, subst_toSubst]

theorem Subst.Depth.comp {σ σ' : Subst}
    (H : σ.Depth n₁ n₂) (H2 : σ'.Depth n₂ n₃) : (σ'.comp σ).Depth n₁ n₃ := by
  intro i; simp [Subst.comp, subst, H2 i, H i]

theorem Subst.Depth.lift_l {σ : Subst}
    (H : σ.Depth n ρ.size) : (Subst.lift_l ρ σ).Depth n ρ.dom := by
  rw [lift_l_eq]; exact .comp H (.toSubst _)

theorem Subst.Depth.lift_r {σ : Subst}
    (H : σ.Depth ρ.dom n) : (Subst.lift_r σ ρ).Depth ρ.size n := by
  rw [lift_r_eq]; exact .comp (.toSubst _) H

theorem ClosedN.subst_eq {e : SExpr} (self : ClosedN e k) (h : σ.Fixes k) : e.subst σ = e := by
  induction e generalizing k σ with (simp [ClosedN] at self; simp [*, SExpr.subst])
  | bvar i => exact h _ self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h.lift⟩

def inst (e a : SExpr) : SExpr := e.subst (.one a)

def Skips (e : SExpr) (ρ : Lift) : Prop := lift' (e.subst ρ.invS) ρ = e

theorem Skips.lift (e : SExpr) (ρ : Lift) : Skips (e.lift' ρ) ρ := by
  rw [Skips, subst_lift'_inv]

def Skips' : SExpr → (ρ : Lift) → Prop
  | .bvar i, ρ => ∃ j, ρ.liftVar j = i
  | .sort .., _ | .const .., _ => True
  | .app fn arg, ρ => fn.Skips' ρ ∧ arg.Skips' ρ
  | .lam ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons
  | .forallE ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons

theorem skips_iff {e : SExpr} {ρ : Lift} : Skips e ρ ↔ Skips' e ρ := by
  simp [Skips]; induction e generalizing ρ with simp!
  | app _ _ ih1 ih2 => exact and_congr ih1 ih2
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact and_congr ih1 (@ih2 ρ.cons)
  | bvar i =>
    constructor <;> [intro h; intro ⟨j, h⟩]
    · refine (?_ : have := (match ρ.invS i with | SExpr.bvar .. => True | _ => True); _); split
      · rename_i eq; cases eq ▸ h; exact ⟨_, rfl⟩
      · suffices ρ.invS i = default by cases this ▸ h
        clear h; rename_i h
        induction ρ generalizing i <;> simp [Lift.invS, Subst.id] at * <;>
          cases i <;> simp [Subst.cons, Subst.lift] at *
        case skip.succ ih i => exact ih _ h
        case cons.succ ih i => rw [ih i fun j h' => h _ (by rw [h']; rfl)]; rfl
    · refine .trans (?_ : _ = (bvar j).lift' ρ) (congrArg bvar h); congr 1
      rw [← h]; exact congrFun (@lift_l_inv _ ρ) j

theorem skips_inter {e : SExpr} : Skips e (ρ.inter ρ') ↔ Skips e ρ ∧ Skips e ρ' := by
  simp [skips_iff]
  induction e generalizing ρ ρ' with simp_all!
  | app => grind
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => have := @ih2 ρ.cons ρ'.cons; grind [Lift.inter]
  | bvar =>
    constructor
    · rintro ⟨j, rfl⟩; constructor
      · rw [Lift.inter_comm, ← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
      · rw [← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
    · rintro ⟨⟨i, h⟩, ⟨j, rfl⟩⟩
      induction ρ generalizing i j ρ' with
      | refl => simp [Lift.inter]
      | skip ρ ih =>
        cases ρ' with
        | refl => simp [Lift.inter]; cases h; exact ⟨_, rfl⟩
        | skip => simp_all [Lift.inter]; exact ih _ _ h
        | cons => cases j <;> simp_all [Lift.inter, Lift.liftVar]; exact ih _ _ h
      | cons ρ ih =>
        cases i <;> simp_all [Lift.liftVar]
        · cases ρ' with
          | refl => simp [Lift.inter]; cases h; exact ⟨0, rfl⟩
          | skip => let 0 := j; simp_all
          | cons => let 0 := j; exact ⟨0, rfl⟩
        · cases ρ' with
          | refl => cases h; exact ⟨_+1, rfl⟩
          | skip => simp_all [Lift.liftVar, Lift.inter]; exact ih _ _ h
          | cons =>
            let _+1 := j; simp_all [Lift.inter]
            have ⟨_, h⟩ := ih _ _ h; exact ⟨_+1, congrArg (·+1) h⟩

theorem lift_r_inj {σ σ' : Subst} : σ.lift_r ρ = σ'.lift_r ρ ↔ σ = σ' := by
  refine ⟨fun h => funext fun i => ?_, (· ▸ rfl)⟩
  simpa [Subst.lift_r, lift'_inj] using congrFun h i

theorem Subst.lift_r_comm (σ : Subst) (ρ : Lift) (H : Subst.Depth σ 0 n) :
    σ.lift_r ρ = .lift_l (ρ.consN n) ((σ.lift_r ρ).trunc 0 n) := by
  funext i; simp [Subst.lift_l, Subst.lift_r, Subst.trunc]
  have : (ρ.consN n).liftVar i = if n ≤ i then ρ.liftVar (i-n) + n else i := by
    clear H; induction n generalizing i <;> [skip; cases i] <;> simp! [*]; split <;> rfl
  rw [this]; split <;> simp
  have := H (i - n); rw [Nat.sub_add_cancel ‹_›] at this; simp [this]

theorem lift_r_one (e : SExpr) (ρ : Lift) :
    (Subst.one e).lift_r ρ = .lift_l ρ.cons (Subst.one (e.lift' ρ)) := by
  refine (Subst.lift_r_comm (Subst.one e) ρ .one).trans ?_; congr 1
  funext i; simp [Subst.trunc]
  cases i <;> simp [Subst.one, Subst.cons, Subst.lift_r, Subst.id]

theorem lift_inst (e : SExpr) : e.lift.inst e' = e := by
  rw [inst, Subst.one, lift, subst_lift', ← Subst.tail_eq_lift_l, Subst.tail_cons, subst_id]

theorem lift'_inst_hi (e1 e2 : SExpr) (ρ : Lift) :
    lift' (e1.inst e2) ρ = (lift' e1 ρ.cons).inst (lift' e2 ρ) := by
  simp [inst, subst_lift', lift'_subst, lift_r_one]

theorem subst_inst {e : SExpr} : (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  rw [SExpr.inst, SExpr.inst, subst_subst, subst_subst]; congr 1
  funext i; obtain _|i := i <;> simp [Subst.comp, Subst.lift, SExpr.subst]
  · simp [Subst.one, Subst.cons]
  · rw [← SExpr.inst, lift_inst]; rfl

theorem inst_lift_cons {e : SExpr} {σ : Subst} :
    (e.subst σ.lift).inst x = e.subst (σ.cons x) := by
  rw [SExpr.inst, subst_subst, Subst.one]; congr 1
  funext i; obtain _|i := i <;>
    simp [Subst.comp, Subst.lift, SExpr.subst, Subst.cons, lift_subst_cons]

inductive Ctx.Lift' : Lift → List SExpr → List SExpr → Prop where
  | refl : Ctx.Lift' .refl Γ Γ
  | skip : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.skip l) Γ (A :: Γ')
  | cons : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.cons l) (A::Γ) (A.lift' l :: Γ')

theorem Ctx.Lift'.one : Ctx.Lift' (.skip .refl) Γ (A::Γ) := .skip .refl

theorem Ctx.Lift'.comp (H1 : Ctx.Lift' l Γ₀ Γ₁) (H2 : Ctx.Lift' l' Γ₁ Γ₂) : Ctx.Lift' (l.comp l') Γ₀ Γ₂ := by
  induction H2 generalizing l Γ₀ with
  | refl => exact H1
  | skip _ ih => exact (ih H1).skip
  | cons H2 ih =>
    cases H1 with
    | refl => exact .cons H2
    | skip H1 => exact .skip (ih H1)
    | cons H1 => exact SExpr.lift'_comp ▸ .cons (ih H1)

inductive Ctx.Inter : List SExpr → List SExpr → Lift → List SExpr → Lift → List SExpr → Prop where
  | refl_l : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Δ .refl Γ ρ Δ
  | refl_r : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Γ ρ Δ .refl Δ
  | skip_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ → Ctx.Inter Γ Γ₁ (.skip ρ₁) Γ₂ (.skip ρ₂) (A::Δ)
  | skip_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ Γ₁ (.skip ρ₁) (A :: Γ₂) (.cons ρ₂) (A.lift' ρ₂ :: Δ)
  | cons_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ (A :: Γ₁) (.cons ρ₁) Γ₂ (.skip ρ₂) (A.lift' ρ₁ :: Δ)
  | cons_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter (A :: Γ) (A.lift' (ρ₂.diff ρ₁) :: Γ₁) (.cons ρ₁)
      (A.lift' (ρ₁.diff ρ₂) :: Γ₂) (.cons ρ₂) (A.lift' (ρ₁.inter ρ₂) :: Δ)

theorem lift_eq_lift {e₁ e₂ : SExpr} (H : e₁.lift' ρ₁ = e₂.lift' ρ₂) :
    ∃ e, .lift' e (ρ₂.diff ρ₁) = e₁ ∧ e.lift' (ρ₁.diff ρ₂) = e₂ := by
  have := Skips.lift e₁ ρ₁
  have h1 : _ = _ := skips_inter.2 ⟨.lift e₁ ρ₁, H ▸ Skips.lift e₂ ρ₂⟩
  have h2 := h1; conv at h1 => enter [1,2]; rw [← Lift.diff_comp]
  conv at h2 => enter [1,2]; rw [Lift.inter_comm, ← Lift.diff_comp]
  rw [lift'_comp] at h1 h2
  exact ⟨_, lift'_inj.1 h2, lift'_inj.1 (h1.trans H)⟩

theorem Ctx.Inter.mk (H1 : Ctx.Lift' l₁ Γ₁ Δ) (H2 : Ctx.Lift' l₂ Γ₂ Δ) :
    ∃ Γ, Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ := by
  induction H1 generalizing l₂ Γ₂ with
  | refl => exact ⟨_, .refl_l H2⟩
  | skip H1 ih =>
    cases H2 with
    | refl => exact ⟨_, .refl_r (.skip H1)⟩
    | skip H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_skip H⟩
    | cons H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_cons H⟩
  | @cons l₁ _ _ A₁ H1 ih =>
    generalize eq : A₁.lift' l₁ = A' at H2
    cases H2 with
    | refl => subst eq; exact ⟨_, .refl_r (.cons H1)⟩
    | skip H2 => subst eq; let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_skip H⟩
    | @cons l₂ _ _ A₂ H2 =>
      obtain ⟨_, rfl, rfl⟩ := lift_eq_lift eq
      rw [← lift'_comp, Lift.diff_comp]
      let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_cons H⟩

theorem Ctx.Inter.symm (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Inter Γ Γ₂ l₂ Γ₁ l₁ Δ := by
  induction H with
  | refl_l h => exact .refl_r h
  | refl_r h => exact .refl_l h
  | skip_skip _ ih => exact .skip_skip ih
  | skip_cons _ ih => exact .cons_skip ih
  | cons_skip _ ih => exact .skip_cons ih
  | cons_cons _ ih => rw [Lift.inter_comm]; exact .cons_cons ih

theorem Ctx.Inter.diff (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' (l₁.diff l₂) Γ Γ₂ := by
  induction H with
  | refl_l h => exact .refl
  | refl_r h => simpa
  | skip_skip _ ih | cons_skip _ ih => exact ih
  | skip_cons _ ih => exact ih.skip
  | cons_cons _ ih => exact ih.cons

theorem Ctx.Inter.right (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₂ Γ₂ Δ := by
  induction H with
  | refl_l h => exact h
  | refl_r h => exact .refl
  | skip_skip _ ih => exact ih.skip
  | cons_skip _ ih => exact ih.skip
  | skip_cons _ ih => exact ih.cons
  | cons_cons _ ih => rw [← Lift.diff_comp, SExpr.lift'_comp]; exact ih.cons

theorem Ctx.Inter.left (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₁ Γ₁ Δ := H.symm.right

/-- The `SExpr` mirror of `Pattern.Matches`, carrying a `p.LPath → List SLevel` map — one
level list **per leaf**, as the `VExpr`-side `Matches` does.

**This used to keep a single list, and that was a defect, not a simplification.** The old
docstring priced the deferral at one consequence — `applyS` ignoring an `RHS.fixed`'s
`LPath` — and there was a second. `Check.defeqsS` also dropped the two `LPath`s of a
`Check.level x i y j` clause and read *both* indices out of the one list. On the `VExpr` side
that clause relates the **recursor** leaf's list to the **constructor** leaf's, which is what
makes `iotaLevelPairs`' `(i+1, i)` true: `selfLvls` is the block's parameters shifted by one
when `isLE` prepends a fresh elimination universe, so both sides evaluate to `ls.getD (i+1)`.
Read out of one list it degenerated to `ls.getD (i+1) = ls.getD i`, relating the elimination
universe to a block parameter — and `extra_pat` quantifies over every `ls` of the right
length, so it demanded that for arbitrary `ls`. **False for any large eliminator with a
universe parameter: `List`, `Prod`, `Sum`, `Sigma`.** So `ParamsExtra` was still
unsatisfiable after the λ-peel, and `strongSoundS` was still vacuous.

The cost of carrying the map is much smaller than the old note guessed: four edits here
(this inductive, `RHS.applyS`, `Check.defeqsS`, and `MatchesS.determ`), and on the shape side
`LE_Interp.RHS` gains the `LPath` index while `LE_Interp.Const` drops its shared `ls`. One
obligation is left open there; see `ShapeLogRel.lean`'s banner, section 11. -/
inductive _root_.Lean4Lean.Pattern.MatchesS :
    (p : Pattern) → SExpr → (p.LPath → List SLevel) → (p.Path → SExpr) → Prop
  | const : MatchesS (.const c) (.const c ls) (fun _ => ls) nofun
  | var : MatchesS f f' f1 g1 → MatchesS (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : MatchesS f f' f1 g1 → MatchesS a a' f2 g2 →
    MatchesS (.app f a) (.app f' a') (Sum.elim f1 f2) (Sum.elim g1 g2)

/-- A pattern never matches a term whose head is a `lam`: `MatchesS`'s spine bottoms out
at `const`, and neither `var` nor `app` accepts a `lam`. This is what separates a `beta`
redex from an `extra` redex in `WHRed.determ`. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.not_lam {p : Pattern} {A e : SExpr} {m1 m2}
    (H : p.MatchesS (.lam A e) m1 m2) : False := nomatch H

/-- Two patterns matching the same term have a non-empty intersection. This is the
`MatchesS` mirror of `Pattern.matches_inter`'s forward direction, and it is what feeds
`Params.pat_uniq` in `WHRed.determ`. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.inter_exists {p : Pattern} {e : SExpr} {m1 m2}
    (hp : p.MatchesS e m1 m2) :
    ∀ {q : Pattern} {m3 m4}, q.MatchesS e m3 m4 → ∃ r, p.inter q = some r := by
  induction hp with
  | const => intro q _ _ hq; let .const := hq; simp [Pattern.inter]
  | var _ ih =>
    intro q _ _ hq
    cases hq with
    | var hq' => have ⟨_, h1⟩ := ih hq'; simp [Pattern.inter, h1]
    | app hqf _ => have ⟨_, h1⟩ := ih hqf; simp [Pattern.inter, h1]
  | app _ _ ihf iha =>
    intro q _ _ hq
    cases hq with
    | var hq' => have ⟨_, h1⟩ := ihf hq'; simp [Pattern.inter, h1]
    | app hqf hqa =>
      have ⟨_, h1⟩ := ihf hqf; have ⟨_, h2⟩ := iha hqa
      simp [Pattern.inter, h1, h2]

/-- A pattern determines its own match. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.determ {p : Pattern} {e : SExpr} {m1 m2 m1' m2'}
    (H1 : p.MatchesS e m1 m2) (H2 : p.MatchesS e m1' m2') : m1 = m1' ∧ m2 = m2' := by
  induction H1 with
  | const => let .const := H2; exact ⟨rfl, rfl⟩
  | var _ ih => let .var h := H2; have ⟨e1, e2⟩ := ih h; exact ⟨e1, by rw [e2]⟩
  | app _ _ ih1 ih2 =>
    let .app h1 h2 := H2
    have ⟨e1, e2⟩ := ih1 h1; have ⟨e3, e4⟩ := ih2 h2
    exact ⟨by rw [e1, e3], by rw [e2, e4]⟩

def _root_.Lean4Lean.Pattern.RHS.applyS {p : Pattern}
    (m1 : p.LPath → List SLevel) (m2 : p.Path → SExpr) : p.RHS → SExpr
  | .fixed c lp _ => .instL (m1 lp) (.mk c)
  | .var path => m2 path
  | .app f a => .app (f.applyS m1 m2) (a.applyS m1 m2)

def _root_.Lean4Lean.Pattern.RHS.Closed {p : Pattern} : p.RHS → Prop
  | .fixed c _ _ => c.Closed
  | .var _ => True
  | .app f a => f.Closed ∧ a.Closed

theorem _root_.Lean4Lean.Pattern.RHS.Closed.applyS {p : Pattern} {m1 m2} :
    ∀ r : p.RHS, r.Closed → (∀ a, (m2 a).ClosedN k) → (r.applyS m1 m2).ClosedN k
  | .fixed .., h1, _ => h1.mkS.instL.mono (Nat.zero_le _)
  | .var _, _, h2 => h2 _
  | .app .., h1, h2 => ⟨h1.1.applyS _ h2, h1.2.applyS _ h2⟩

/-- The term-level obligations of a `Check`.

A `Check.level x i y j` obligation is emitted as a defeq between two *sorts*: on the
`SExpr` side `SLevel` is already quotiented by `≈`, and
`SExpr.sort_inv : Γ ⊢ .sort u ≡ .sort v : V → u = v` turns that defeq back into the level
equation. So no separate level-checking predicate is needed here, and `WHRed.extra` keeps
its single `defeqsS` premise. -/
def _root_.Lean4Lean.Pattern.Check.defeqsS {p : Pattern}
    (m1 : p.LPath → List SLevel) (m2 : p.Path → SExpr) : p.Check → List (SExpr × SExpr)
  | .true => []
  | .defeq a b rest => (a.applyS m1 m2, b.applyS m1 m2) :: rest.defeqsS m1 m2
  | .level x i y j rest =>
    (.sort ((m1 x).getD i .zero), .sort ((m1 y).getD j .zero)) :: rest.defeqsS m1 m2

section
set_option hygiene false

inductive Lookup : List SExpr → Nat → SExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

theorem Lookup.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Lookup Γ i A) :
    Lookup Γ' (ρ.liftVar i) (A.lift' ρ) := by
  induction W generalizing i A with
  | refl => simp; exact H
  | skip W ih => have' := (ih H).succ; rwa [SExpr.lift, ← SExpr.lift'_comp] at this
  | cons W ih =>
    cases H with
    | zero => refine' cast _ Lookup.zero; congr 1; simp [SExpr.lift, ← SExpr.lift'_comp]
    | succ H => refine' cast _ (ih H).succ; congr 1; simp [SExpr.lift, ← SExpr.lift'_comp]

theorem Lookup.weakU_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) A') : ∃ A, A' = A.lift' ρ ∧ Lookup Γ i A := by
  induction W generalizing i A' with
  | refl => simpa using H
  | @skip ρ W _ _ _ ih =>
    simp at H; let .succ H := H
    obtain ⟨_, rfl, h2⟩ := ih H; refine ⟨_, ?_, h2⟩
    rw [SExpr.lift, ← SExpr.lift'_comp]; rfl
  | @cons ρ Γ Δ B W ih =>
    cases i with
    | zero => cases H; exact ⟨_, by simp [SExpr.lift, ← SExpr.lift'_comp], .zero⟩
    | succ i =>
      let .succ (ty := C) H := H
      obtain ⟨C, rfl, h⟩ := ih H
      refine ⟨_, ?_, .succ h⟩
      simp [SExpr.lift, ← SExpr.lift'_comp]

theorem Lookup.weak'_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) (A.lift' ρ)) : Lookup Γ i A := by
  let ⟨_, h1, h2⟩ := H.weakU_inv W
  exact SExpr.lift'_inj.1 h1 ▸ h2

theorem Lookup.uniq (hA : Lookup Γ i A) (hB : Lookup Γ i B) : A = B :=
  match hA, hB with
  | .zero, .zero => rfl
  | .succ hA, .succ hB => Lookup.uniq hA hB ▸ rfl

theorem Lookup.determ (H1 : Lookup Γ i A) (H2 : Lookup Γ i A') : A = A' := by
  induction H1 generalizing A' with obtain _ | r1 := H2
  | zero => rfl
  | succ _ ih => cases ih r1; rfl

scoped notation:65 Γ " ⊢ " e " : " A:36 => IsDefEq Γ e e A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq Γ e1 e2 A
inductive IsDefEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls : (SExpr.mk ci.type).instL ls
  | appDF : Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  -- | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
  --   (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) → Γ ⊢ e ≡ r.1.applyS m1 m2' : A
  | extra : env.defeqs df → ls.length = df.uvars →
    Γ ⊢ .instL ls (.mk df.lhs) ≡ .instL ls (.mk df.rhs) : .instL ls (.mk df.type)

/-- λ-telescope builder, mirroring `VExpr.mkLams`.  Needed only to state `extra_pat`'s peel;
see that field's docstring.

**Declared WITHOUT an `SExpr.` prefix on purpose.**  This sits inside `namespace SExpr`, so
`def SExpr.mkLams` would declare `Lean4Lean.SExpr.SExpr.mkLams` and thereby CREATE the
namespace `Lean4Lean.SExpr.SExpr`.  Every later `SExpr.Foo` written inside
`namespace Lean4Lean.SExpr` -- in this file or any consumer -- then resolves there first and
fails.  It surfaced as `Unknown constant Lean4Lean.SExpr.SExpr.Subst` in
`Experimental/LogRel.lean`, a file this stream does not otherwise touch. -/
def mkLams : List SExpr → SExpr → SExpr
  | [], b => b
  | A :: As, b => .lam A (mkLams As b)

@[simp] theorem mkLams_nil {b} : mkLams [] b = b := rfl
@[simp] theorem mkLams_cons {A As b} : mkLams (A :: As) b = .lam A (mkLams As b) := rfl

/--
The pattern discipline for the environment's definitional equality rules: every `extra`
rule of `env` is an instance of a `Pat`-registered pattern, whose `Check` side conditions
hold in `Γ`.

This is a class separate from `Params` only because `Params` has to be declared before
`SExpr` exists, while this statement mentions `SExpr.IsDefEq`.

It must **not** be an `axiom`. The statement is refutable: `Pat := fun _ _ => False`
satisfies every field of `Params` vacuously, and then `extra_pat` yields `False` for any
environment carrying a definitional equality rule. As an axiom it therefore made every
downstream result silently vacuous — and `Experimental/` is outside `kernel_sound`'s cone,
so `Verify/Guard.lean` would not have caught it.
-/
class ParamsExtra [Params] where
  /--
  **λ-peeled.**  The unpeeled form -- asking for `p.MatchesS (.instL ls (.mk df.lhs))` on the
  left-hand side as stored -- is UNSATISFIABLE, and `unpeeled_extra_pat_unsatisfiable` below
  is the proof.  `Pattern.MatchesS` bottoms out at `const` and never accepts a `lam`
  (`Pattern.MatchesS.not_lam`), while `SExpr.mk` and `SExpr.instL` are both structural on
  `lam`, so a binder in `df.lhs` survives both.  And every rule shape in a real environment
  has binders: `quotDefEq.lhs` is `fun α r β f c a => …` (six), and an ι-rule's lhs is
  `mkLams (iotaCtx C) _` with `iotaCtx` never empty.  So the unpeeled field admits no
  instance for any environment carrying a quotient rule or an ι-rule -- i.e. any real one.

  This mirrors the cure the mainline `VEnv.Params.extra_pat` already has; see
  `Pat.extra_delta` / `Pat.extra_quot` / `Pat.extra_iota` in
  `Theory/Typing/PatternRules.lean`, and `PLAN.md`'s "`extra_pat` is unsatisfiable" entry.
  The two sides share their telescope `Δ`, which is what lets the check clauses be discharged
  over `Δ.reverse ++ Γ`.

  **The shape below is the mainline's, clause for clause**, so that an instance can transport
  `Pat.extra` across `SExpr.mk` rather than reprove anything.  Against
  `Theory/Typing/PatternRules.lean`'s

      Pat.extra : ∃ Δ L R p r m1 m2,
        df.lhs.instL ls = mkLams Δ L ∧ df.rhs.instL ls = mkLams Δ R ∧
        Pat env p r ∧ Pattern.Matches p L m1 m2 ∧
        (r.2).OK (env.IsDefEqU U (Δ.reverse ++ Γ)) m1 m2 ∧ R = (r.1).apply m1 m2

  the binder order, the six conjuncts, their order, the `Δ.reverse ++ Γ` on the check side and
  the orientation of the last equation all agree.  The only differences are the `SExpr`
  spellings -- `.instL ls (.mk ·)` for `.instL ls`, `MatchesS` for `Matches`, and the `dfs`
  list in place of `Check.OK`, which is how this file has encoded the check side since
  `WHRed.extra` and is not something the peel introduced. -/
  extra_pat (Γ : List SExpr) {df : VDefEq} {ls : List SLevel} :
    env.defeqs df → ls.length = df.uvars →
    ∃ Δ L R p r m1 m2 dfs,
      .instL ls (.mk df.lhs) = mkLams Δ L ∧
      .instL ls (.mk df.rhs) = mkLams Δ R ∧
      Pat p r ∧ p.MatchesS L m1 m2 ∧
      (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 ∧
      (∀ a b A, (A, a, b) ∈ dfs → Δ.reverse ++ Γ ⊢ a ≡ b : A) ∧
      R = r.1.applyS m1 m2
  /--
  Constructor types are Π-telescopes over their inductive type.

  Stated as a **syntactic** equation on `ci.type`, because `VIndCtor.type`
  (`Theory/Inductive/Decl.lean`) is a computing `def`: the binder count, the head constant
  and the head's arguments are all readable by `simp`, with no conversion reasoning at all.
  `SExpr.mk_instL` (`Experimental/Bridge.lean`) then transports it to `SExpr`.

  The declaration is *carried* rather than looked up, because `VEnv.Sig` (design §7.7) does
  not exist yet; switching to a lookup when it does is mechanical.

  Two deliberate choices, both flagged by the keystone stream. The head arity is
  `D.np + T.indices.length`, which is constructor-*independent* — `C.args.length` would
  assert that one `classify` value equals a per-constructor quantity, rescued only by
  `args_len`. And the result is stated over `C.params.reverse`, not `D.params.reverse`, so
  that every clause is read off `ci.type = mkPi (C.params ++ …) …` in **one** context;
  `VIndCtor.WF.result'` is the transport that delivers it. `C.params` and `D.params` are
  only *definitionally* equal, so mixing the two would silently mix contexts.

  **`D.lvl ≠ .zero` is NOT asserted. It was, and it was false.** `D.lvl` is the block's
  common result universe, so it is `.zero` for *every* `Prop`-valued inductive — `Eq`, `And`,
  `Or`, `Exists`, `False` — and those must be classified, because their recursors' ι-rules
  pattern-match on their constructors. Asserting it made this class unsatisfiable for any
  realistic environment, and nothing caught that, because there is no `ParamsExtra` instance
  in the tree. What the field asserts now is the *tie* `rel = true ↔ D.lvl ≠ .zero`, which
  **records** the block's `Prop`-ness in the classification instead of forbidding it.

  Two consequences, both opposite to what the old text said:

  * `classify Eq.refl` **is** `.ctor` (with `rel = false`), so `CtorBundle.IsCtor Eq.refl`
    holds and `∀ cl, CtorBundle c cl` is *not* vacuous. `CtorBundle.hu0` was therefore false;
    it has been replaced by `hrel : rel = true ↔ u ≠ .zero` — see that structure's docstring.
  * **`Pattern.WF` does NOT need relaxing.** It still demands a `.ctor` leaf at a constructor
    position (its `.const` clause), `Eq.refl` still supplies one, and `Eq.rec`'s ι-rule is
    still a pattern. Relaxing it was route (β) of the `.indTy` migration, and (β) is
    *refuted*: `Eq` is a `Prop` that **large**-eliminates, so its ι-rule cannot be dropped —
    see `eq_large_eliminates` in `Experimental/ShapeLogRel.lean`, and that file's banner §7.

  The sort of `ci.type` is `imax … D.lvl` and `imax x y = .zero ↔ y = .zero`, so
  `D.lvl ≠ .zero` is equivalent to the constructor's type not being a `Prop`; that equivalence
  is what makes the tie above the right way to state it. The result-sort clause is
  `VIndCtor.WF.result'`'s content.

  *(This paragraph replaces one that survived the change it described, and the replacement is
  recorded rather than silently made: a docstring that outlives its own fix is worse than no
  docstring, because it reads as a live constraint. The Params stream read the old text,
  concluded `Params` + `ParamsExtra` were newly jointly unsatisfiable — and it was right about
  the world the text described, since `Pattern.WF` is indeed unrelaxed — and only disconfirmed
  it by reading the field body below.)*
  -/
  ctor_ty {c : Name} {cl : Classification} {ci : VConstant} :
    classify c = some cl → (cl matches .ctor .. | .etaCtor ..) →
    env.constants c = some ci →
    ∃ (D : VInductDecl') (j : Nat) (T : VIndType) (C : VIndCtor) (rel : Bool),
      D.types[j]? = some T ∧ C ∈ T.ctors ∧ C.name = c ∧
      (C.params ++ C.fields.map (·.type)).length = cl.arity ∧
      classify T.name = some (.indTy (D.np + T.indices.length) rel) ∧
      -- `rel` is the block's result universe, recorded in the classification so that the
      -- shape model can read it off the head constant alone.
      (rel = true ↔ D.lvl ≠ .zero) ∧
      -- `D.lvl ≠ .zero` used to sit here.  It is **false**: `D.lvl` is the block's common
      -- result universe, so it is `.zero` for every `Prop`-valued inductive (`Eq`, `And`,
      -- `Or`, `Exists`, `False`) -- and those must be classified, since their recursors'
      -- iota-rules pattern-match on their constructors.  With it, `ParamsExtra` was
      -- unsatisfiable for any realistic environment, which no instance ever caught because
      -- there is no `ParamsExtra` instance in the tree.  `CtorBundle.hu0` was the same claim
      -- one layer down; it has been repaired too, and is now `hrel`.
      -- Everything the declaration side owns is bundled: the stored constant (so `ci` is
      -- determined), arities, `args_len`, the result sort over `C.params.reverse`, and the
      -- split closedness facts.  Widening this is a field of `Interface`, not a clause here.
      VIndCtor.Interface env D j T C

/-! ### Regression tests for `ParamsExtra.extra_pat`'s λ-peel

These are stated as *conditionals on an unpeeled field*, so they cannot rot: they hold
whatever the real field says, and anyone who restates `extra_pat` without the peel can
instantiate `unpeeled` with it and read off `False`. -/

/-- **The unpeeled form of `extra_pat` is unsatisfiable for any rule whose left-hand side is
a `lam`.**  `Pattern.MatchesS` bottoms out at `const` and never accepts a `lam`
(`Pattern.MatchesS.not_lam`), and both `SExpr.mk` and `SExpr.instL` are structural on `lam`,
so the binder survives both. -/
theorem unpeeled_extra_pat_unsatisfiable [Params]
    (unpeeled : ∀ {df : VDefEq} {ls : List SLevel}, env.defeqs df → ls.length = df.uvars →
      ∃ p r m1 m2, Pat p r ∧ p.MatchesS (.instL ls (.mk df.lhs)) m1 m2)
    {df : VDefEq} {A b : VExpr} (hdf : env.defeqs df) (hlam : df.lhs = VExpr.lam A b) :
    False := by
  obtain ⟨p, r, m1, m2, _, hM⟩ :=
    unpeeled (ls := List.replicate df.uvars (SLevel.mk .zero)) hdf (by simp)
  rw [hlam] at hM
  exact hM.not_lam

/-- **And every ι-rule's left-hand side IS a `lam`**, because `iotaCtx` is never empty
(`D.motives` has one entry per type of the block and `D.types ≠ []`).  With
`unpeeled_extra_pat_unsatisfiable` this says: no environment carrying an inductive admits an
unpeeled `ParamsExtra`.  The quotient rule is the same story --
`quotDefEq.lhs = fun α r β f c a => …`, six binders -- and is not repeated here only because
it would cost this file an import of `Theory.Quot`. -/
theorem iota_lhs_lam {D : VInductDecl'} {j q : Nat} {C : VIndCtor} {T : VIndType}
    (hT : D.types[j]? = some T) : ∃ A b, (D.iotaRule j q C).lhs = VExpr.lam A b := by
  refine ⟨(D.iotaCtx C).headD default,
    VExpr.mkLams ((D.iotaCtx C).tail) (D.iotaLhs j C), ?_⟩
  show VExpr.mkLams (D.iotaCtx C) (D.iotaLhs j C) = _
  -- `iotaCtx` contains `D.motives`, one entry per type of the block, and `hT` says the block
  -- has at least a `j`-th type.  Proved from `Decl.lean` alone, so this file needs no import
  -- of `Theory.Typing.PatternRules` (where `length_iotaCtx` lives).
  have hne : D.iotaCtx C ≠ [] := by
    have hj : j < D.types.length := (List.getElem?_eq_some_iff.1 hT).1
    have hmot : D.motives ≠ [] := by
      intro h
      have hl : D.motives.length = 0 := by rw [h]; rfl
      simp only [VInductDecl'.motives, List.length_map, List.length_range,
        VInductDecl'.nm] at hl
      omega
    intro h
    simp only [VInductDecl'.iotaCtx, List.append_assoc, List.append_eq_nil_iff] at h
    exact hmot h.2.1
  cases hc : D.iotaCtx C with
  | nil => exact absurd hc hne
  | cons X Xs => rw [VExpr.mkLams]; rfl

def CtorBundle.IsCtor (c : Name) : Prop :=
  ∃ cl, Params.classify c = some cl ∧ cl matches .ctor .. | .etaCtor ..

def CtorBundle.IsCtor.cl (H : CtorBundle.IsCtor c) :
    {cl // Params.classify c = some cl ∧ cl matches .ctor .. | .etaCtor ..} := by
  dsimp [CtorBundle.IsCtor] at H
  match Params.classify c, H with
  | some cl, H => refine ⟨cl, ?_⟩; obtain ⟨_, ⟨⟩, H⟩ := H; exact ⟨rfl, H⟩

/--
The Π-telescope decomposition of a constructor's type, as `IsDefEqStrong.const` consumes it.

**REPAIRED — the old `hu0 : u ≠ .zero` was false and is gone.** `Eq.refl :
∀ {α : Sort u} (a : α), a = a` has sort `imax (u+1) (imax u 0) = 0`, so `u = .zero` for it;
yet `Eq.refl` must be `classify`-ed as a constructor, because `Eq.rec`'s ι-rule
pattern-matches on it and `Pattern.WF` demands a `.ctor` leaf there. So `CtorBundle Eq.refl`
was uninhabited while `IsDefEqStrong.const` demands `∀ cl, CtorBundle c cl` — a *second*,
independent reason that `IsDefEq.strong` was false as stated (the first is the missing
`Ctx.WF`; see `not_strong_of_isDefEq`).

What replaces it is `hrel : rel = true ↔ u ≠ .zero`, which is *not* an extra assumption
chosen to make a proof go through: it is exactly the fact `ParamsExtra.ctor_ty` already
supplies (`rel = true ↔ D.lvl ≠ .zero`), now readable off the head constant because
`Classification.indTy` carries the boolean. `u` is the sort of `rhs`, whose head is `I`
applied to its arguments, and `imax x y = .zero ↔ y = .zero`, so `u ≠ .zero` is exactly the
inductive's result universe being non-`Prop`.

The only consumer, `LE_Interp.build_spine` (`ShapeLogRel.lean`, the `app`/`nil` case), used
`hu0` to force the head's type-shape to `.sort true`; it now takes `.sort rel` and discharges
`decide (u_body ≠ .zero) = rel` from `hrel`.

The `mkPi`/`mkApp` reordering of `rhs` below (to match `VIndCtor.type`) touches the same
lines and should be done with it.
-/
structure CtorBundle (c : Name) (cl : CtorBundle.IsCtor c) : Type where
  I : Name
  Ts : List SExpr
  args : List SExpr
  u : SLevel
  hlen : Ts.length = cl.cl.1.arity
  /-- The inductive's result universe, as recorded by `classify`. -/
  rel : Bool
  hclI : Params.classify I = some (.indTy args.length rel)
  /-- The recorded sort boolean is exactly "the constructor's type is not a proposition".
  Replaces the false `hu0 : u ≠ .zero`; see the structure docstring. -/
  hrel : rel = true ↔ u ≠ .zero
  /-- `rhs` is closed — written out, since `rhs` is defined after this structure.

  Without this `SExpr.IsDefEqStrong` is **not closed under weakening**: `const` carries one
  bundle for *all* contexts, so lifting its equation premise needs
  `((F cl).rhs ls).lift' ρ = (F cl).rhs ls`. `Ts` and `args` come from the declaration and
  really are closed; not saying so made the judgment subtly wrong. -/
  hclosed : ∀ ls, ClosedN (Ts.foldr .forallE (args.foldr (fun A acc => acc.app A)
    (.const I ls))) 0

def CtorBundle.rhs (H : CtorBundle c cl) (ls : List SLevel) : SExpr :=
  H.Ts.foldr .forallE (H.args.foldr (fun A acc => acc.app A) (.const H.I ls))

theorem CtorBundle.rhs_closed (H : CtorBundle c cl) (ls) : (H.rhs ls).ClosedN 0 := H.hclosed ls

section
local notation:65 (priority := high) Γ " ⊢ " e1 " : " A:36 => IsDefEqStrong Γ e1 e1 A
local notation:65 (priority := high) Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong Γ e1 e2 A
inductive IsDefEqStrong : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ A : .sort u → Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ (SExpr.mk ci.type).instL ls : .sort u →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, Γ ⊢ (SExpr.mk ci.type).instL ls ≡ (F cl).rhs ls : .sort (F cl).u) →
    Γ ⊢ .const c ls : (SExpr.mk ci.type).instL ls
  | appDF : Γ ⊢ A : .sort u →
    Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B → A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v → A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' : B.inst e' → Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  | extra : env.defeqs df → ls.length = df.uvars →
    Γ ⊢ .instL ls (.mk df.lhs) : .instL ls (.mk df.type) →
    Γ ⊢ .instL ls (.mk df.rhs) : .instL ls (.mk df.type) →
    Γ ⊢ .instL ls (.mk df.lhs) ≡ .instL ls (.mk df.rhs) : .instL ls (.mk df.type)
end

def Ctx.WF : List SExpr → Prop
  | [] => True
  | A::Γ => WF Γ ∧ ∃ u, Γ ⊢ A : .sort u
scoped notation:65 "⊢ " Γ:36 => Ctx.WF Γ

/-- Reflection of `IsDefEq` into the decorated judgment.

The `Ctx.WF Γ` hypothesis is **necessary**: `not_strong_of_isDefEq` below refutes the
version without it, because `IsDefEqStrong.bvar` demands `Γ ⊢ A : .sort u` for the
looked-up type while `IsDefEq.bvar` says nothing about the context. This mirrors
`hΓ : OnCtx Γ (env.IsType U)` in the `VExpr` analogue `VEnv.IsDefEq.strong`
(`Theory/Typing/Strong.lean`).

The `[ParamsExtra]` hypothesis is **also necessary**, and for an independent reason.
`IsDefEqStrong.const` demands `∀ cl, CtorBundle c cl` for every `c` that `classify` calls a
constructor, and a bundle carries `hclI : classify I = some (.indTy args.length rel)` plus an
equation tying `ci.type` to a telescope headed by `I`. Under `[Params]` alone, `classify` is
unconstrained *relative to `env`*: an instance may declare an arbitrary constant a
constructor -- say `classify c = some (.ctor 0)` with `classify` `none` elsewhere -- and then
no `I` satisfies `hclI`, so `CtorBundle c cl` is uninhabited while `IsDefEq.const` still
derives the undecorated judgment. `ParamsExtra.ctor_ty` is exactly what rules this out.

**This statement is still a `sorry`, but its hypotheses are no longer known-unsatisfiable.**
Three hardwired falsehoods used to sit downstream; all three are repaired:

* `CtorBundle.hu0 : u ≠ .zero` -- false, `CtorBundle Eq.refl` was uninhabited. Now
  `hrel : rel = true ↔ u ≠ .zero` (see the `CtorBundle` docstring above).
* `ParamsExtra.ctor_ty`'s `D.lvl ≠ .zero` -- false for *every* `Prop`-valued inductive
  (`Eq`, `And`, `Or`, `Exists`, `False`), since `D.lvl` is the block's common result universe.
  Now the tie `rel = true ↔ D.lvl ≠ .zero` (see that field's docstring).
* `ParamsExtra.extra_pat` asked for `MatchesS` on the **unpeeled** left-hand side, which no
  rule shape can satisfy. Now λ-peeled, mirroring the mainline `Pat.extra`; the two
  regression tests below pin it.

`ParamsExtra` still has **no instance in the tree**, so `[ParamsExtra]` does not yet make this
theorem true — but it is now an open obligation rather than a vacuous one, and the `Params`
stream is constructing an instance against exactly these fields. The `Ctx.WF Γ` hypothesis is
the fourth repair and is in the statement already; see `not_strong_of_isDefEq`. -/
theorem IsDefEq.strong [ParamsExtra] (hΓ : Ctx.WF Γ) :
    Γ ⊢ e1 ≡ e2 : A → IsDefEqStrong Γ e1 e2 A := sorry

/-- `IsDefEqStrong` has no general reflexivity lemma, because its `trans` carries an extra
`Γ ⊢ A : .sort u` premise. But when the type *is* a sort that premise is discharged by
`sort`, so reflexivity is available exactly there — which is all the `VExpr → SExpr` bridge
needs, since every reflexive fact it must manufacture is a typing. -/
theorem IsDefEqStrong.hasTypeAtSort (H : IsDefEqStrong Γ e1 e2 (.sort u)) :
    IsDefEqStrong Γ e1 e1 (.sort u) := .trans .sort H H.symm

/-- Erasing the decorations of `IsDefEqStrong` gives back `IsDefEq`. The `VExpr` analogue
is `VEnv.IsDefEqStrong.defeq` in `Theory/Typing/Strong.lean`. -/
theorem IsDefEqStrong.defeq (H : IsDefEqStrong Γ e1 e2 A) : Γ ⊢ e1 ≡ e2 : A := by
  induction H with
  | bvar h _ _ => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ _ _ ih1 ih2 => exact .trans ih1 ih2
  | trans' _ _ ih1 ih2 => exact .trans' ih1 ih2
  | sort => exact .sort
  | const h1 h2 => exact .const h1 h2
  | appDF _ _ _ _ _ ih2 ih3 _ => exact .appDF ih2 ih3
  | lamDF _ _ _ _ ih1 _ ih3 _ => exact .lamDF ih1 ih3
  | forallEDF _ _ _ ih1 ih2 _ => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ _ _ ih1 ih2 _ _ => exact .beta ih1 ih2
  | eta _ _ ih1 _ => exact .eta ih1
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 => exact .extra h1 h2

/-- Every bound variable occurring at the head of either side, or of the type, of an
`IsDefEqStrong` judgment is in scope. (`IsDefEq` has no such property: its `bvar` rule has
no premise about the context.) -/
theorem IsDefEqStrong.bvar_lookup (H : IsDefEqStrong Γ e1 e2 A) :
    (∀ i, e1 = .bvar i → ∃ B, Lookup Γ i B) ∧
    (∀ i, e2 = .bvar i → ∃ B, Lookup Γ i B) ∧
    (∀ i, A = .bvar i → ∃ B, Lookup Γ i B) := by
  induction H with
  | bvar h _ ih =>
    exact ⟨fun _ e => by cases e; exact ⟨_, h⟩, fun _ e => by cases e; exact ⟨_, h⟩, ih.1⟩
  | symm _ ih => exact ⟨ih.2.1, ih.1, ih.2.2⟩
  | trans _ _ _ ihA ih1 ih2 => exact ⟨ih1.1, ih2.2.1, ihA.1⟩
  | trans' _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2.1, nofun⟩
  | sort => exact ⟨nofun, nofun, nofun⟩
  | const _ _ _ _ _ ih3 _ => exact ⟨nofun, nofun, ih3.1⟩
  | appDF _ _ _ _ _ _ _ ihB => exact ⟨nofun, nofun, ihB.1⟩
  | lamDF => exact ⟨nofun, nofun, nofun⟩
  | forallEDF => exact ⟨nofun, nofun, nofun⟩
  | defeqDF _ _ ih1 ih2 => exact ⟨ih2.1, ih2.2.1, ih1.2.1⟩
  | beta _ _ _ _ _ _ _ ih4 => exact ⟨nofun, ih4.1, ih4.2.2⟩
  | eta _ _ ih1 _ => exact ⟨nofun, ih1.1, nofun⟩
  | proofIrrel _ _ _ ihp ihh ihh' => exact ⟨ihh.1, ihh'.1, ihp.1⟩
  | extra _ _ _ _ ih3 ih4 => exact ⟨ih3.1, ih4.1, ih3.2.2⟩

/--
**Why `IsDefEq.strong` needs its `Ctx.WF Γ` hypothesis:** without it the statement is false.

`IsDefEqStrong.bvar` demands `Γ ⊢ A : .sort u` for the looked-up type, while `IsDefEq.bvar`
has no premise about the context at all, so an ill-formed context separates the two
judgments. The `VExpr` analogue gets this right — `VEnv.IsDefEq.strong` in
`Theory/Typing/Strong.lean` takes `hΓ : OnCtx Γ (env.IsType U)`.
-/
theorem not_strong_of_isDefEq :
    ¬ ∀ {Γ e1 e2 A}, IsDefEq Γ e1 e2 A → IsDefEqStrong Γ e1 e2 A := fun H => by
  have h : IsDefEq [SExpr.bvar 0] (.bvar 0) (.bvar 0) ((SExpr.bvar 0).lift) := .bvar .zero
  obtain ⟨_, hB⟩ := (H h).bvar_lookup.2.2 1 rfl
  let .succ h' := hB
  nomatch h'

theorem IsDefEq.hasType (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ ⊢ e1 ≡ e1 : A ∧ Γ ⊢ e2 ≡ e2 : A := ⟨H.trans H.symm, H.symm.trans H⟩

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
local notation:65 Γ " ⊢ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

/-- SExpr-side analog of `HasTypeStratified`: a typing derivation indexed by
its tree depth `n`, used for well-founded induction on stratification. -/
inductive HasTypeStratifiedS : List SExpr → SExpr → SExpr → Bool → Nat → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u !! n → Γ ⊢ .bvar i :! A !! n+1
  | sort' : Γ ⊢ .sort l :! .sort (.succ l) !! n
  | const :
    env.constants c = some ci →
    ls.length = ci.uvars →
    Γ ⊢ (mk ci.type).instL ls : .sort u !! n →
    Γ ⊢ .const c ls :! (mk ci.type).instL ls !! n+1
  | app :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    Γ ⊢ f : .forallE A B !! n →
    Γ ⊢ a : A !! n →
    Γ ⊢ B.inst a : .sort v !! n →
    Γ ⊢ .app f a :! B.inst a !! n+1
  | lam :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    A::Γ ⊢ body : B !! n →
    Γ ⊢ .forallE A B : .sort (.imax u v) !! n →
    Γ ⊢ .lam A body :! .forallE A B !! n+1
  | forallE :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ body : .sort v !! n →
    Γ ⊢ .forallE A body :! .sort (.imax u v) !! n+1
  | base : Γ ⊢ e :! A !! n → Γ ⊢ e : A !! n
  | defeq : Γ ⊢ A ≡ B : .sort u →
    Γ ⊢ A : .sort u !! n → Γ ⊢ B : .sort u !! n →
    Γ ⊢ e : A !! n → Γ ⊢ e : B !! n+1
end

scoped notation:65 Γ " ⊢ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
scoped notation:65 Γ " ⊢ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

theorem HasTypeStratifiedS.to_core (H : Γ ⊢ e : A !! n) :
    ∃ A', Γ ⊢ e :! A' !! n := sorry

theorem HasTypeStratifiedS.isType (H : HasTypeStratifiedS Γ e A b n) :
    ∃ u, Γ ⊢ A : .sort u !! n - 1 := sorry

theorem IsDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h => refine .bvar (h.weak' W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | const h1 h2 => rw [(henv.closedC h1).mkS.instL.lift'_eq .zero]; exact .const h1 h2
  | appDF _ _ ih1 ih2 => exact SExpr.lift'_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.cons)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    rw [SExpr.lift'_inst_hi, SExpr.lift'_inst_hi]
    exact .beta (ih1 W.cons) (ih2 W)
  | eta _ ih => refine cast ?_ (IsDefEq.eta (ih W)); congr 1; simp [← SExpr.lift'_comp]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [hA1.mkS.instL.lift'_eq .zero, hA2.mkS.instL.lift'_eq .zero, hA3.mkS.instL.lift'_eq .zero]
    exact .extra h1 h2

/-- Weakening for the decorated judgment. Needs `CtorBundle.hclosed`: `const` carries one
bundle for *all* contexts, so lifting its equation premise requires the bundle's `rhs` to be
closed. -/
theorem IsDefEqStrong.weak' (W : Ctx.Lift' ρ Γ Γ') (H : IsDefEqStrong Γ e1 e2 A) :
    IsDefEqStrong Γ' (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ) := by
  induction H generalizing ρ Γ' with
  | bvar h _ ihA => exact .bvar (h.weak' W) (ihA W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ _ ihA ih1 ih2 => exact .trans (ihA W) (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | const h1 h2 _ F _ ihT ihFeq =>
    have hT := ihT W
    rw [ClosedN.lift'_eq (henv.closedC h1).mkS.instL .zero] at hT ⊢
    refine .const h1 h2 hT F fun cl => ?_
    have h := ihFeq cl W
    rwa [ClosedN.lift'_eq (henv.closedC h1).mkS.instL .zero,
      ClosedN.lift'_eq ((F cl).rhs_closed _) .zero] at h
  | appDF _ _ _ _ ihA ihf iha ihBa =>
    have hBa := ihBa W
    simp only [SExpr.lift', SExpr.lift'_inst_hi] at hBa ⊢
    exact .appDF (ihA W) (ihf W) (iha W) hBa
  | lamDF _ _ _ _ ihA ihB ihb ihb' =>
    exact .lamDF (ihA W) (ihB W.cons) (ihb W.cons) (ihb' W.cons)
  | forallEDF _ _ _ ihA ihb ihb' => exact .forallEDF (ihA W) (ihb W.cons) (ihb' W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ _ _ ih1 ih2 ih3 ih4 =>
    have h3 := ih3 W; have h4 := ih4 W
    simp only [SExpr.lift', SExpr.lift'_inst_hi] at h3 h4 ⊢
    exact .beta (ih1 W.cons) (ih2 W) h3 h4
  | @eta _ e A B _ _ ih1 ih2 =>
    have eq : (SExpr.lam A (.app e.lift (.bvar 0))).lift' ρ
        = .lam (A.lift' ρ) (.app ((e.lift' ρ).lift) (.bvar 0)) := by
      simp only [SExpr.lift']; congr 1; simp [← SExpr.lift'_comp]
    have h2 := ih2 W
    rw [eq] at h2 ⊢
    exact .eta (ih1 W) h2
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 _ _ ih3 ih4 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    have i3 := ih3 W; have i4 := ih4 W
    rw [ClosedN.lift'_eq hA1.mkS.instL .zero, ClosedN.lift'_eq hA3.mkS.instL .zero] at i3
    rw [ClosedN.lift'_eq hA2.mkS.instL .zero, ClosedN.lift'_eq hA3.mkS.instL .zero] at i4
    rw [ClosedN.lift'_eq hA1.mkS.instL .zero, ClosedN.lift'_eq hA2.mkS.instL .zero,
      ClosedN.lift'_eq hA3.mkS.instL .zero]
    exact .extra h1 h2 i3 i4

/-- Every context is reachable from the empty one by a lift. `Ctx.Lift'.skip` carries no
typing side condition, so this is pure list recursion. -/
theorem Ctx.Lift'.nil : ∀ Γ : List SExpr, ∃ ρ, Ctx.Lift' ρ [] Γ
  | [] => ⟨.refl, .refl⟩
  | _::Γ => let ⟨_, h⟩ := Ctx.Lift'.nil Γ; ⟨_, h.skip⟩

/-- A judgment about closed terms holds in every context. `VEnv.IsDefEqStrong.extra` types
`df.type.instL ls` only at `[]`, but the `VExpr → SExpr` bridge needs it at `Γ`. -/
theorem IsDefEqStrong.closed_weak {Γ : List SExpr} {e1 e2 A : SExpr}
    (h1 : e1.ClosedN 0) (h2 : e2.ClosedN 0) (hA : A.ClosedN 0)
    (H : IsDefEqStrong [] e1 e2 A) : IsDefEqStrong Γ e1 e2 A := by
  obtain ⟨ρ, hρ⟩ := Ctx.Lift'.nil Γ
  have := H.weak' hρ
  rwa [h1.lift'_eq .zero, h2.lift'_eq .zero, hA.lift'_eq .zero] at this

variable (HasType : List SExpr → SExpr → SExpr → Prop)
inductive Ctx.Subst (Γ : List SExpr) : SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.Subst Γ σ []
  | cons : Ctx.Subst Γ σ.tail Δ → HasType Γ σ.head (A.subst σ.tail) → Ctx.Subst Γ σ (A::Δ)

variable {HasType}
theorem Ctx.Subst.head (H : Ctx.Subst HasType Γ σ (A::Δ)) : HasType Γ σ.head (A.subst σ.tail) :=
  let .cons _ H := H; H

theorem Ctx.Subst.tail (H : Ctx.Subst HasType Γ σ (A::Δ)) : Ctx.Subst HasType Γ σ.tail Δ :=
  let .cons H _ := H; H

theorem Ctx.Subst.cons' (H1 : Ctx.Subst HasType Γ σ Δ) (H2 : HasType Γ e (A.subst σ)) :
    Ctx.Subst HasType Γ (σ.cons e) (A::Δ) := .cons H1 H2

theorem Ctx.Subst.lift_r (H1 : Ctx.Subst HasType Θ σ Γ) (H2 : Ctx.Lift' ρ Θ Δ) :
    Ctx.Subst HasType Δ (σ.lift_r ρ) Γ := sorry

theorem Ctx.Subst.lift (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A)
    (H : Ctx.Subst HasType Γ σ Δ) : Ctx.Subst HasType (A.subst σ :: Γ) σ.lift (A :: Δ) := by
  have : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i; simp [SExpr.Subst.tail, SExpr.Subst.lift, SExpr.Subst.lift_r]
  refine .cons (this ▸ .lift_r H .one) (this ▸ bvar ?_)
  rw [← lift'_subst, ← SExpr.lift]; exact .zero

theorem Ctx.Subst.id : Ctx.Subst HasType Γ .id Γ := sorry
theorem Ctx.Subst.one (H : HasType Γ e A) : Ctx.Subst HasType Γ (.one e) (A::Γ) :=
  .cons .id (by simpa)

/-- Weakening the *target* context of a typing substitution. This is `Ctx.Subst.lift_r`
specialised to `HasType := (· ⊢ · : ·)`, which is what makes it provable: the generic
version cannot be, since an arbitrary `HasType` need not be closed under weakening. -/
theorem Ctx.Subst.wk (W : Ctx.Lift' ρ Γ₀ Γ₁) :
    ∀ {σ Γ}, Ctx.Subst (· ⊢ · : ·) Γ₀ σ Γ → Ctx.Subst (· ⊢ · : ·) Γ₁ (σ.lift_r ρ) Γ := by
  intro σ Γ H
  induction H with
  | nil => exact .nil
  | cons _ ht ih => exact .cons ih (lift'_subst ▸ ht.weak' W)

theorem Ctx.Subst.lookupS {Γ₀ : List SExpr} : ∀ {Γ i A}, Lookup Γ i A →
    ∀ {σ}, Ctx.Subst (· ⊢ · : ·) Γ₀ σ Γ → Γ₀ ⊢ σ i : A.subst σ := by
  intro Γ i A h
  induction h with
  | zero => intro σ H; let .cons _ ht := H; rw [lift_subst]; exact ht
  | succ _ ih => intro σ H; let .cons H' _ := H; rw [lift_subst]; exact ih H'

theorem Ctx.Subst.liftS (H : Ctx.Subst (· ⊢ · : ·) Γ σ Δ) :
    Ctx.Subst (· ⊢ · : ·) (A.subst σ :: Γ) σ.lift (A :: Δ) := by
  refine .cons (Ctx.Subst.wk (.skip .refl) H) ?_
  show (A.subst σ :: Γ) ⊢ SExpr.bvar 0 : A.subst (σ.lift_r (.skip .refl))
  rw [← lift'_subst]; exact .bvar .zero

/-- The identity substitution, at `HasType := (· ⊢ · : ·)`. The generic `Ctx.Subst.id`
cannot be proved, since an arbitrary `HasType` need not contain the variable rule. -/
theorem Ctx.Subst.idS : ∀ {Γ : List SExpr}, Ctx.Subst (· ⊢ · : ·) Γ .id Γ
  | [] => .nil
  | A::Γ => by
    have := Ctx.Subst.liftS (A := A) (idS (Γ := Γ))
    rwa [subst_id, id_lift] at this

/-- Substitution by a *single* well-typed substitution. Unlike the two-substitution
`IsDefEq.subst` this needs nothing beyond `IsDefEq` itself: the `appDF` rule's conclusion
type mentions only the first argument, so no type-level congruence is required. -/
theorem IsDefEq.substL (H : Γ ⊢ e1 ≡ e2 : A) :
    ∀ {Γ₀ σ}, Ctx.Subst (· ⊢ · : ·) Γ₀ σ Γ → Γ₀ ⊢ e1.subst σ ≡ e2.subst σ : A.subst σ := by
  induction H with intro Γ₀ σ W
  | bvar h => exact Ctx.Subst.lookupS h W
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | const h1 h2 => rw [(henv.closedC h1).mkS.instL.subst_eq .zero]; exact .const h1 h2
  | appDF _ _ ih1 ih2 => rw [subst_inst]; exact .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.liftS)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.liftS)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 => rw [subst_inst, subst_inst]; exact .beta (ih1 W.liftS) (ih2 W)
  | eta _ ih =>
    refine cast ?_ (IsDefEq.eta (ih W)); congr 2
    exact congrArg (SExpr.app · (.bvar 0)) (lift'_subst.trans (lift_subst (σ := σ.lift)).symm)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [hA1.mkS.instL.subst_eq .zero, hA2.mkS.instL.subst_eq .zero,
      hA3.mkS.instL.subst_eq .zero]
    exact .extra h1 h2

/--
Simultaneous substitutions relating two contexts.

`Γ₀` is an **index**, not a parameter, so that the `weak` constructor can change it. Without
`weak` the relation cannot express a weakened substitution at all — `nil` pins both
substitutions to the identity at the base — and `Ctx.SubstEq.lift` is then unprovable,
because proving `Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ'.lift (A :: Γ)` requires peeling
with `cons` down to `Ctx.SubstEq (A.subst σ :: Γ₀) _ _ Γ₀`, whose only constructor would
demand `Γ₀ = A.subst σ :: Γ₀`.
-/
inductive Ctx.SubstEq : List SExpr → SExpr.Subst → SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.SubstEq Γ₀ .id .id Γ₀
  | cons : Ctx.SubstEq Γ₀ σ.tail σ'.tail Γ →
    Γ ⊢ A : .sort u →
    Γ₀ ⊢ σ.head ≡ σ'.head : A.subst σ.tail →
    Ctx.SubstEq Γ₀ σ σ' (A :: Γ)
  | weak : Ctx.SubstEq Γ₀ σ σ' Γ → Ctx.Lift' ρ Γ₀ Γ₁ →
    Ctx.SubstEq Γ₁ (σ.lift_r ρ) (σ'.lift_r ρ) Γ

theorem Ctx.SubstEq.left (W : Ctx.SubstEq Γ₀ σ σ' Γ) : Ctx.Subst (· ⊢ · : ·) Γ₀ σ Γ := by
  induction W with
  | nil => exact .idS
  | cons _ _ h ih => exact .cons ih h.hasType.1
  | weak _ W' ih => exact Ctx.Subst.wk W' ih

theorem Ctx.SubstEq.lookup (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    ∀ {i A}, Lookup Γ i A → Γ₀ ⊢ σ i ≡ σ' i : A.subst σ := by
  induction W with
  | nil => intro _ _ h; rw [subst_id]; exact .bvar h
  | cons _ _ hh ih =>
    intro _ _ h
    cases h with
    | zero => rw [lift_subst]; exact hh
    | succ h => rw [lift_subst]; exact ih h
  | weak _ W' ih => intro _ _ h; exact lift'_subst ▸ (ih h).weak' W'

theorem Ctx.SubstEq.lift (W : Ctx.SubstEq Γ₀ σ σ' Γ) (hA : Γ ⊢ A : .sort u) :
    Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ'.lift (A :: Γ) := by
  refine .cons (W.weak (.skip .refl)) hA ?_
  show (A.subst σ :: Γ₀) ⊢ SExpr.bvar 0 ≡ SExpr.bvar 0 : A.subst (σ.lift_r (.skip .refl))
  rw [← lift'_subst]
  exact .bvar .zero


/--
Congruence of a term in the substitution: the two endpoints and the type, all three at
once.

This runs on `IsDefEqStrong` rather than `IsDefEq`. The `symm` case needs the type-level
congruence, `defeqDF` and `trans'` need to retype, `appDF` needs its
`B.inst a ≡ B.inst a'` premise, and `lamDF` needs `A::Γ ⊢ B : .sort v` to rebuild the
`forallE` conversion. Plain `IsDefEq` supplies none of these, and re-deriving them would
need an `isType` lemma that `SExpr` does not have.
-/
theorem IsDefEqStrong.substCong (H : IsDefEqStrong Γ e1 e2 A) :
    ∀ {Γ₀ σ σ'}, Ctx.SubstEq Γ₀ σ σ' Γ →
      (Γ₀ ⊢ e1.subst σ ≡ e1.subst σ' : A.subst σ) ∧
      (Γ₀ ⊢ e2.subst σ ≡ e2.subst σ' : A.subst σ) ∧
      ∃ u, Γ₀ ⊢ A.subst σ ≡ A.subst σ' : .sort u := by
  induction H with intro Γ₀ σ σ' W
  | bvar h _ ihA => exact ⟨W.lookup h, W.lookup h, _, (ihA W).1⟩
  | symm _ ih => exact ⟨(ih W).2.1, (ih W).1, (ih W).2.2⟩
  | trans _ _ _ ihA ih1 ih2 => exact ⟨(ih1 W).1, (ih2 W).2.1, _, (ihA W).1⟩
  | trans' h1 h2 ih1 ih2 =>
    exact ⟨(ih1 W).1,
      ((h1.defeq.trans' h2.defeq).hasType.2.substL W.left).trans' (ih2 W).2.1, _, .sort⟩
  | sort => exact ⟨.sort, .sort, _, .sort⟩
  | const h1 h2 _ _ _ ih3 _ =>
    refine ⟨?_, ?_, _, (ih3 W).1⟩ <;>
      (rw [(henv.closedC h1).mkS.instL.subst_eq .zero]; exact .const h1 h2)
  | appDF _ _ _ hBa _ ihf iha ihBa =>
    refine ⟨?_, ?_, _, (ihBa W).1⟩
    · rw [subst_inst]; exact .appDF (ihf W).1 (iha W).1
    · refine (hBa.defeq.substL W.left).symm.defeqDF ?_
      rw [subst_inst]; exact .appDF (ihf W).2.1 (iha W).2.1
  | lamDF hA hB _ _ ihA ihB ihbody ihbody' =>
    have hA1 := hA.defeq.hasType.1
    have hA2 := hA.defeq.hasType.2
    refine ⟨.lamDF (ihA W).1 (ihbody (W.lift hA1)).1, ?_, _,
      .forallEDF (ihA W).1 (ihB (W.lift hA1)).1⟩
    exact ((hA.defeq.forallEDF hB.defeq).substL W.left).symm.defeqDF
      (.lamDF (ihA W).2.1 (ihbody' (W.lift hA2)).2.1)
  | forallEDF hA _ _ ihA ihbody ihbody' =>
    have hA1 := hA.defeq.hasType.1
    have hA2 := hA.defeq.hasType.2
    exact ⟨.forallEDF (ihA W).1 (ihbody (W.lift hA1)).1,
      .forallEDF (ihA W).2.1 (ihbody' (W.lift hA2)).2.1, _, .sort⟩
  | defeqDF hAB _ ihAB ih =>
    have sAB := hAB.defeq.substL W.left
    exact ⟨sAB.defeqDF (ih W).1, sAB.defeqDF (ih W).2.1, _, (ihAB W).2.1⟩
  | beta _ _ _ _ _ _ ih3 ih4 => exact ⟨(ih3 W).1, (ih4 W).1, (ih3 W).2.2⟩
  | eta _ _ ih1 ih2 => exact ⟨(ih2 W).1, (ih1 W).1, (ih2 W).2.2⟩
  | proofIrrel _ _ _ _ ih2 ih3 => exact ⟨(ih2 W).1, (ih3 W).1, (ih2 W).2.2⟩
  | extra _ _ _ _ ih3 ih4 => exact ⟨(ih3 W).1, (ih4 W).1, (ih3 W).2.2⟩

/-- Substitution by a pair of definitionally equal substitutions. -/
theorem IsDefEqStrong.subst (W : Ctx.SubstEq Γ₀ σ σ' Γ) (H : IsDefEqStrong Γ e1 e2 A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ :=
  (H.defeq.substL W.left).trans (H.substCong W).2.1

/-- Substitution for the undecorated judgment. The `Ctx.WF Γ` hypothesis comes from
`IsDefEq.strong`; see `not_strong_of_isDefEq` for why it is unavoidable. -/
theorem IsDefEq.subst [ParamsExtra] (hΓ : Ctx.WF Γ) (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (H : Γ ⊢ e1 ≡ e2 : A) : Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ :=
  (H.strong hΓ).subst W

theorem Ctx.SubstEq.symm [ParamsExtra] (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Ctx.WF Γ → Ctx.SubstEq Γ₀ σ' σ Γ := by
  induction W with
  | nil => exact fun _ => .nil
  | cons W hA h ih =>
    exact fun hΓ => .cons (ih hΓ.1) hA (.defeqDF (.subst hΓ.1 W hA) h.symm)
  | weak _ W' ih => exact fun hΓ => .weak (ih hΓ) W'

/--
Structural context conversion: `Γ` and `Γ'` agree except at one entry, where the two types
are definitionally equal sorts.

The prefix entries are demanded **identical**, not merely defeq. That is what lets
`IsDefEq.convCtx` avoid a well-formedness hypothesis: routing this through `Ctx.SubstEq`
instead would hit `Ctx.SubstEq.cons`'s `Γ ⊢ A : .sort u` premise at *every* prefix entry,
and `IsDefEq.defeqDF_l'` carries no `Ctx.WF` to discharge it. `IsDefEqCtx` below is the
defeq-at-every-level version, and is derived from this one rather than the other way round.
-/
inductive Ctx.Conv : List SExpr → List SExpr → Prop where
  | here : Γ ⊢ A ≡ A' : .sort u → Ctx.Conv (A::Γ) (A'::Γ)
  | cons : Ctx.Conv Γ Γ' → Ctx.Conv (B::Γ) (B::Γ')

theorem Ctx.Conv.lookup (W : Ctx.Conv Γ Γ') (H : Lookup Γ i A) : Γ' ⊢ .bvar i : A := by
  induction W generalizing i A with
  | @here _ _ A' _ h =>
    cases H with
    | zero => exact .defeqDF (h.weak' (.one (A := A'))).symm (.bvar .zero)
    | succ h' => exact .bvar (.succ h')
  | cons _ ih =>
    cases H with
    | zero => exact .bvar .zero
    | succ h' => exact (ih h').weak' .one

theorem IsDefEq.convCtx (W : Ctx.Conv Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) : Γ' ⊢ e1 ≡ e2 : A := by
  induction H generalizing Γ' with
  | bvar h => exact W.lookup h
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | const h1 h2 => exact .const h1 h2
  | appDF _ _ ih1 ih2 => exact .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.cons)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 => exact .beta (ih1 W.cons) (ih2 W)
  | eta _ ih => exact .eta (ih W)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 => exact .extra h1 h2

theorem Ctx.Conv.append (h : Γ ⊢ A ≡ A' : .sort u) :
    ∀ Δ : List SExpr, Ctx.Conv (Δ ++ A::Γ) (Δ ++ A'::Γ)
  | [] => .here h
  | _::Δ => (Ctx.Conv.append h Δ).cons

theorem IsDefEq.defeqDF_l' (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : Δ++A::Γ ⊢ e1 ≡ e2 : B) : Δ++A'::Γ ⊢ e1 ≡ e2 : B :=
  h2.convCtx (Ctx.Conv.append h1 Δ)

theorem IsDefEq.defeqDF_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e1 ≡ e2 : B) : A'::Γ ⊢ e1 ≡ e2 : B :=
  .defeqDF_l' (Δ := []) h1 h2

theorem HasType.defeq_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e : B) : A'::Γ ⊢ e : B := h1.defeqDF_l h2

variable (DefEq : List SExpr → SExpr → SExpr → SExpr → Prop) in
structure WithLift (Γ : List SExpr) (e1 e2 A : SExpr) : Prop where
  defeq' {{Δ ρ e1' e2' A'}} : Ctx.Lift' ρ Δ Γ →
    e1 = .lift' e1' ρ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e1' e2' A'
  left' {{Δ ρ e1' A'}} : Ctx.Lift' ρ Δ Γ → e1 = .lift' e1' ρ → A = .lift' A' ρ → DefEq Δ e1' e1' A'
  right' {{Δ ρ e2' A'}} : Ctx.Lift' ρ Δ Γ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e2' e2' A'

def IsDefEqLift := WithLift IsDefEq
scoped notation:65 Γ " ⊢ " e " :↑ " A:36 => IsDefEqLift Γ e e A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " :↑ " A:36 => IsDefEqLift Γ e1 e2 A

theorem WithLift.imp
    (imp : ∀ {Γ e1 e2 A}, DefEq Γ e1 e2 A → DefEq' Γ e1 e2 A)
    (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq' Γ e1 e2 A where
  defeq' _ _ _ _ _ W' h1 h2 h3 := imp (H.defeq' W' h1 h2 h3)
  left' _ _ _ _ W' h1 hA := imp (H.left' W' h1 hA)
  right' _ _ _ _ W' h1 hA := imp (H.right' W' h1 hA)

theorem WithLift.refl
    (refl : ∀ {ρ Δ e' A'}, Ctx.Lift' ρ Δ Γ →
      e = .lift' e' ρ → A = .lift' A' ρ → DefEq Δ e' e' A')
    : WithLift DefEq Γ e e A where
  defeq' _ _ _ _ _ W := by rintro rfl he rfl; cases SExpr.lift'_inj.1 he; exact refl W rfl rfl
  left' _ _ _ _ W := by rintro rfl rfl; exact refl W rfl rfl
  right' _ _ _ _ W := by rintro rfl rfl; exact refl W rfl rfl

theorem WithLift.weak'
    (weak : ∀ {ρ Γ Δ e1 e2 A}, Ctx.Lift' ρ Γ Δ → DefEq Γ e1 e2 A →
      DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ))
    (W : Ctx.Lift' ρ Γ Δ) (H : WithLift DefEq Γ e1 e2 A) :
    WithLift DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ) where
  defeq' Δ' ρ' e1' e2' A' W' h1 h2 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨e2, rfl, rfl⟩ := lift_eq_lift h2
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.defeq' I.symm.diff rfl rfl rfl)
  left' Δ' ρ' e1' A' W' h1 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.left' I.symm.diff rfl rfl)
  right' Δ' ρ' e1' A' W' h1 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.right' I.symm.diff rfl rfl)

theorem IsDefEqLift.weak' : Ctx.Lift' ρ Γ Δ → Γ ⊢ e1 ≡ e2 :↑ A →
    Δ ⊢ e1.lift' ρ ≡ e2.lift' ρ :↑ A.lift' ρ := WithLift.weak' IsDefEq.weak'

theorem IsDefEqLift.subst : Ctx.Subst HasType Δ σ Γ → Γ ⊢ e1 ≡ e2 :↑ A →
    Δ ⊢ e1.subst σ ≡ e2.subst σ :↑ A.subst σ := sorry

theorem WithLift.weak'_inv (W : Ctx.Lift' ρ Γ Δ)
    (H : WithLift DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ)) : WithLift DefEq Γ e1 e2 A where
  defeq' Δ' ρ' _ _ _ W' := by
    rintro rfl rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.defeq' (W'.comp W) rfl rfl rfl
  left' Δ' ρ' _ _ W' := by
    rintro rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.left' (W'.comp W) rfl rfl
  right' Δ' ρ' _ _ W' := by
    rintro rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.right' (W'.comp W) rfl rfl

nonrec theorem IsDefEqLift.weak'_inv : Ctx.Lift' ρ Γ Δ →
    Δ ⊢ e1.lift' ρ ≡ e2.lift' ρ :↑ A.lift' ρ → Γ ⊢ e1 ≡ e2 :↑ A := .weak'_inv

theorem WithLift.symm
    (symm : ∀ {Γ e1 e2 A}, DefEq Γ e1 e2 A → DefEq Γ e2 e1 A)
    (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e2 e1 A where
  defeq' _ _ _ _ _ W' h1 h2 h3 := symm (H.defeq' W' h2 h1 h3)
  left' _ _ _ _ W' h1 hA := H.right' W' h1 hA
  right' _ _ _ _ W' h1 hA := H.left' W' h1 hA

nonrec theorem IsDefEqLift.symm : Γ ⊢ e1 ≡ e2 :↑ A → Γ ⊢ e2 ≡ e1 :↑ A := .symm .symm

theorem WithLift.left (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e1 e1 A :=
  .refl (H.left' ·)

theorem WithLift.right (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e2 e2 A :=
  .refl (H.right' ·)

theorem IsDefEqLift.left (H : Γ ⊢ e1 ≡ e2 :↑ A) : Γ ⊢ e1 :↑ A where
  defeq' _ _ _ _ _ W' := by rintro rfl he hA; exact SExpr.lift'_inj.1 he ▸ H.left' W' rfl hA
  left' := H.left'
  right' := H.left'

theorem WithLift.defeq (H : WithLift DefEq Γ e1 e2 A) : DefEq Γ e1 e2 A :=
  H.defeq' .refl SExpr.lift'_refl.symm SExpr.lift'_refl.symm SExpr.lift'_refl.symm

nonrec theorem IsDefEqLift.defeq (H : Γ ⊢ e1 ≡ e2 :↑ A) : Γ ⊢ e1 ≡ e2 : A := H.defeq

variable (Γ₀ : List SExpr) in
inductive IsDefEqCtx : List SExpr → List SExpr → Prop
  | zero : IsDefEqCtx Γ₀ Γ₀
  | succ :  IsDefEqCtx Γ₁ Γ₂ → Γ₁ ⊢ A₁ ≡ A₂ : .sort u → IsDefEqCtx (A₁ :: Γ₁) (A₂ :: Γ₂)

theorem IsDefEq.defeqDFC' (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Δ ++ Γ₁ ⊢ e₁ ≡ e₂ : A) : Δ ++ Γ₂ ⊢ e₁ ≡ e₂ : A := by
  induction h1 generalizing e₁ e₂ A Δ with
  | zero => exact h2
  | @succ _ _ _ A₂ _ _ AA ih =>
    simpa using ih (Δ := Δ ++ [A₂]) (by simpa using AA.defeqDF_l' h2)

theorem IsDefEq.defeqDFC (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Γ₁ ⊢ e₁ ≡ e₂ : A) : Γ₂ ⊢ e₁ ≡ e₂ : A := .defeqDFC' (Δ := []) h1 h2

scoped notation:65 Γ " ⊢ " e1 " ⤳ " e2:36 => WHRed Γ e1 e2
inductive WHRed (Γ : List SExpr) : SExpr → SExpr → Prop where
  | app : Γ ⊢ f ⤳ f' → Γ ⊢ .app f a ⤳ .app f' a
  | beta : Γ ⊢ .app (.lam A e) a ⤳ e.inst a
  | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
    (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) → Γ ⊢ e ⤳ r.1.applyS m1 m2

theorem WHRed.subst (W : Ctx.Subst HasType Δ σ Γ) :
    Γ ⊢ e1 ⤳ e2 → Δ ⊢ e1.subst σ ⤳ e2.subst σ
  | .app h1 => .app (h1.subst W)
  | .beta => subst_inst ▸ .beta
  | .extra h1 h2 h3 h4 => sorry

theorem WHRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ⤳ e2 → Γ' ⊢ e1.lift' ρ ⤳ e2.lift' ρ
  | .app h1 => .app (h1.weak' W)
  | .beta => by rw [SExpr.lift'_inst_hi]; exact .beta
  | .extra h1 h2 h3 h4 => sorry

theorem WHRed.weakU_inv (W : Ctx.Lift' ρ Γ Γ') (H : Γ' ⊢ e1.lift' ρ ⤳ e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳ e2 := by
  generalize he : e1.lift' ρ = e1' at H
  induction H generalizing e1 with
  | app h1 ih => let .app .. := e1; cases he; obtain ⟨_, rfl, a1⟩ := ih rfl; exact ⟨_, rfl, .app a1⟩
  | beta =>
    let .app e1 _ := e1; let .lam .. := e1; cases he
    simp [← SExpr.lift'_inst_hi, SExpr.lift'_inj]; exact .beta
  | extra => sorry

def WHNF (Γ : List SExpr) (e : SExpr) := ∀ e', ¬Γ ⊢ e ⤳ e'

theorem WHNF.lam : WHNF Γ (.lam A e) := nofun
theorem WHNF.sort : WHNF Γ (.sort A) := nofun
theorem WHNF.forallE : WHNF Γ (.forallE A B) := nofun

theorem _root_.Lean4Lean.Subpattern.ne_var_l {qf p : Pattern}
    (h : Subpattern (.var qf) p) : qf ≠ p := by
  rintro rfl; have := h.sizeOf_le; simp at this; omega

theorem _root_.Lean4Lean.Subpattern.ne_app_l {qf qa p : Pattern}
    (h : Subpattern (.app qf qa) p) : qf ≠ p := by
  rintro rfl; have := h.sizeOf_le; simp at this; omega

/--
A term matched by a **proper** sub-pattern of a registered pattern is in weak-head normal
form.

The spine of a matched term bottoms out at a `const`, so the only way it could reduce is
by `extra` — and then two registered patterns would match the same term, so `pat_uniq`
forces the sub-pattern to *be* the whole pattern, contradicting properness.

This needs **only** `pat_uniq`. The `pat_app_l` / `pat_app_l_uniq` / `pat_app_uniq` family
exists to compare two patterns' *function spines*; comparing the registered pattern against
its own sub-pattern instead is strictly shorter and needs none of them. Please do not
reintroduce the longer route.
-/
theorem WHRed.not_of_matchesS {p : Pattern} {r} (hp : Params.Pat p r) :
    ∀ {q : Pattern} {e : SExpr} {m1 m2}, q.MatchesS e m1 m2 →
      Subpattern q p → q ≠ p → ∀ {Γ : List SExpr} {e' : SExpr}, ¬ WHRed Γ e e' := by
  intro q e m1 m2 hq
  induction hq with
  | @const c ls =>
    intro hsub hne _ _ H
    let .extra a1 r2 _ _ := H
    have ⟨_, hi⟩ := Pattern.MatchesS.inter_exists (.const (c := c) (ls := ls)) r2
    rw [Pattern.inter_comm] at hi
    obtain ⟨e1, e2, -⟩ := Params.pat_uniq hp a1 hsub hi
    exact hne (e1.trans e2).symm
  | @var qf f' f1 g1 a' hf ih =>
    intro hsub hne _ _ H
    cases H with
    | app h1 => exact ih (.trans (.varL .refl) hsub) hsub.ne_var_l h1
    | beta => exact hf.not_lam
    | extra a1 r2 _ _ =>
      have ⟨_, hi⟩ := Pattern.MatchesS.inter_exists (hf.var (a' := a')) r2
      rw [Pattern.inter_comm] at hi
      obtain ⟨e1, e2, -⟩ := Params.pat_uniq hp a1 hsub hi
      exact hne (e1.trans e2).symm
  | @app qf f' f1 g1 qa a' f2 g2 hf ha ihf _ =>
    intro hsub hne _ _ H
    cases H with
    | app h1 => exact ihf (.trans (.appL .refl) hsub) hsub.ne_app_l h1
    | beta => exact hf.not_lam
    | extra a1 r2 _ _ =>
      have ⟨_, hi⟩ := Pattern.MatchesS.inter_exists (hf.app ha) r2
      rw [Pattern.inter_comm] at hi
      obtain ⟨e1, e2, -⟩ := Params.pat_uniq hp a1 hsub hi
      exact hne (e1.trans e2).symm

theorem WHRed.determ (H1 : Γ ⊢ e ⤳ e₁) (H2 : Γ ⊢ e ⤳ e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | app l1 ih =>
    cases H2 with
    | app r1 => cases ih r1; rfl
    | beta => cases WHNF.lam _ l1
    | extra a1 r2 _ _ =>
      cases r2 with
      | var hf => exact (WHRed.not_of_matchesS a1 hf (.varL .refl) (Subpattern.ne_var_l .refl) l1).elim
      | app hf _ =>
        exact (WHRed.not_of_matchesS a1 hf (.appL .refl) (Subpattern.ne_app_l .refl) l1).elim
  | beta =>
    cases H2 with
    | app r1 => cases WHNF.lam _ r1
    | beta => rfl
    | extra _ r2 => cases r2 with
      | var hf => exact hf.not_lam.elim
      | app hf _ => exact hf.not_lam.elim
  | extra a1 l2 _ _ =>
    cases H2 with
    | beta => cases l2 with
      | var hf => exact hf.not_lam.elim
      | app hf _ => exact hf.not_lam.elim
    | app r1 =>
      cases l2 with
      | var hf => exact (WHRed.not_of_matchesS a1 hf (.varL .refl) (Subpattern.ne_var_l .refl) r1).elim
      | app hf _ =>
        exact (WHRed.not_of_matchesS a1 hf (.appL .refl) (Subpattern.ne_app_l .refl) r1).elim
    | extra a1' r2 _ _ =>
      have ⟨_, hi⟩ := l2.inter_exists r2
      rw [Pattern.inter_comm] at hi
      obtain ⟨rfl, -, hr⟩ := Params.pat_uniq a1 a1' .refl hi
      cases hr
      obtain ⟨rfl, rfl⟩ := l2.determ r2
      rfl

def WHRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (WHRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ⤳* " e2:36 => WHRedS Γ e1 e2

theorem WHRedS.subst (W : Ctx.Subst HasType Δ σ Γ) (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.subst σ ⤳* e2.subst σ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.subst W)

theorem WHRedS.defeq (H : Γ ⊢ e1 ⤳* e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e1 ≡ e2 : A := sorry

theorem WHRedS.weak' (W : Ctx.Lift' ρ Γ Δ) (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.lift' ρ ⤳* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

theorem WHRedS.app (H : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1.app a ⤳* e2.app a := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.app

theorem WHRedS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e1.lift' ρ ⤳* e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳* e2 := by
  induction H with
  | rfl => exact ⟨_, rfl, .rfl⟩
  | tail _ h2 ih =>
    obtain ⟨_, rfl, a1⟩ := ih
    obtain ⟨_, rfl, a2⟩ := h2.weakU_inv W
    exact ⟨_, rfl, .tail a1 a2⟩

theorem WHRedS.determ_l (H1 : Γ ⊢ e ⤳* e₁) (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : Γ ⊢ e₁ ⤳* e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl => exact H2
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem WHNF.whRedS (W : WHNF Γ e) (H : Γ ⊢ e ⤳* e') : e = e' := by
  cases H using ReflTransGen.headIndOn with
  | rfl => rfl
  | head h1 => cases W _ h1

theorem WHRedS.determ
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := W1.whRedS (H1.determ_l H2 W2)

scoped notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
inductive ParRed : List SExpr → SExpr → SExpr → Prop where
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
    (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.applyS m1 m2'

theorem ParRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫ e2 → Γ' ⊢ e1.lift' ρ ≫ e2.lift' ρ
  | .bvar => .bvar
  | .sort => .sort
  | .const => .const
  | .app h1 h2 => .app (h1.weak' W) (h2.weak' W)
  | .lam h1 h2 => .lam (h1.weak' W) (h2.weak' W.cons)
  | .forallE h1 h2 => .forallE (h1.weak' W) (h2.weak' W.cons)
  | .beta h1 h2 => by rw [SExpr.lift'_inst_hi]; exact (h1.weak' W.cons).beta (h2.weak' W)
  | .extra h1 h2 h3 h4 h5 => sorry

def ParRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (ParRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

theorem ParRedS.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≫* e2) :
    Γ' ⊢ e1.lift' ρ ≫* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

scoped notation:65 Γ " ⊢ " e1 " ▷ " e2:36 => InferType Γ e1 e2
inductive InferType : List SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i ▷ A
  | sort : Γ ⊢ .sort u ▷ .sort (.succ u)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls ▷ (SExpr.mk ci.type).instL ls
  | app : Γ ⊢ f ▷ F → Γ ⊢ F ⤳* .forallE A B → Γ ⊢ a :↑ A → Γ ⊢ .app f a ▷ B.inst a
  | lam : Γ ⊢ A :↑ .sort u → A::Γ ⊢ body ▷ B → Γ ⊢ .lam A body ▷ .forallE A B
  | forallE : Γ ⊢ A ▷ U → Γ ⊢ U ⤳* .sort u →
    A::Γ ⊢ B ▷ V → A::Γ ⊢ V ⤳* .sort v → Γ ⊢ .forallE A B ▷ .sort (.imax u v)

theorem InferType.hasType (H : Γ ⊢ e ▷ A) : Γ ⊢ e : A := sorry

theorem InferType.determ (H1 : Γ ⊢ e ▷ A) (H2 : Γ ⊢ e ▷ A') : A = A' := by
  induction H1 generalizing A' with
  | bvar h1 => cases H2 with | bvar h2 => exact h1.determ h2
  | sort => cases H2; rfl
  | const l1 l2 => cases H2 with | const r1 r2 => cases l1.symm.trans r1; rfl
  | app l1 l2 _ ih =>
    cases H2 with | app r1 r2 => cases ih r1; cases l2.determ .forallE r2 .forallE; rfl
  | lam _ l2 ih => cases H2 with | lam _ r2 => cases ih r2; rfl
  | forallE l1 l2 l3 l4 ih1 ih2 =>
    cases H2 with | forallE r1 r2 r3 r4
    cases ih1 r1; cases l2.determ .sort r2 .sort
    cases ih2 r3; cases l4.determ .sort r4 .sort; rfl

theorem InferType.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷ A → Δ ⊢ e.lift' ρ ▷ A.lift' ρ
  | .bvar h => .bvar (h.weak' W)
  | .sort => .sort
  | .const h1 h2 => by rw [(henv.closedC h1).mkS.instL.lift'_eq .zero]; exact .const h1 h2
  | .app h1 h2 h3 => SExpr.lift'_inst_hi .. ▸ .app (h1.weak' W) (h2.weak' W) (h3.weak' W)
  | .lam h1 h2 => .lam (h1.weak' W) (h2.weak' W.cons)
  | .forallE h1 h2 h3 h4 => .forallE (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (h4.weak' W.cons)

theorem InferType.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷ A := by
  generalize he : e.lift' ρ = e' at H
  induction H generalizing Γ ρ e with
  | bvar h => let .bvar _ := e; cases he; let ⟨_, h1, h2⟩ := h.weakU_inv W; exact ⟨_, h1, .bvar h2⟩
  | sort => let .sort _ := e; cases he; exact ⟨_, rfl, .sort⟩
  | const h1 h2 =>
    let .const .. := e; cases he
    exact ⟨_, ((henv.closedC h1).mkS.instL.lift'_eq .zero).symm, .const h1 h2⟩
  | app h1 h2 h3 ih =>
    let .app .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih W rfl
    obtain ⟨F, a2, a3⟩ := h2.weakU_inv W; cases F <;> cases a2
    refine ⟨_, by rw [SExpr.lift'_inst_hi], .app a1 a3 (h3.weak'_inv W)⟩
  | lam h1 h2 ih =>
    let .lam .. := e; cases he
    obtain ⟨_, rfl, a2⟩ := ih W.cons rfl
    exact ⟨_, rfl, .lam (h1.weak'_inv W) a2⟩
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    let .forallE .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih1 W rfl
    obtain ⟨U, a2, a3⟩ := h2.weakU_inv W; cases U <;> cases a2
    obtain ⟨_, rfl, b1⟩ := ih2 W.cons rfl
    obtain ⟨V, b2, b3⟩ := h4.weakU_inv W.cons; cases V <;> cases b2
    exact ⟨_, rfl, .forallE a1 a3 b1 b3⟩

theorem InferType.weak'_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A.lift' ρ) : Γ ⊢ e ▷ A := by
  obtain ⟨_, h1, h2⟩ := H.weakU_inv W
  exact SExpr.lift'_inj.1 h1 ▸ h2

theorem InferType.subst (W : Ctx.Subst InferType Δ σ Γ)
    (H : Γ ⊢ e ▷ A) : Δ ⊢ e.subst σ ▷ A.subst σ := by
  induction H generalizing Δ σ with
  | @bvar Γ i A h =>
    simp [SExpr.subst]
    induction W generalizing i A with | nil | @cons Γ σ B W h' ih <;> cases h
    case zero => rw [SExpr.lift, SExpr.subst_lift']; exact h'
    case succ i C h => rw [SExpr.lift, SExpr.subst_lift']; exact ih h
  | sort => exact .sort
  | const h1 h2 =>
    rw [(henv.closedC h1).mkS.instL.subst_eq .zero]
    exact .const h1 h2
  | app h1 h2 h3 ih => exact subst_inst ▸ .app (ih W) (h2.subst W) (h3.subst W)
  | lam h1 h2 ih => exact .lam (h1.subst W) (ih (W.lift .bvar))
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    exact .forallE (ih1 W) (h2.subst W) (ih2 (W.lift .bvar)) (h4.subst (W.lift .bvar))

theorem InferType.inst (H₀ : Γ ⊢ a ▷ A₀) (H : A₀::Γ ⊢ e ▷ A) :
    Γ ⊢ e.inst a ▷ A.inst a := .subst (.one H₀) H

def InferTypeS (Γ : List SExpr) (e A : SExpr) := ∃ A', Γ ⊢ e ▷ A' ∧ Γ ⊢ A' ⤳* A
scoped notation:65 Γ " ⊢ " e1 " ▷* " e2:36 => InferTypeS Γ e1 e2

theorem InferTypeS.hasType : Γ ⊢ e ▷* A → Γ ⊢ e : A := sorry

theorem WHRedS.inferType
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => rfl
    | head r1 => cases W1 _ r1
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem WHRedS.parRedS (H : Γ ⊢ e ⤳* e') : Γ ⊢ e ≫* e' := sorry

theorem InferTypeS.determ
    (H1 : Γ ⊢ e ▷* A) (W1 : WHNF Γ A)
    (H2 : Γ ⊢ e ▷* A') (W2 : WHNF Γ A') : A = A' := by
  let ⟨_, h1, h2⟩ := H1; let ⟨_, h3, h4⟩ := H2
  cases h1.determ h3; exact h2.determ W1 h4 W2

theorem InferTypeS.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷* A → Δ ⊢ e.lift' ρ ▷* A.lift' ρ
  | ⟨_, h1, h2⟩ => ⟨_, h1.weak' W, h2.weak' W⟩

theorem InferTypeS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷* A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷* A := by
  let ⟨_, h1, h2⟩ := H
  obtain ⟨_, rfl, a1⟩ := h1.weakU_inv W
  obtain ⟨_, rfl, a2⟩ := h2.weakU_inv W
  exact ⟨_, rfl, _, a1, a2⟩

scoped notation:65 Γ " ⊢ " e1 " ≡ₚ " e2 " : " A:36 => NormalEq Γ e1 e2 A
inductive NormalEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e : A
  | appDF : Γ ⊢ f₁ ≡ₚ f₂ : .forallE A B → Γ ⊢ a₁ ≡ₚ a₂ : A →
    Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂ : B.inst a₁
  | lamDF : Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body₁ ≡ₚ body₂ : B → Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂ : .forallE A B
  | forallEDF : Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u →
    Γ ⊢ A₁ ≡ₚ A₂ : .sort u → A::Γ ⊢ B₁ ≡ₚ B₂ : .sort v →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂ : .sort (.imax u v)
  | etaL : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) : B → Γ ⊢ .lam A e ≡ₚ e' : .forallE A B
  | etaR : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e : B → Γ ⊢ e' ≡ₚ .lam A e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ₚ h' : p
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ₚ e2 : A → Γ ⊢ e1 ≡ₚ e2 : B

theorem NormalEq.defeqDFC (W : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ≡ₚ e2 : A) : Γ₂ ⊢ e1 ≡ₚ e2 : A := by
  induction H generalizing Γ₂ with
  | refl h => refine .refl (h.defeqDFC W)
  | appDF h1 h2 ih1 ih2 => exact .appDF (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 _ ih2 =>
    exact .lamDF (h1.defeqDFC W) (h2.defeqDFC W)
      (h3.defeqDFC (W.succ h1.hasType.2)) (ih2 (W.succ h1.hasType.2))
  | forallEDF h1 h2 _ _ ih1 ih2 =>
    exact .forallEDF (h1.defeqDFC W) (h2.defeqDFC W) (ih1 W) (ih2 (W.succ h1.hasType.2))
  | etaL h1 h2 h3 _ ih =>
    exact .etaL (h1.defeqDFC W) (h2.defeqDFC (W.succ h1)) (h3.defeqDFC W) (ih (W.succ h1))
  | etaR h1 h2 h3 _ ih =>
    exact .etaR (h1.defeqDFC W) (h2.defeqDFC (W.succ h1)) (h3.defeqDFC W) (ih (W.succ h1))
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.defeqDFC W) (h2.defeqDFC W) (h3.defeqDFC W)
  | defeqDF h1 _ ih => exact .defeqDF (h1.defeqDFC W) (ih W)

theorem NormalEq.defeq (H : Γ ⊢ e1 ≡ₚ e2 : A) : Γ ⊢ e1 ≡ e2 : A := by
  induction H with
  | refl h => exact h
  | appDF h1 h2 ih1 ih2 => exact .appDF ih1 ih2
  | lamDF hA₁ hA₂ hB _ ihB =>
    exact have W := .succ .zero hA₁.symm
      .defeqDF (.forallEDF hA₁ (hB.defeqDFC W)) (.lamDF (hA₁.trans hA₂.symm) (ihB.defeqDFC W))
  | forallEDF hA₁ hA₂ _ _ ihA ihB =>
    exact .forallEDF (hA₁.trans hA₂.symm) (ihB.defeqDFC (.succ .zero hA₁.symm))
  | etaL hA _ h1 _ ih => exact .trans (.lamDF hA ih) (.eta h1)
  | etaR hA _ h1 _ ih => exact .trans (.symm (.eta h1)) (.lamDF hA ih)
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3
  | defeqDF h1 _ ih => exact .defeqDF h1 ih

theorem NormalEq.symm (H : Γ ⊢ e1 ≡ₚ e2 : A) : Γ ⊢ e2 ≡ₚ e1 : A := by
  induction H with
  | refl h => exact .refl h
  | appDF h1 h2 ih1 ih2 => exact .defeqDF sorry (u := sorry) <| .appDF ih1 ih2
  | lamDF h1 h2 h3 _ ih2 => exact .lamDF h2 h1 h3 ih2
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF h2 h1 ih1 ih2
  | etaL h1 h2 h3 _ ih => exact .etaR h1 h2 h3 ih
  | etaR h1 h2 h3 _ ih => exact .etaL h1 h2 h3 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2
  | defeqDF h1 _ ih => exact .defeqDF h1 ih

theorem NormalEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ₚ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ₚ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing Γ' ρ with
  | refl h => exact .refl (h.weak' W)
  | appDF h1 h2 ih1 ih2 => exact .defeqDF sorry (u := sorry) <| .appDF (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 _ ih2 => exact .lamDF (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (ih2 W.cons)
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF (h1.weak' W) (h2.weak' W) (ih1 W) (ih2 W.cons)
  | etaL h1 h2 h3 _ ih =>
    refine .etaL (h1.weak' W) (h2.weak' W.cons) (h3.weak' W) ?_
    simpa [← SExpr.lift'_comp] using ih W.cons
  | etaR h1 h2 h3 _ ih =>
    refine .etaR (h1.weak' W) (h2.weak' W.cons) (h3.weak' W) ?_
    simpa [← SExpr.lift'_comp] using ih W.cons
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.weak' W) (h2.weak' W) (h3.weak' W)
  | defeqDF h1 _ ih => exact .defeqDF (h1.weak' W) (ih W)

def CRDefEq (Γ : List SExpr) (e₁ e₂ A : SExpr) : Prop :=
  Γ ⊢ e₁ ≡ e₂ : A ∧
  ∃ e₁' e₂', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₂ ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂' : A
scoped notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " : " A:36 => CRDefEq Γ e1 e2 A

def CRDefEqLift := WithLift CRDefEq
scoped notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " :↑ " A:36 => CRDefEqLift Γ e1 e2 A

theorem CRDefEq.normalEq (H : Γ ⊢ e₁ ≡ₚ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂ : A :=
  ⟨H.defeq, _, _, .rfl, .rfl, H⟩

theorem CRDefEq.refl (H : Γ ⊢ e : A) : Γ ⊢ e ≫≪ e : A :=
  .normalEq (.refl H)

theorem CRDefEq.defeq : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₁ ≡ e₂ : A := (·.1)

theorem CRDefEq.symm : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₁ : A
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.symm, _, _, h4, h3, h5.symm⟩

theorem CRDefEq.trans : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₃ : A → Γ ⊢ e₁ ≫≪ e₃ : A
  | ⟨l1, _, _, l3, l4, l5⟩, ⟨r1, _, _, r3, r4, r5⟩ => sorry

theorem CRDefEq.defeqDF : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ A ≡ B : .sort u → Γ ⊢ e₁ ≫≪ e₂ : B
  | ⟨l1, _, _, l3, l4, l5⟩, H => ⟨H.defeqDF l1, _, _, l3, l4, l5.defeqDF H⟩

theorem CRDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫≪ e2 : A → Γ' ⊢ e1.lift' ρ ≫≪ e2.lift' ρ : A.lift' ρ
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.weak' W, _, _, h3.weak' W, h4.weak' W, h5.weak' W⟩

theorem WHRedS.crDefEq (H1 : Γ ⊢ e1 : A) (H2 : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1 ≫≪ e2 : A :=
  ⟨H2.defeq H1, _, _, H2.parRedS, .rfl, .refl (H2.defeq H1).hasType.2⟩

nonrec theorem CRDefEqLift.symm : Γ ⊢ e1 ≫≪ e2 :↑ A → Γ ⊢ e2 ≫≪ e1 :↑ A := .symm .symm

theorem CRDefEqLift.defeq (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 ≡ e2 :↑ A := H.imp (·.1)

theorem CRDefEqLift.left (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 :↑ A := H.defeq.left

nonrec theorem CRDefEqLift.refl (H : Γ ⊢ e :↑ A) : Γ ⊢ e ≫≪ e :↑ A :=
  .refl (.refl <| H.left' · · ·)

theorem InferType.whRed (H1 : Γ ⊢ e ⤳ e') (H2 : Γ ⊢ e ▷ A) : Γ ⊢ e' ▷ A := by
  induction H1 generalizing A with
  | app h1 ih => let .app r1 r2 r3 := H2; exact .app (ih r1) r2 r3
  | beta =>
    let .app a1 a2 a3 := H2
    let .lam b1 b2 := a1
    cases WHNF.forallE.whRedS a2
    exact .inst sorry b2
  | extra => sorry
