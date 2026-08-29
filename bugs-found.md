# Bugs found as a result of formalization

## In Lean's own kernel

* https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Soundness.20bug.3A.20hasLooseBVars.20is.20not.20conservative/near/521286338
* https://github.com/leanprover/lean4/issues/10475
* https://github.com/leanprover/lean4/issues/10511

Nothing new here from the `kernel_sound` work so far. Four pieces of upstream
behaviour did turn out to constrain the specification, and are recorded because a
reader will otherwise assume the opposite:

* **Positivity is checked on the whnf of a field's domain, but constructor types
  are stored un-normalised** (`Add.lean:190` vs the stored type). So
  `Foo.mk : (r : Foo) → (fun _ => Nat) r → Foo` is accepted by *both* kernels
  even though that field's stored type mentions the block constant and an
  earlier recursive field. Any syntactic occurrence condition in the abstract
  spec would reject a declaration both kernels accept. Verified by building the
  declaration by hand and running it through each.
* **A mutual block's types may not mention each other**, because each
  `indType.type` is type-checked before any of them is declared. So every index
  telescope of a block is block-free — which is what makes the set-theoretic
  interpretation of a constructor's non-recursive fields independent of the
  family being constructed.
* **The declared types of the `Nat` primitives carry `@&` borrow annotations**
  (`.mdata { borrowed := true }` around each `Nat` domain). Structural
  comparison of a declared type against `q(Nat → Nat → Nat)`, which is what the
  `Char.ofNat` branch does, is therefore not available for them.
* **The safe/`partial`/`unsafe` boundary is enforced identically by both
  kernels, in every syntactic position — a verified non-bug.** Recorded so the
  next person does not have to re-run the experiments. The check is
  `type_checker::infer_constant`, `~/lean4/src/kernel/type_checker.cpp:109-117`,
  guarded by `!infer_only`; its lean4lean mirror is
  `Lean4Lean/TypeChecker.lean:125-131`. `inferOnly` is threaded faithfully into
  every subterm by `inferType'` when it is `false`, so there is no fast-path
  escape hatch.

  Both kernels **accept** `partial def bad : (∀ p : Prop, p) := bad` and its
  `unsafe` twin, submitted as a `.mutualDefnDecl`, and both **reject** a *safe*
  `.mutualDefnDecl` outright with `invalid mutual definition, declaration is not
  tagged as unsafe/partial`. So a kernel-level `mutualDefnDecl` is only ever
  `partial`/`unsafe`.

  Eleven safe consumers of such a constant were built by hand and run through
  `Lean4Lean.addDecl` and `Lean.Kernel.Environment.addDeclCore` on the *same*
  environment, and eight of them again against an environment the C++ kernel had
  built for itself. All are rejected by both, with byte-identical messages —
  `invalid declaration, safe declaration must not contain partial declaration
  'L4LBadP'` and `invalid declaration, it uses unsafe declaration 'L4LBadU'`.
  The positions, tag in parentheses: a `defnDecl`'s value (`partial`, `unsafe`);
  a `thmDecl`'s value (`partial`, `unsafe`); an `axiomDecl`'s **type**
  (`partial`); behind a beta redex, `(fun f => f False) bad` (`partial`); in a
  `let` value (`partial`); under `.mdata` (`partial`); an `opaqueDecl`'s value
  (`partial`); and the **constructor type of an `inductDecl`** (`partial`,
  `unsafe`).

  The consequence for the specification: **the safe fragment is closed**, so a
  `partial`/`unsafe` constant can be given no image at all in the `safe`-level
  abstract environment without losing anything the kernel accepts. Entry 9 below
  is the fix that relies on this.

15. **`init_quot` accepts an `unsafe inductive Eq`, and then installs a *safe*
    `Quot.lift` whose type mentions it.** Present in **both** kernels:
    `check_eq_type` (`~/lean4/src/kernel/quot.cpp:19-44`) and its lean4lean
    mirror `Lean4Lean.checkEqType` (`Lean4Lean/Quot.lean`) check that `Eq` is an
    inductive with one universe parameter, one constructor, and the exact
    expected types for the type and the constructor — and check nothing about
    its safety tag. `Eq` is not in `Lean.Kernel.Environment.primitives`, so
    `checkName` does not object; `checkPrimitiveInductive` recognises only `Bool`
    and `Nat`, and in any case returns `false` immediately when `isUnsafe`, so
    `allowPrimitive` plays no part. Positivity is *skipped* for an unsafe block
    (`Add.lean:381`, `!isUnsafe` guard), so the declaration is admitted without
    the check that the safe path applies.

    **Witness, machine-checked, C++ kernel.** A `prelude` file with no imports:

    ```lean
    prelude
    universe u
    unsafe inductive Eq : {α : Sort u} → α → α → Prop where
      | refl : ∀ {α : Sort u} (a : α), Eq a a
    init_quot
    ```

    This elaborates with no error. `#print Eq` reports
    `unsafe inductive Eq.{u} : {α : Sort u} → α → α → Prop`, and `#print Quot.lift`
    reports
    `Quotient primitive Quot.lift.{u, v} : … → (∀ (a b : α), r a b → Eq (f a) (f b)) → Quot r → β`.
    The same declaration built by hand and passed to `Lean4Lean.addDecl` followed
    by `Lean4Lean.Environment.addQuot` on `Kernel.Environment.empty` was accepted
    by lean4lean too (before the fix).

    **What actually goes wrong in the C++ kernel.** Not a proof of `False`: the
    shape of `Eq` is pinned exactly by `check_eq_type`, so the unsafe tag buys no
    extra strength for `Eq` itself — the constructor type it forces is positive
    anyway. What breaks is the **safe/unsafe stratification invariant**, which
    both kernels otherwise enforce in every syntactic position (see the
    "verified non-bug" entry above): `type_checker::infer_constant`
    (`type_checker.cpp:109-117`) rejects any *safe* declaration that names an
    *unsafe* constant. `add_quot` installs `Quot`, `Quot.mk`, `Quot.lift` and
    `Quot.ind` with `add_core`, which **bypasses the type checker entirely**, and
    a `quot_val` is always safe (`ConstantInfo.isUnsafe` returns `false` for
    `.quotInfo` unconditionally). So `init_quot` mints a safe constant whose
    stored type names an unsafe one — a state the kernel refuses to let any
    ordinary declaration reach. In the same file, appending

    ```lean
    axiom bad : ∀ {α : Sort u} (a : α), Eq a a
    axiom useLift : ∀ {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β),
      (∀ (a b : α), r a b → Eq (f a) (f b)) → Quot r → β
    ```

    gives, twice,
    `error: (kernel) invalid declaration, it uses unsafe declaration 'Eq'` — the
    second of those is literally `Quot.lift`'s own type, spelled out. So the
    honest statement of the C++ consequence is: **`init_quot` produces an
    environment whose `Quot.lift` cannot be re-declared, and in which the
    invariant "no safe constant mentions an unsafe one" is false.** It is a
    reachable inconsistency in the kernel's own bookkeeping, not (as far as this
    stream could establish) a route to `False`.

    **What goes wrong here.** For lean4lean it is worse than bookkeeping, because
    `kernel_sound` reads a model. `TrEnv'` is indexed by `quotInit`, and the only
    constructor setting it is `TrEnv'.quot`, whose first premise is
    `VEnv.QuotReady env`, i.e. `env.constants ``Eq = some eqConst`. So
    `TrEnv safety env venv` with `env.quotInit = true` forces `Eq` into the model
    and hence forces `Eq` visible at `safety`
    (`TrEnv.eq_visible_of_quotInit`, `Verify/SafeFragment.lean`); at
    `safety = .safe` that is `ci.safety = .safe`. An unsafe `Eq` will moreover be
    in **no** model at **any** level, because `TrEnv'.induct` is to be gated to
    safe blocks (positivity is skipped when `isUnsafe`, so `VIndField.WF.pos` has
    no witness and `TrEnv'.ignore` takes the declaration). So after a
    `.quotDecl` step on such an environment, `∃ venv, TrEnv .safe env venv` is
    **false**, and `addQuot.WF` — hence `addDecl.WF`, hence `kernel_sound` — is
    unprovable, not merely unproved. It is masked today only because
    `checkEqType.WF`'s postcondition is `False`, discharged from
    `TrEnv'.no_inductInfo` at `.unsafe`, which holds only because `AddInduct` has
    no constructors yet.

    **Fixed in lean4lean** (`Lean4Lean/Quot.lean`): `checkEqType` now rejects an
    `Eq` whose `InductiveVal.isUnsafe` is `true`. This is a deliberate divergence
    from the C++ kernel — see `divergences.md`. Proof side:
    `Lean4Lean/Verify/EqSafety.lean` proves the necessity direction
    (`TrEnv.eq_isUnsafe_false_of_quotInit`: the `.safe` model demands exactly this
    check) and the sufficiency direction (`checkEqType.WF_safe`: the checker now
    establishes it), and reduces the full non-vacuous `checkEqType.WF` to the
    single `AddInduct` premise that a safe inductive `Eq` translates to
    `eqConst`. Kernel Arena: 185 correct / 6 either / 0 incorrect, unchanged.

## In the lean4lean kernel implementation

Found while trying to prove `checkPrimitiveDef.WF`, the statement that the
primitive-definition recognizer establishes what the abstract model assumes.
`checkPrimitiveDef` is a lean4lean-only check (see `divergences.md`): Lean itself
does not verify that primitives are declared with the right types and
definitional behaviour, because it ships its prelude. lean4lean does verify it,
and the verification was not sound.

1. **`Char.ofNat` and `String.ofList` were recognized up to definitional
   equality, where the model pins a literal type.** `VEnv.HasPrimitives` fixes
   these constants' `VConstant` to a syntactic type, and `TrConstant` reads
   `v.type` off structurally — but the recognizer only checked
   `isDefEq v.type q(Nat → Char)`. Declaring `Char.ofNat` at
   `(fun _ : Nat => Nat → Char) Nat.zero` passed the check and translated to a
   different constant, so the recognizer's postcondition was false. **Fixed**:
   those branches now compare with `Expr.eqv`.

2. **The `Nat` equations were checked on deliberately ill-typed terms.**
   `defeq1`/`defeq2` compared `∀ _ : Nat, e₁` against `∀ _ : Nat, e₂` to get
   under a binder, but `Nat.add x 0` is not a type, so the comparison had no
   `TrExprS` witness and carried no semantic content whatsoever — every one of
   those checks was vacuous with respect to the model. `Nat.land` and `Nat.lor`
   additionally bound their `Bool` variable at type `Nat`, which is not merely
   untranslatable but plainly ill-typed. **Fixed**: the equations are now checked
   under `withLocalDecl`-bound free variables, as the `Nat.div`/`Nat.mod`
   branches already did.

3. **Branches depended on constants they never required to be present.** Every
   arithmetic branch built `Nat`/`Bool` literals, and depended on other
   primitives' semantics, without requiring any of them in the environment. Each
   was implied by a later `checkType`, but only by inverting "type checking
   succeeded" — and the `TrExprS` witnesses the `isDefEq` specification demands
   cannot be built before that inversion is available. **Fixed**: explicit
   `env.contains` guards. They reject nothing new; the arena confirms it.

4. **`checkPrimitiveDef` runs before `checkConstantVal`, so it calls `isDefEq` on
   untyped input.** A successful comparison is recorded in the `EquivManager`,
   whose well-formedness invariant demands `TrExprS` witnesses on both sides,
   and untyped input has none. The recognizer returns `.ok true` on
   `Nat.pred : (fun _ : NoSuchType => Nat → Nat) NoSuchValue := fun n => n`,
   whose type mentions constants absent from the environment, and its final
   `eqvManager` merges that type with `Nat → Nat` into one class.

   **Not a soundness bug — a broken postcondition.** Run end to end, both
   `Lean4Lean.addDecl` and Lean's own kernel reject the declaration with
   `unknown constant 'NoSuchType'`; `checkConstantVal`'s type check catches it
   immediately after. Nothing unsound is accepted and the arena is unaffected.
   What is false is `checkPrimitiveDef.WF`'s postcondition, since `M.WF` demands
   the state *after* the recognizer satisfy `VState.WF` and `checkDefinition.WF`
   continues from it. The C++ kernel has no analogue because it has no
   `checkPrimitiveDef` at all, so this is a lean4lean-only proof-obligation
   defect with no behavioural divergence. **Open**; the fix is either to run the
   recognizer after `checkConstantVal`, or to have each branch obtain its own
   witnesses by comparing against `checkType v.value` rather than the unchecked
   `v.type`.

14. **lean4lean did not re-check what `restoreNested` rewrote; the C++ kernel
    does.** A missing check, i.e. a divergence in the *accepting* direction.
    (Numbered by discovery order, not by section.)

    For a nested inductive, `restoreNested` rewrites every constructor type,
    every recursor type and every recursor rule `rhs` **after** the auxiliary
    block has been checked, and the rewritten terms are never checked again in
    the resulting environment. Both kernels do this rewrite. The C++ kernel then
    re-checks all of it — `~/lean4/src/kernel/inductive.cpp:1325-1346`, whose own
    comment is explicit:

    > *Re-check everything `restore_nested` rewrote: the constructor types, and
    > the recursor types and computation rules. The rewritten terms are not
    > otherwise checked in `new_env`. … it keeps a mistake in the restoration
    > from reaching the environment.*

    lean4lean had only the *preceding* check (`inductive.cpp:1317-1324`, the
    lean4#14576/#14577 hardening: type-check the nested applications `I Ds`
    whose parametric arguments are dropped from the auxiliary declaration). It
    had no analogue of the re-check.

    **This corrects a claim made in an earlier scoping report**, that "the kernel
    trusts a rewrite it does not verify." That is false of the C++ kernel, which
    verifies it deliberately. It was true only of lean4lean, which makes it our
    bug rather than an upstream property.

    **Established by mutant, because nothing else can reach this code.** Item 12
    below: the arena has zero nested-inductive coverage, so the suite cannot
    exercise this path at all — 185/6/0 before and after. The mutant was to drop
    the `restoreNested` call on the recursor type, simulating exactly the
    "mistake in the restoration" the upstream comment names:

    | | re-check present | re-check absent |
    |---|---|---|
    | mutated `restoreNested` | **rejected** — `unknown constant '_nested.List_1'` | **accepted** |

    Without the check, lean4lean stored a recursor whose type mentions a constant
    that is not in the resulting environment, and nothing downstream noticed.

    **Fixed**: `Inductive/Add.lean` now mirrors `inductive.cpp:1325-1346`,
    re-checking each constructor type at the declaration's level parameters and
    each recursor type and rule `rhs` at the recursor's own level parameters
    (which differ — the elimination universe is prepended). Arena unchanged at
    185/6/0, which — per item 12 — is evidence of no regression and *not*
    evidence the fix works; the mutant table is that evidence.

    **Calibration.** No witness is claimed of an unmutated lean4lean accepting
    something unsound through this gap, and upstream's comment says the preceding
    checks are expected to make the re-check redundant ("these checks are not
    necessary. We added them to catch additional bugs and missing checks in the
    nested inductive handling"). This is defence in depth that lean4lean was
    missing, not a demonstrated soundness hole.

## In the lean4lean proof infrastructure

Not kernel bugs — defects in the specification and its metatheory, which matter
because they are what `kernel_sound` is stated against.

5. **`VEnv.HasPrimitives` pinned neither `Nat.pred` nor `Nat.bitwise`,** yet the
   `Nat.sub` branch depends on the first and `land`/`lor`/`xor` on the second. An
   environment defining `Nat.pred := fun _ => 0` satisfied `HasPrimitives` and
   still passed the `Nat.sub` check, refuting the recognizer's postcondition.
   **Fixed.** `Nat.bitwise`'s field needed care: it is second order, so the
   obvious statement puts `ReflectsBoolBoolBool` in negative position and is not
   monotone, which a `HasPrimitives` invariant must be. It is relativized to an
   arbitrary extension instead.

6. **The empty environment had no model at all.** `Kernel.Environment.empty`
   builds its constant map at `SMap` stage 2, so `stage₁` is `false`, while
   `TrEnv'.empty` and `Aligned.empty` pinned the literal `({} : ConstMap)` whose
   `stage₁` defaults to `true` — and no other `TrEnv'` rule can produce
   `VEnv.empty` at that map. So `∃ ves, ves.WF (Kernel.Environment.empty ‵main)`
   was underivable, which would have made every statement about a run of the
   checker vacuous. **Fixed**: both `empty` constructors now take the two facts
   actually consumed downstream.

7. **`SExpr.Params.extra_pat` was a standalone `axiom` that proves `False`.** It
   was one because `SExpr.Params` is declared before `SExpr` exists, so a field
   mentioning `SExpr.IsDefEq` was impossible. Guard 2 did not catch it because
   `Experimental/` is outside `kernel_sound`'s cone — but the whole injectivity
   route runs through `Params`, so anything proved that way would have been
   vacuous. **Fixed**: it and `ctor_ty` now live in a companion class declared
   after the judgment.

8. **`SExpr.IsDefEq.strong` is false as stated,** for two independent reasons.
   It lacks the `Ctx.WF Γ` hypothesis its `VExpr` analogue carries —
   `IsDefEqStrong.bvar` demands the looked-up type be a type while
   `IsDefEq.bvar` assumes nothing about the context, and `Γ = [.bvar 0]` is a
   witness. And `CtorBundle.hu0` asserts the constructor's result sort is
   nonzero, which fails for `Eq.refl`, whose codomain is a `Prop` — yet `Eq.refl`
   must still classify as a constructor, because `Eq.rec`'s ι-rule matches on it.
   **Statement fixed**; `hu0` recorded with its exact location.

9. **`VDecl.WF.mutualDef` refuted `leanTTConsistent`.** The rule typechecked each
   member's *value* in `env'`, the environment that already carries the block's
   own constants, so `def f : (∀ p : Prop, p) := f` was a well-formed,
   axiom-free step over any environment in which one name is free. Since
   `VDecl.isAxiomFree` admitted it and `VEnv.LeanWF` asked for nothing more, the
   consistency statement that links 1 and 2 of `PLAN.md` compose through was
   **false, not merely unproved**. `Theory/MutualDefUnsound.lean` is the
   machine-checked witness (`selfRef_wf`, `selfRef_inconsistent`), kept as a
   regression test rather than deleted: nothing else pins the exclusion, and if
   the step is ever readmitted to the pure fragment that file goes red.

   **This is not a kernel bug and not a divergence.** Both kernels reject a safe
   mutual block and refuse to look through a `partial`/`unsafe` constant while
   checking a safe declaration (fourth bullet under "In Lean's own kernel"). The
   abstract theory simply modelled no safety tag: `VConstant` is
   `⟨uvars, type⟩` and `VDecl.WF` had no safety condition anywhere.

   **Fixed**, but *not* by dropping the constructor — that turned out to be
   impossible, for a reason worth recording. The refinement layer keeps three
   safety-indexed models (`VEnvs`), and the `partial`/`unsafe` ones must carry
   the block's defining equations: `ConstantInfo.deltaValue?`
   (`Lean4Lean/Declaration.lean:15`) is `some` for *every* `.defnInfo`, and
   `isDelta` (`Lean4Lean/TypeChecker.lean:427`) has no safety guard, so the
   kernel really does delta-unfold a `partial` definition — confirmed by running
   `whnf` on one at `safety := .partial` and `.unsafe`, which reduces. Without
   the equations `TrEnv'.of_value` is false, and with them the step is
   necessarily circular. Removing the constructor outright would additionally
   require deleting the `.partial`/`.unsafe` levels of `VEnvs` and making
   `safety = .safe` a `VContext` invariant, since `Aligned.find?` at
   `safety := .unsafe` owes an image for every constant
   (`Verify/TypeChecker/InferType.lean:85` is the consumer).

   What landed instead: the constructor is renamed `VDecl.unsafeDef` and
   documented as the sole impure former; `VDecl.isPure` (which replaces
   `isAxiomFree` in `VEnv.LeanWF`) is `False` on it as well as on `.axiom`; and
   `TrEnv'.unsafeDef` gains a **safety gate** — at least one member must carry a
   `DefinitionSafety` other than `.safe`. Because `TrDefBlock .safe` forces every
   member to be `.safe`, the gate is unsatisfiable at `safety := .safe`, which
   `TrEnv'.wf_noUnsafe` turns into the fact that the safe-level model is built
   without the circular step; `partial`/`unsafe` constants reach it only through
   `TrEnv'.ignore`, which gives them no counterpart at all. The gate is
   discharged from the tag the kernel itself checked — `addMutual.WF` takes it
   from the `if let .safe := v₀.safety then throw` branch it has just ruled out,
   and `addUnsafeDef.WF` from `v.safety = .unsafe` — not assumed.

   **Held, not rejected**: collapsing `VEnvs` to the single `safe` model would be
   a net simplification and would let the constructor go entirely. It is
   cross-cutting (`Verify/TypeChecker.lean`, `TypeChecker/Basic.lean`,
   `InferType.lean`, `Primitive.lean`, all of `Verify/Environment/`,
   `Bridge.lean`) and is not on the critical path, since the fragment is already
   closed.

10. **`.proj` on a *recursive* single-constructor inductive is accepted by both
    kernels and cannot be modelled by `TrProj`.** `VExpr` has no projection
    constructor, so `TrProj` (`Verify/Typing/Expr.lean`) translates `Expr.proj`
    into the recursor application `VInductDecl'.projTerm`
    (`Theory/Inductive/Structure.lean`), whose minor premise is
    `fun f₀ … f_{n-1} => fᵢ` — it binds only the constructor's fields. A
    constructor with recursive fields has a minor premise that *also* binds the
    induction hypotheses (`D.ihTypes`), so that term has the wrong arity, and
    `VEnv.IsStructure.noRec : C.recFields = []` therefore restricts `TrProj` to
    non-recursive constructors.

    `structure` never emits a recursive constructor, so the elaborator cannot
    produce this — but `kernel_sound` quantifies over arbitrary `Declaration`
    lists, and `inferProj` (`TypeChecker.lean:233`) checks only that the type has
    a single constructor and enough parameters. It never looks at recursiveness.

    **Measured, not predicted.** With

    ```lean
    inductive R : Type | mk : R → Nat → R   -- isRec = true, isStructure = false
    ```

    hand-built declarations `fun r : R => r.0 : R → R` and
    `fun r : R => r.1 : R → Nat`, containing `Expr.proj`, are **accepted by
    Lean's own kernel and by `Lean4Lean.addDecl` alike** — for the recursive
    field as well as the ordinary one. They also *reduce*: with `r₀ : R` an
    axiom, `theorem _ : pr1 (R.mk r₀ 7) = 7 := Eq.refl 7` is accepted by both
    kernels, so ι-reduction fires through the hand-built projection and the term
    is fully computational, not merely well-typed.

    So this is a hole in the proof, not a missing convenience: `addDecl`
    succeeds, `TrProj` has no derivation, hence `TrExprS` has none,
    `addDecl.WF`'s conclusion is unavailable, and the soundness argument says
    nothing about an environment the checker accepted.

    Two ways out, neither implemented — recorded and costed first:

    * **Generalise the minor premise** over `D.ihTypes`, dropping `noRec`. Keeps
      both kernels in agreement and needs no arena run, but the generalised term
      cannot be validated the way `projTerm` is: no real Lean structure
      exercises it, so `StructureExamples.lean` would have nothing to compare
      against, and the de Bruijn arithmetic would rest on review alone.
    * **Have `addDecl` reject `.proj` when the constructor has recursive
      fields.** Smaller and checkable, but it is a deliberate divergence from the
      C++ kernel — a `divergences.md` entry — and needs an arena run to confirm
      nothing real depends on it.

11. **Nested inductives are accepted by `addDecl` and cannot be modelled at all,
    so `addDecl.WF`'s `inductDecl` branch is unprovable as stated.** The same
    shape of hole as item 10, one layer up: not a missing convenience, but a
    declaration form the checker accepts and the refinement says nothing about.

    `Environment.addInductive` does not stop when `AddInductive.run` returns.
    For `numNested ≠ 0` it **discards** that environment and rebuilds from the
    original one (`Inductive/Add.lean:747-776`), re-emitting every constructor
    and recursor with `restoreNested`-rewritten types and rules, plus the
    auxiliary recursors under renamed names (`mkAuxRecNameMap`); the `_nested.*`
    inductives and their constructors never reach the final environment. The
    restored types mention `List (Tree α)` where the auxiliary block declared
    `_nested.List_1 α`, and **those two constants are not definitionally
    equal**. So the final environment is not `addInduct' env D` for any `D`
    (`docs/design-inductive.md:73-74`), and since `TrEnv'`'s only inductive rule
    is `induct`, which demands exactly that, no `TrEnv'` derivation exists.

    `kernel_sound` quantifies over arbitrary `Declaration` lists, so the branch
    has to cover this. Three exits, and it is not really a choice:

    * **Thread `numNested = 0` through `addDecl.WF`.** Only relocates the hole —
      `Verify/Bridge.lean`'s `AddDeclWF` and `kernel_sound` need the branch
      unconditionally.
    * **Reject nested inductives in the checker.** **Dead**: see item 12. Costs
      nothing measurable in the arena and breaks anything importing Lean's own
      syntax tree.
    * **Extend the spec with `docs/design-inductive.md` §9.3 companion types** —
      a `VIndType` that names an already-declared `J` at a parameter
      instantiation, contributing only a new recursor and ι-rules. XL, and the
      only exit that closes the hole. Two constraints known up front:
      `VInductDecl'` currently has no notion of a type whose head is anything but
      `.const I_j ownLvls`, and `restoreNested` is a rewrite applied *after* the
      block is checked, so the companion story must explain why the rewritten
      types are well-typed without re-checking them.

## In the stop condition itself

Neither of these is a bug in a kernel or in a proof. They are defects in the
*instruments* `CLAUDE.md` uses to decide when the project is done — goal 1 (the
Kernel Arena suite) and `Verify/Guard.lean`'s check 3. They are recorded here
because an instrument that mismeasures is exactly as dangerous as a false lemma,
and neither is visible from inside the thing it measures.

12. **Goal 1 has zero nested-inductive coverage: a regression breaking nested
    inductives entirely would pass the stop condition.**

    `CLAUDE.md` goal 1 is "the Kernel Arena suite passes, every non-`either` test
    correct." Making `Environment.addInductive` reject every nested block
    outright — a one-line `throw` right after `numNested` is computed
    (`Inductive/Add.lean:768`) — changes **nothing**: all 191 test verdicts are
    byte-identical to the baseline, and the summary stays 185 correct / 6 either
    / 0 incorrect. That includes the two whole-library replays, `init` (53090
    declarations, 1.4 min) and `std` (2.3 min).

    **The patch was verified live before the null result was trusted.** Three
    positive controls, run against the patched build:

    * `inductive RT | node : List RT → RT` → rejected;
    * `inductive AT | node : Array AT → AT`, the `Lean.Syntax.node` shape →
      rejected;
    * a plain non-nested inductive → accepted.

    Nested inductives are not rare. In the loaded environment there are **53 of
    them out of 2893 inductives**, including `Lean.Syntax`, `Lean.MessageData`,
    `Lean.IR.FnBody`, `Lean.Doc.Part` and a dozen `Grind.Arith.Cutsat`
    constraint types. By module root: `Init` 1, `Std` 2, `Lean` 50.

    **Traced cause.** `import Init` contains exactly one nested inductive,
    `Lean.Syntax`, at `numNested = 2`, declared in `Init.Prelude`; its *stored*
    constructor types really do mention the nested occurrences
    (`Lean.Syntax.node : SourceInfo → SyntaxNodeKind → Array Syntax → Syntax`,
    `Lean.Syntax.ident : … → List Syntax.Preresolved → Syntax`), so replaying it
    would take the nested path. It is not replayed, because **the export does not
    contain it**: grepping the 310 MB `init.ndjson` produced by `lean4export`
    3.1.0 finds `Lean.Syntax.Preresolved.decl` and
    `Lean.Syntax.Preresolved.namespace` — a different, non-nested inductive — and
    no `Lean.Syntax`.

    Two alternative explanations were ruled out first, which is what makes this a
    finding rather than a suspicion:

    * `Replay` does not skip inductives. `Replay.lean:192-210` rebuilds
      `.inductDecl lparams nparams types false` from the stored `ConstantInfo`
      and its stored constructor types, and sends it to `addDecl`.
    * lean4lean's own classifier is not at fault. `ElimNestedInductive` catches
      nesting through `List` *and* through `Array`, as the two controls above
      show.

    Whether `lean4export` ought to emit `Lean.Syntax` is the exporter's business,
    not this project's, and the investigation stopped there. The consequence for
    this project holds regardless of the cause: **goal 1 does not certify
    nested-inductive support, so it cannot be read as certifying that the checker
    accepts what Lean's kernel accepts.** Closing the gap means adding
    nested-inductive tests to the suite, which is a change to the arena rather
    than to this repository.

    This measurement was taken to price one of the three exits from item 11
    above — rejecting nested inductives in the checker. That exit is **dead**,
    but on real-world evidence rather than arena evidence: it would break
    anything importing Lean's own syntax tree, and `Lean4Lean.Replay` on any real
    module would fail immediately.

13. **Guard 3's count over-reports obstacles by an order of magnitude, and cannot
    move for most of them.** Conservative rather than dangerous, but it has been
    read as a progress metric and is not one.

    Guard 3 (`Verify/Guard.lean:182`) classifies a constant as an implementation
    gap when `env.contains (n ++ "_unsafe_rec")`. That test does **not** mean
    `partial`: Lean emits `_unsafe_rec` for *well-founded-compiled* definitions
    too, purely as a compiler artefact. The tell was already in the whitelist —
    `Lean4Lean.TypeChecker.Methods.withFuel` is a plain structural `def` on `Nat`
    whose `WF` lemma is proved by `match n with | 0 | n+1`, and guard 3 flags it.

    What actually blocks reasoning is being `.opaqueInfo` — no body, no equation
    lemmas. Measured over the 22 inductive-side whitelist entries: **2** were
    genuinely opaque (`AddInductive.getElimLevel.loop`,
    `ElimNestedInductive.mkUniqueName.loop`, the only two carrying neither fuel
    nor a `termination_by`); the other 20 already had equation lemmas and unfold
    theorems. Both have since been bounded, so the inductive cone's
    reasoning-blocked count is **0** — while guard 3 still reads 54/54, and can
    only fall if a loop becomes *structurally* recursive, which most of these
    cannot be.

    The guard still does its real job: nothing new and opaque enters
    `addDecl`'s cone without sign-off. `Guard.lean` is frozen and was not
    touched. What should change is the reading — `CLAUDE.md` says "shrinking the
    allowlist is progress", and for this workstream it is not a measure of
    progress at all.

## In the 32 frozen axioms

Not yet audited. `Lean4Lean/Verify/Axioms.lean` asserts 32 unproven facts about
*upstream Lean* functions, and guard 2 whitelists them, so they sit inside
`kernel_sound`'s trusted cone: if one is false the end-to-end theorem is
worthless. An audit is in progress; results in `docs/axiom-audit.md`.

The a-priori risk is concentrated in axioms relating an `@[extern]` or
`@[implemented_by]` function to a pure model of it (which is exactly the gap
those attributes create), axioms about `partial` functions, axioms about data
structures whose statements may quietly assume a well-formedness invariant the
caller has not established, and `Lean.Level.instLawfulBEqLevel`, since asserting
a `LawfulBEq` instance is a strong claim.
