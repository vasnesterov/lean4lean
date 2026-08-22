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
