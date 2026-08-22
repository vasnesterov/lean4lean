# Bugs found as a result of formalization

## In Lean's own kernel

* https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Soundness.20bug.3A.20hasLooseBVars.20is.20not.20conservative/near/521286338
* https://github.com/leanprover/lean4/issues/10475
* https://github.com/leanprover/lean4/issues/10511

Nothing new here from the `kernel_sound` work so far. Three pieces of upstream
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
   whose type mentions constants absent from the environment. **Open**; whether
   `addDecl` as a whole accepts it, or `checkConstantVal` rejects it immediately
   afterwards, is being confirmed by running it.

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
