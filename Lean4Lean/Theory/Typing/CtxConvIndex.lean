import Lean4Lean.Theory.Typing.DefInvRefute

/-!
# Context conversion, index by index — the verdict on `PropTypeAgreeN`'s `forallEDF` case

`Theory/Typing/UniqueTypingN.lean` §"Is `PropTypeAgreeN` closable at the index?" claims:

> **`forallEDF`** wants **context conversion at a preserved index** … Its induction drops an
> index exactly as `SubstC` does (the conversion is available at `n+1`, the typing premises
> want it at `n`), so it is in the family refuted in `Theory/Typing/SubstCRefute.lean`, and by
> the arithmetic in `docs/options-circularity-breakers.md` a rule cannot repair it.

This file checks that claim rather than inheriting it, and the verdict is **split**:

* **The mechanism claim is correct.**  Context transport separates into two statements — one
  for typings, one for conversions — and the second one's `appDF`/`beta`/`eta`/`proofIrrel`
  cases need the first at *one index lower* than the conversion they are given.  That drop is
  real (`Stratified`'s conversion rules take their typing premises at `n`, its conclusion at
  `n+1`), and the dropped statement is **false**: `ctxTransportT_drop_false`.

* **The "therefore refuted" conclusion is NOT established, and reads as overstated.**  What
  the family refutes is transport of a **conversion** (`ctxTransportD_one_false`) and transport
  of a typing **across an index drop** (`ctxTransportT_drop_false`).  `CtxConvProp` is transport
  of a **typing at the preserved index**, and at the very witness that refutes the other two it
  **holds**: `witness_transports_typing` machine-checks that the guilty term `cod` is `⊢₁`-typed
  in *both* contexts, because typing at index `n` has `conv` at index `n` and the `bvar` rule's
  mismatch is absorbed there.  So `CtxConvProp` is not refuted by the family; only the
  induction that would prove it is blocked.

* **One obvious repair is vacuous, and that is worth knowing before it is tried**
  (`uniform_index_hypothesis_vacuous`): strengthening the hypothesis to "the domain conversion
  holds at every index `≤ n`" collapses to `A = A'`, because `≡₀` is syntactic equality
  (`IsDefEqN.zero_iff`).  There is no room between "at index `n`" and "syntactically equal".

## Net effect on the route

`PropTypeAgreeN`'s `forallEDF` case is **not** known-unreachable.  `PropTypeAgreeN` is not
known reachable either: the standard induction for `CtxConvProp` is blocked at its `conv` case,
which needs `CtxTransportD` at the preserved index, and that is *false* — so a proof of
`CtxConvProp` must avoid inducting through conversion transport.  The honest status is
**blocked induction, statement open**, which is a strictly weaker claim than the docstring's
and does not warrant abandoning the route.

The two indices are kept separate throughout — `CtxTransportT env U n j` transports a typing at
index `n` along a conversion at index `j` — because every claim in this area turns on which of
the two is meant, and collapsing them is how the overstatement happened.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## The two transport statements, with the two indices separated -/

/-- **Typing transport**: a typing at index `n` survives replacing the head of the context
along a conversion available at index `j`.  `j = n` is the *preserved-index* form (what
`CtxConvProp` is an instance of); `j = n+1` is the *dropped-index* form (what the conversion
rules of `Stratified` hand their typing premises). -/
def CtxTransportT (env : VEnv) (U n j : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A A' e T : VExpr},
    env.IsDefEqN U j Γ A A' → env.HasTypeN U n (A::Γ) e T → env.HasTypeN U n (A'::Γ) e T

/-- **Conversion transport**: the same for a conversion at index `n`.  This is what the `conv`
case of `CtxTransportT`'s induction needs, at `j = n`. -/
def CtxTransportD (env : VEnv) (U n j : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A A' e e' : VExpr},
    env.IsDefEqN U j Γ A A' → env.IsDefEqN U n (A::Γ) e e' → env.IsDefEqN U n (A'::Γ) e e'

/-- `CtxConvProp` is the preserved-index typing transport, restricted to the target
`.sort .zero`.  So anything that refutes `CtxConvProp` refutes `CtxTransportT env U n n`, and
— the direction used below — a witness that fails to refute the latter cannot refute the
former. -/
theorem CtxConvProp.of_ctxTransportT (h : env.CtxTransportT U n n) : env.CtxConvProp U n :=
  fun hA hB => h hA hB

/-! ## Where the content is: `j = 0` is free, and `j = 0` is the *only* free case

Both statements are trivial when the conversion is at index `0`, because `≡₀` is equality.
This pins the vacuity boundary: the first open instance is `j = 1`. -/

theorem ctxTransportT_index_zero : env.CtxTransportT U n 0 := fun h hT =>
  IsDefEqN.zero_iff.1 h ▸ hT

theorem ctxTransportD_index_zero : env.CtxTransportD U n 0 := fun h hD =>
  IsDefEqN.zero_iff.1 h ▸ hD

/-- **The index-uniform repair is vacuous.**  "The domain conversion is available at every
index `≤ n`" is not a hypothesis one can assume in place of the drop: it *is* syntactic
equality, since index `0` is included and `≡₀` is equality.  So the mutual induction
`CtxTransportT n ← CtxTransportD n ← CtxTransportT (n-1)` cannot be repaired by demanding the
conversion uniformly; the drop has to be paid for some other way. -/
theorem uniform_index_hypothesis_vacuous {Γ : List VExpr} {A A' : VExpr}
    (h : ∀ m, m ≤ n → env.IsDefEqN U m Γ A A') : A = A' :=
  IsDefEqN.zero_iff.1 (h 0 (Nat.zero_le _))

/-! ## Why the preserved index behaves differently: the `bvar` case

One lemma explains the whole split.  The only rule whose premise mentions the head of the
context is `bvar`, and at the preserved index its mismatch is repaired **by `conv`, in one
step**, because typing at index `n` may use a conversion at index `n`.  One index down there is
no `conv` to use — `⊢₀` has no conversion at all — which is exactly what
`ctxTransportT_drop_false` records. -/

/-- **The variable transports, at the preserved index, unconditionally.**  Pair this with
`CtxConvIndex.ctxTransportT_drop_false`, which is the same statement one index down and is
false: the difference is that `conv` is available here and not there. -/
theorem bvar_zero_transport (henv : Ordered env) {Γ : List VExpr} {A A' : VExpr}
    (h : env.IsDefEqN U n Γ A A') : env.HasTypeN U n (A'::Γ) (.bvar 0) A.lift :=
  .conv (Stratified.weak henv (IsDefEqN.symm' h)) (.bvar Lookup.zero)

namespace CtxConvIndex
open DefInvRefute

/-! ## 1. Conversion transport at a preserved index is FALSE

`DefInvRefute`'s witness is exactly this statement's counterexample, one index up from where
that file uses it: `dom ≡₁ dom'` in any context, `[dom'] ⊢₁ x ≡ cod` by one `beta` step, and
`[dom] ⊢₁ x ≡ cod` is false because `cod` is not `⊢₀`-typeable there and every `⊢₁` rule that
could move it carries a `⊢₀` premise. -/

/-- **`CtxTransportD ∅ 1 1 1` is false.** -/
theorem ctxTransportD_one_false : ¬ (∅ : VEnv).CtxTransportD 1 1 1 := fun h =>
  bvar_not_conv_cod (h (Γ := []) (IsDefEqN.symm' hdom) bvar_conv_cod_right)

/-! ## 2. Typing transport across an index drop is FALSE

The same witness one index down, at the `bvar` rule itself: the variable is `⊢₀`-typed at
`dom'` in `[dom']` and not in `[dom]`, and the conversion that would fix it lives at `⊢₁`.
This is the drop the conversion rules of `Stratified` impose on their typing premises, and it
is where the mutual induction bottoms out. -/

/-- **`CtxTransportT ∅ 1 0 1` is false** — typing transport at index `0` along a conversion at
index `1`.  This is the residual the `appDF`/`beta`/`eta`/`proofIrrel` cases of
`CtxTransportD ∅ 1 1 1` would consume, so the docstring's *mechanism* claim in
`UniqueTypingN.lean` is confirmed: the induction really does drop an index, and the dropped
statement really is false. -/
theorem ctxTransportT_drop_false : ¬ (∅ : VEnv).CtxTransportT 1 0 1 := fun h =>
  bvar_not_hasType0_left (h (Γ := []) (IsDefEqN.symm' hdom) bvar_hasType0_right)

/-! ## 3. …but typing transport at the *preserved* index is not touched

The guilty term is `cod`.  At index `1` it is typeable in **both** contexts, at the same type:
in `[dom']` directly, and in `[dom]` because the argument position is repaired by `conv` along
`hdom` — a conversion at index `1`, which the typing rules at index `1` may use.  So the
witness supplies no counterexample to `CtxTransportT ∅ 1 1 1`, and hence none to
`CtxConvProp ∅ 1 1`. -/

/-- `[dom'] ⊢₁ cod : dom'` — the inner derivation of `DefInvRefute.piR_type`, named. -/
theorem cod_hasType_right : (∅ : VEnv).HasTypeN 1 1 [dom'] cod dom' :=
  Stratified.app (A := dom') (B := dom')
    (Stratified.lam (dom'_type.mono (Nat.zero_le 1)) (Stratified.bvar Lookup.zero))
    (Stratified.bvar Lookup.zero)

/-- `[dom] ⊢₁ cod : dom'` — **the transport that the refutation of conversion transport does
not obstruct.**  The only difference from `cod_hasType_right` is the `conv` on the argument,
and `conv` is available because the typing rules of `Stratified` do not drop the index. -/
theorem cod_hasType_left : (∅ : VEnv).HasTypeN 1 1 [dom] cod dom' :=
  Stratified.app (A := dom') (B := dom')
    (Stratified.lam (dom'_type.mono (Nat.zero_le 1)) (Stratified.bvar Lookup.zero))
    (Stratified.conv hdom (Stratified.bvar Lookup.zero))

/-- **The split, in one statement.**  At one and the same pair of contexts: the conversion does
not transport, and the typing does.  Reading the first conjunct as evidence against
`CtxConvProp` — which is the second kind of statement — is the overstatement this file
corrects. -/
theorem witness_transports_typing :
    (∅ : VEnv).HasTypeN 1 1 [dom'] cod dom' ∧
    (∅ : VEnv).HasTypeN 1 1 [dom] cod dom' ∧
    ¬ (∅ : VEnv).IsDefEqN 1 1 [dom] (.bvar 0) cod :=
  ⟨cod_hasType_right, cod_hasType_left, bvar_not_conv_cod⟩

/-- And the negative half, stated where a reader of `UniqueTypingN.lean` will look for it:
**nothing here refutes `CtxConvProp`.**  The two refutations above are about the other two
statements, and `CtxConvProp ∅ 1 1` is neither proved nor refuted. -/
theorem verdict :
    ¬ (∅ : VEnv).CtxTransportD 1 1 1 ∧ ¬ (∅ : VEnv).CtxTransportT 1 0 1 ∧
    (∅ : VEnv).HasTypeN 1 1 [dom] cod dom' :=
  ⟨ctxTransportD_one_false, ctxTransportT_drop_false, cod_hasType_left⟩

end CtxConvIndex
end VEnv
end Lean4Lean
