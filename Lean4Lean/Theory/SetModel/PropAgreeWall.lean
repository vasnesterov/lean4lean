import Lean4Lean.Theory.SetModel.PreludeOracle
import Lean4Lean.Theory.Typing.PropShadow
import Lean4Lean.Theory.Typing.UniqueTypingN

/-!
# `PropTypeAgree preludeEnv 0`: is it the injectivity wall?

`docs/handoff-setmodel.md` §10.2 reduced the whole `.induct`-oracle corner to a single
statement: `InductOracleOK` is quantified over `L : PropSplit envF nv`, nothing in the tree
constructs a `PropSplit`, and `nonempty_propSplit_preludeEnv_iff` pins that to
`PropUniq preludeEnv 0 ∧ PropTypeAgree preludeEnv 0` with `PropUniq` free where it is
consumed.  §7.6 says `PropTypeAgree 0` is irreducible and not to be attacked; §10.9 item 1
says to pick it up because §10.3 removed the level-layer obstruction at `nv = 0`.

**The answer, and it is not either of those.**  `PropTypeAgree env 0` splits, cleanly, into
two pieces that live in different places:

1. the **context-guarded** statement `PropTypeAgreeOnCtx env 0`, and
2. the **context guard itself** — `PropTypeAgree` quantifies over every `Γ`, including
   contexts whose entries are not types.

Piece (1) has **two independent routes**, and only one of them touches the injectivity
corner:

* `NotProofNoModel.WF.propTypeAgreeOn` at `preludeEnv_WF` — a theorem, whose hole cone is
  **exactly one** sorry-carrying declaration, `VEnv.IsDefEqU.forallE_inv_stratified`
  (measured, not read: a forward cone walk over type-and-value dependencies).  So on this
  route the guarded import at `preludeEnv` *is* gated on one of the four named holes.
* `propTypeAgreeOnCtx_of_stratifiedN` below — **new, and `sorryAx`-free**: the guarded
  import at `nv = 0` follows from the *syntactic* stream's own two stratified statements,
  `VEnv.PropTypeAgreeN env 0 n` and `VEnv.PropUniqN env 0 n`, and nothing else.  No
  `forallE_inv_stratified`, no `rigidShapeUniq`, no `weakN_iff`, no `descend`.

So **piece (1) is not gated on the injectivity corner**: it has an escape through
`Theory/Typing/PropConv.lean` + `Theory/Typing/PropShadow.lean`, which is where the other
stream is already working.  §7.6's "no choice of predicate removes it" is right about
`PropSplit`'s *fields*; it is wrong as a claim that the statement has only the one route.

The `nv = 0` restriction in that route is **load-bearing, not cosmetic**, and this is
`handoff-setmodel.md` §10.3 doing real work rather than correcting a docstring: the model's
`PropTypeAgree` is pointwise in `ls` and the stratified statements are `≈ .zero`-shaped, and
those two agree **only** at `nv = 0` (`NEAudit.equivZero_iff_eval_zero`;
`NotProofNoModel.propAgree_pointwise_not_from_equivZero` refutes the general case at
`WF 2`).  `PropTypeAgreeInput` is `PropTypeAgree env 0`, so the one instance H2 consumes is
the one instance where the composition is legal.

Piece (2) is the part with no route at all, and it is **shared by both routes to (1)**:
the only bridge from unstratified `HasType` to `HasTypeN` is
`VEnv.HasType.stratifyN` (`Theory/Typing/Stratified.lean`, `sorryAx`-free), and it takes
`OnCtx Γ (env.IsType U)` because `IsDefEq.strong` does — `CtxStrong` *is* "every entry is a
type", by definition.  `WF.propTypeAgreeOn` takes the same guard for the same reason.
So neither route reaches a junk context, and §4 below records what that costs.

## A correction to `NotProofNoModel.lean` §5, machine-checked here

That section says the guarded-to-unguarded gap "is a *strengthening* statement … and
strengthening is `IsDefEqU.weakN_iff`".  **`weakN_iff` does not supply it.**  `weakN_iff` is
stated over `Ctx.LiftN n k Γ Γ'` at a *lifted* term, so the entries it removes are exactly the
ones the derivation does not mention.  A junk entry that is **looked up** is outside its
reach, and §4's `hasType_junk_lookup` exhibits one at every environment.  The bridge
`propTypeAgree_of_onCtx_of_strengthen` asks for something strictly stronger than `weakN_iff`:
replacement of junk entries, not deletion of unused ones.

**Consequence for the wall question.**  `PropTypeAgree preludeEnv 0` is *not* reducible to
the four holes gating `Bridge.kernel_sound_of`.  It reduces to
`forallE_inv_stratified` **plus** an unnamed context-replacement statement, or to
`PropTypeAgreeN ∧ PropUniqN` **plus** the same statement.  The context guard is the piece
that is nobody's target, and it is cheaper to remove from `PropSplit` than to prove: §5 of
`NotProofNoModel.lean` prices that repair at 64 call sites, and with it done the model's whole
syntactic import is either of the two routes above.

## Nothing here is claimed refuted

`PropTypeAgree preludeEnv 0` is **not** refuted, and the section below does not try: the
junk-context witnesses show the extra quantifier range is inhabited (so the gap is not
vacuous), not that the statement fails on it.  A refutation would need a term with two
sort-typed types of differing propositionhood, which by `IsDefEq`'s only retyping rule
(`defeqDF`, which converts *at a sort*) is a failure of `PropUniq` or of `PropConvInv` — i.e.
the same content, one level in.  Flagged as an unproved negative per
`docs/vacuity-ledger.md` §0 kind 4.
-/

namespace Lean4Lean
namespace SetModel
namespace PropAgreeWall

open SetModel.NEAudit

/-! ## 1. Route A: the guarded import at `preludeEnv`, unconditionally

Both of these are `WF.propTypeAgreeOn` / `WF.propUniqOn` at `PreludeWitness.preludeEnv_WF`.
They are statements *at a named environment* with no hypotheses left, and their hole cone is
measured (module docstring) at exactly `IsDefEqU.forallE_inv_stratified`. -/

/-- **The guarded model import, at the witness environment, with nothing assumed.** -/
theorem preludeEnv_propTypeAgreeOnCtx : preludeEnv.PropTypeAgreeOnCtx 0 :=
  VEnv.WF.propTypeAgreeOn preludeEnv_WF

/-- The companion. -/
theorem preludeEnv_propUniqOnCtx : preludeEnv.PropUniqOnCtx 0 :=
  VEnv.WF.propUniqOn preludeEnv_WF

/-! ## 2. Route B: the same statement from the *stratified* side, `sorryAx`-free

`Theory/Typing/PropConv.lean` and `Theory/Typing/PropShadow.lean` develop `PropTypeAgreeN`
and `PropUniqN` — the index-relativised forms — and neither file mentions the model.
`NotProofNoModel.lean` §6 records that the two shapes "do not compose"; that is a statement
about `nv ≥ 2`.  At `nv = 0` they do, and this is the composition. -/

variable {env : VEnv}

/-- **The guarded model import from the syntactic stream's own targets.**

Three ingredients, no holes:

* `VEnv.HasType.stratifyN` lands each of the four unstratified premises at some index
  (`Theory/Typing/Stratified.lean`, reference basics (3)/(4)) — this is the bridge
  `handoff-setmodel.md` §10.9 asks for, and it already exists;
* `PropTypeAgreeN` at the common index carries `IsPropN Γ A` to `IsPropN Γ A'`;
* `PropUniqN` reads the level back off `A'`'s two sort typings.

The `.conv (.sortDF …)` step is why the index is `N+1`: `Stratified.sortDF` concludes one
index up, and `Stratified.conv` wants both premises at the same index.  `Stratified.mono`
pays for that with no hypothesis.

**`nv = 0` is essential.**  `equivZero_iff_eval_zero` is what turns the pointwise conclusion
into the `≈ .zero` shape, and it needs `u.WF 0`; at `nv ≥ 2` the step is refuted
(`NotProofNoModel.propAgree_pointwise_not_from_equivZero`).  `PropTypeAgreeInput` is at
`nv = 0`, so this is exactly the instance H2 consumes.

Hypotheses are `∀ n` rather than "at some n" deliberately: the index is produced by
`stratifyN` from the caller's derivations and is not under our control. -/
theorem propTypeAgreeOnCtx_of_stratifiedN (henv : VEnv.Ordered env)
    (pta : ∀ n, env.PropTypeAgreeN 0 n) (pun : ∀ n, env.PropUniqN 0 n) :
    env.PropTypeAgreeOnCtx 0 := by
  intro Γ e A A' u u' ls hΓ hu hu' he he' hA hA'
  rw [← equivZero_iff_eval_zero hu ls, ← equivZero_iff_eval_zero hu' ls]
  obtain ⟨n₁, sHe⟩ := he.stratifyN henv hΓ
  obtain ⟨n₂, sHe'⟩ := he'.stratifyN henv hΓ
  obtain ⟨n₃, sHA⟩ := hA.stratifyN henv hΓ
  obtain ⟨n₄, sHA'⟩ := hA'.stratifyN henv hΓ
  have hrefl : (VLevel.zero : VLevel) ≈ (VLevel.zero : VLevel) := VLevel.equiv_def.2 fun _ => rfl
  set N := max (max n₁ n₂) (max n₃ n₄) with hN
  have He : env.HasTypeN 0 (N+1) Γ e A := sHe.mono (by omega)
  have He' : env.HasTypeN 0 (N+1) Γ e A' := sHe'.mono (by omega)
  have HA : env.HasTypeN 0 (N+1) Γ A (.sort u) := sHA.mono (by omega)
  have HA' : env.HasTypeN 0 (N+1) Γ A' (.sort u') := sHA'.mono (by omega)
  constructor
  · intro hz
    have hpA : env.HasTypeN 0 (N+1) Γ A (.sort .zero) :=
      .conv (.sortDF hu trivial hz) HA
    exact (pun (N+1) (pta (N+1) He He' hpA) HA').1 hrefl
  · intro hz
    have hpA' : env.HasTypeN 0 (N+1) Γ A' (.sort .zero) :=
      .conv (.sortDF hu' trivial hz) HA'
    exact (pun (N+1) (pta (N+1) He' He hpA') HA).1 hrefl

/-! ### Anti-vacuity for route B's hypotheses

`docs/vacuity-ledger.md` §0 asks for the hypotheses to be instantiated before a reduction is
reported.  Both of route B's inputs hold **at the base index, at every environment and with no
hypothesis at all**, through `VEnv.HasTypeN.uniq_zero` (`≡₀` is syntactic equality, so a
term's index-`0` types are syntactically equal).  So the reduction is not a statement about an
empty class of inputs.

*What this does not show*, and the distinction is the one `docs/vacuity-ledger.md` exists to
keep: that `∀ n` holds anywhere.  `stratifyN` produces the index from the caller's derivation
and it is not `0`, so the base index does not discharge route B — it only certifies that its
hypotheses are about something.  The `∀ n` form is `Theory/Typing/PropConv.lean`'s and
`Theory/Typing/PropShadow.lean`'s open target, and route B is the statement that closing it
closes the model's import too. -/

/-- `PropUniqN` at the base index, unconditionally: index-`0` types are syntactically equal. -/
theorem propUniqN_zero : env.PropUniqN 0 0 := by
  intro Γ A u v h1 h2
  cases VExpr.sort.inj (VEnv.HasTypeN.uniq_zero h1 h2)
  exact Iff.rfl

/-- `PropTypeAgreeN` at the base index, unconditionally. -/
theorem propTypeAgreeN_zero : env.PropTypeAgreeN 0 0 := by
  intro Γ e A A' h1 h2 hp
  cases VEnv.HasTypeN.uniq_zero h1 h2
  exact hp

/-- Route B at the witness environment. -/
theorem preludeEnv_propTypeAgreeOnCtx_of_stratifiedN
    (pta : ∀ n, preludeEnv.PropTypeAgreeN 0 n) (pun : ∀ n, preludeEnv.PropUniqN 0 n) :
    preludeEnv.PropTypeAgreeOnCtx 0 :=
  propTypeAgreeOnCtx_of_stratifiedN preludeEnv_ordered pta pun

/-! ## 3. The residual, at the named environment

`propTypeAgree_of_onCtx_of_strengthen` (`NotProofNoModel.lean` §5) names the gap as a
hypothesis.  With §1 the guarded half is discharged at `preludeEnv`, so the residual of
`PropTypeAgree preludeEnv 0` is **exactly** that one hypothesis — and by
`nonempty_propSplit_preludeEnv_of_propTypeAgree` so is the inhabitation of the parameter the
whole `.induct` corner is quantified over. -/

/-- The context-replacement statement, at the witness environment.  Named so that the
residual is a single object rather than a paragraph. -/
def CtxReplace (env : VEnv) (nv : ℕ) : Prop :=
  ∀ {Γ : List VExpr} {e A : VExpr}, env.HasType nv Γ e A →
    ∃ Γ' : List VExpr, OnCtx Γ' (env.IsType nv) ∧
      ∀ {e' A' : VExpr}, env.HasType nv Γ e' A' ↔ env.HasType nv Γ' e' A'

/-- **`PropTypeAgree preludeEnv 0` from the context guard alone.** -/
theorem preludeEnv_propTypeAgree_of_ctxReplace (h : CtxReplace preludeEnv 0) :
    preludeEnv.PropTypeAgree 0 :=
  VEnv.propTypeAgree_of_onCtx_of_strengthen preludeEnv_propTypeAgreeOnCtx h

/-- **…and hence the parameter is inhabited from the context guard alone**, given the goal's
own inhabitant of `∀ p : Prop, p` (§7.6's last bullet: `kernel_sound` is proved by refuting
"the kernel accepts a proof of `False`", so `hf` is free where the reduction is consumed). -/
theorem nonempty_propSplit_preludeEnv_of_ctxReplace (h : CtxReplace preludeEnv 0)
    (hf : ∃ e, preludeEnv.HasType 0 [] e falseProp) :
    Nonempty (PropSplit preludeEnv 0) :=
  nonempty_propSplit_preludeEnv_of_propTypeAgree
    (preludeEnv_propTypeAgree_of_ctxReplace h) hf

/-- The same, with route B's inputs in place of route A's — so the *whole* reduction avoids
all four of the holes gating `Bridge.kernel_sound_of`. -/
theorem nonempty_propSplit_preludeEnv_of_stratifiedN (h : CtxReplace preludeEnv 0)
    (pta : ∀ n, preludeEnv.PropTypeAgreeN 0 n) (pun : ∀ n, preludeEnv.PropUniqN 0 n)
    (hf : ∃ e, preludeEnv.HasType 0 [] e falseProp) :
    Nonempty (PropSplit preludeEnv 0) :=
  nonempty_propSplit_preludeEnv_of_propTypeAgree
    (VEnv.propTypeAgree_of_onCtx_of_strengthen
      (preludeEnv_propTypeAgreeOnCtx_of_stratifiedN pta pun) h) hf

/-! ## 4. The gap is not vacuous, and `weakN_iff` does not close it

Anti-vacuity in the direction `docs/vacuity-ledger.md` §0's seventh blindness asks for:
instantiate at the degenerate instance and check the hypotheses are satisfiable.  Here the
"degenerate instance" is the *junk* context, i.e. the part of `PropTypeAgree`'s quantifier
range that `PropTypeAgreeOnCtx` does not cover.

* `not_onCtx_junk`: `[.bvar 0]` is not an `OnCtx` context, at **every** `Ordered`
  environment — `.bvar 0` is not closed at length `0`, so it inhabits no sort in `[]`.
* `hasType_junk_sort`: yet typing is derivable there, so the extra range is inhabited.
* `hasType_junk_lookup`: and the junk entry is **looked up**, by a derivation whose subject
  is `.bvar 0`.  That is the witness that puts the gap outside `IsDefEqU.weakN_iff`: that
  lemma relates a *lifted* term in the bigger context to the term in the smaller one, so the
  entries it deletes are exactly those the derivation never mentions. -/

/-- `.bvar 0` inhabits no sort in the empty context: it is not `ClosedN 0`. -/
theorem not_isType_bvar (henv : VEnv.Ordered env) : ¬ env.IsType 0 [] (.bvar 0) := by
  rintro ⟨u, h⟩
  exact absurd (VEnv.IsDefEq.closedN henv h trivial) (by simp [VExpr.ClosedN])

/-- A junk context, at every `Ordered` environment. -/
theorem not_onCtx_junk (henv : VEnv.Ordered env) :
    ¬ OnCtx [(.bvar 0 : VExpr)] (env.IsType 0) := fun h => not_isType_bvar henv h.2

/-- Typing is derivable in it, so `PropTypeAgree`'s extra quantifier range is **inhabited**
and the guarded-to-unguarded gap is not vacuous. -/
theorem hasType_junk_sort : env.HasType 0 [(.bvar 0 : VExpr)] (.sort .zero) (.sort (.succ .zero)) :=
  VEnv.HasType.sort trivial

/-- And the junk entry is *looked up* — the witness that `weakN_iff` cannot delete it. -/
theorem hasType_junk_lookup : env.HasType 0 [(.bvar 0 : VExpr)] (.bvar 0) (.bvar 1) :=
  VEnv.HasType.bvar Lookup.zero

/-! ## 5. The bridge §10.9 asks for: audit

§10.9 item 1 names the remaining bridge as `HasTypeN U n` ↔ `HasType 0` and says to check
whether `Theory/Typing` has it.  It has the direction that is needed, and not the other:

* `→` (unstratified to stratified, which is what routes A and B both use):
  `VEnv.HasType.stratifyN`, `sorryAx`-free, **with** `Ordered env` and
  `OnCtx Γ (env.IsType U)`.  Restated here at `preludeEnv` so the `Ordered` half is
  discharged and the `OnCtx` half is visible.
* `←` (stratified to unstratified): **absent, deliberately.**
  `Theory/Typing/Stratified.lean`'s own docstring says it "is *not* proved here and is not
  needed", because `IsDefEqN`'s `conv` rule is three-place while `IsDefEq.defeqDF` demands a
  type, so it needs `IsDefEq.uniq`.  Route B does not use it. -/

theorem stratifyN_at_preludeEnv {Γ : List VExpr} {e A : VExpr}
    (hΓ : OnCtx Γ (preludeEnv.IsType 0)) (H : preludeEnv.HasType 0 Γ e A) :
    ∃ n, preludeEnv.HasTypeN 0 n Γ e A :=
  H.stratifyN preludeEnv_ordered hΓ

end PropAgreeWall
end SetModel
end Lean4Lean

/-! ## Axiom census -/

#print axioms Lean4Lean.SetModel.PropAgreeWall.preludeEnv_propTypeAgreeOnCtx
#print axioms Lean4Lean.SetModel.PropAgreeWall.preludeEnv_propUniqOnCtx
#print axioms Lean4Lean.SetModel.PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN
#print axioms Lean4Lean.SetModel.PropAgreeWall.propUniqN_zero
#print axioms Lean4Lean.SetModel.PropAgreeWall.propTypeAgreeN_zero
#print axioms Lean4Lean.SetModel.PropAgreeWall.preludeEnv_propTypeAgreeOnCtx_of_stratifiedN
#print axioms Lean4Lean.SetModel.PropAgreeWall.preludeEnv_propTypeAgree_of_ctxReplace
#print axioms Lean4Lean.SetModel.PropAgreeWall.nonempty_propSplit_preludeEnv_of_ctxReplace
#print axioms Lean4Lean.SetModel.PropAgreeWall.nonempty_propSplit_preludeEnv_of_stratifiedN
#print axioms Lean4Lean.SetModel.PropAgreeWall.not_isType_bvar
#print axioms Lean4Lean.SetModel.PropAgreeWall.not_onCtx_junk
#print axioms Lean4Lean.SetModel.PropAgreeWall.hasType_junk_sort
#print axioms Lean4Lean.SetModel.PropAgreeWall.hasType_junk_lookup
#print axioms Lean4Lean.SetModel.PropAgreeWall.stratifyN_at_preludeEnv
