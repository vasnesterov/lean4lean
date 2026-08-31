import Lean4Lean.Theory.Typing.StrengthenNarrow
import Lean4Lean.Theory.Typing.ChurchRosser

/-!
# Entry (2) of the confluence ↔ strengthening cycle: the `extra`-case check obligation

The cycle this file measures is

```
IsDefEqU.weakN_iff  (Theory/Typing/UniqueTyping.lean:187, the hole)
  ← ParRed.weakN_inv / parRedK_weakN_invP  (ChurchRosser.lean:799, KMeasure.lean:737)
  ← the `extra` case of `ParRed`, whose only content is transporting a rule's
    `Pattern.Check.OK` obligations from the larger context to the smaller one.
```

The question this file answers is whether that `extra`-case obligation is *weaker* than the
hole — whether the checks, being pattern-shaped, could descend by a structural argument that
general conversions cannot.

**They cannot: the obligation is not weaker, it is equivalent (§1).**  §2 records what the
restriction to the kernel's actual rule table does and does not buy.  §3 gives the one
reduction that does dodge conversion strengthening entirely — re-deriving the checks from the
redex's typing rather than transporting them — together with the measurement showing that its
only available discharge route is circular, so it is a *deferral* and not an elimination.

## Measurements (recorded 2026-08-31, census baseline 14 holes, unchanged by this file)

`IsDefEqU.weakN_iff` has **12** direct users across `Lean4Lean.*`:
`ConditionallyWHNF.weakN_inv`, `IsDefEq.skips`, `IsDefEq.weakN_iff'`, `IsDefEqU.weak'_iff`,
`KTable.kstep_liftN_inv_stepP`, `NormalEq.weakN_inv_DFC`, `ParRed.weakN_inv`,
`ParRedExt.parRed_beta`, `hasType_app_bvar0`, `parRedK_weakN_invP`, `parRedK_weakN_invPS`,
`VExpr.WF.weakN_iff`.

Per-seed edge counts (a "route" is a direct user of the hole inside the seed's cone):

| seed | cone | routes to the hole |
|---|---|---|
| `ParRed.weakN_inv` (`ChurchRosser.lean:799`) | 3423 | **exactly one**: its own `extra` case |
| `parRedK_weakN_invP` (`KMeasure.lean:737`) | 3872 | four: itself (`extra`), `VExpr.WF.weakN_iff`, `NormalEq.weakN_inv_DFC`, `IsDefEq.weakN_iff'` |

So `ParRed.weakN_inv` really is entry (2) and nothing else — and §1 shows that single edge,
taken uniformly in the pattern, *is* the hole.  `parRedK_weakN_invP` carries three further
edges (the `keta` case's `OnCtx.weakN_inv` route, and entry (1) via `NormalEq.weakN_inv_DFC`),
so closing entry (2) alone does not free it.  Confirmed *not* to reach the hole:
`keta_weakN_invK`, `NormalEq.apply_pat`, `NormalEq.instN`.

Cones relevant to §3's discharge route:

| declaration | cone | reaches `IsDefEqU.weakN_iff` |
|---|---|---|
| `VEnv.patWF` (`PatWFIota.lean:624`) | 3892 | no |
| `VEnv.patWF_iota` | 3843 | no |
| `VEnv.patWF_quot` | 3717 | no |
| `VEnv.patWF_of_wf` (`Verify/Typing/ConstSpineWF.lean:57`) | 4025 | no |
| `VEnv.piInv_axiom` | 3539 | no |
| `VEnv.constApp_inv_of_patWF` (`Verify/Typing/ConstSpine.lean:670`) | 7303 | **yes** |
| `VEnv.constApp_inv_of_wf` | 7465 | **yes** |
| `VEnv.const_app_inv_of_wf` | 7468 | **yes** |

This module's own declarations:

| declaration | cone | reaches the hole | other holes reached |
|---|---|---|---|
| `checkStrengthening_iff_target` (§1) | 790 | no | **none** — fully sorry-free |
| `StrengtheningTarget.patCheckStrengthening` (§2) | 776 | no | none |
| `PatCheckOfTyping.check_descend` (§3) | 3639 | no | `forallE_inv_stratified`, `WF.rigidShapeUniqNS` |

§3's two holes are inherited from `TypingStrengthening.wf_inv`/`onCtx_inv`
(`StrengthenNarrow.lean` §5) and are pre-existing and orthogonal to entry (2).

All measurements use the `deps`/`go`/`cone` walker copied verbatim from
`scripts/hole-cone.lean`.

This module is a leaf that nothing imports, so it is **not** in
`Experimental/ConeJoin.lean`'s import list and is therefore invisible to
`scripts/sorry-census.lean`.  It contains no `sorry`, so that does not hide anything; adding
the import line is the orchestrator's call (this module does not edit shared files).

## Notes about files this module does not own

* `Theory/Typing/KMeasure.lean`'s `parRedK_weakN_invP` has three appeals to the hole, not the
  one its surrounding comments describe.  §3's `PatCheckOfTyping.check_descend` replaces the
  first; `TypingStrengthening.onCtx_inv` (`StrengthenNarrow.lean:355`) replaces the second;
  the third is entry (1) and is out of scope here.
* `Verify/Typing/ConstSpine.lean`'s `constApp_inv_of_patWF` is proved *via confluence*, so it
  is downstream of `ParRed.weakN_inv`.  Any attempt to discharge §3's `PatCheckOfTyping` with
  const-application injectivity is therefore circular.  A non-circular proof would have to
  invert a well-typed ι-redex without Church–Rosser.
-/

namespace Lean4Lean
namespace VEnv

open VExpr

variable {env : VEnv} {U : Nat}

/-! ## 1. The `extra`-case obligation is *equivalent* to the hole

The `extra` case of `ParRed.weakN_inv` needs: given a rule whose `Check` obligations hold in
`Γ'` at *lifted* arguments, the same obligations hold in `Γ` at the unlifted ones.  Naming that:
-/

/-- **The `extra`-case obligation, as a named `Prop`.**  Note that the arguments `m2` are
universally quantified and the check `ck` is arbitrary: this is the obligation *as the
induction presents it*, with no rule-table restriction. -/
def CheckStrengthening (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {p : Pattern} {ck : p.Check}
    {m1 : p.LPath → List VLevel} {m2 : p.Path → VExpr},
    Ctx.LiftN n k Γ Γ' → OnCtx Γ' (env.IsType U) →
    ck.OK (env.IsDefEqU U Γ') m1 (fun x => (m2 x).liftN n k) →
    ck.OK (env.IsDefEqU U Γ) m1 m2

/-- **Task 0, the easy half.**  `CheckStrengthening` follows from the hole, uniformly in the
pattern, by `Pattern.Check.OK.map`: the two endpoints of every `.defeq` clause are *literally*
lifts (`Pattern.RHS.liftN_apply`), and the `.level` clauses do not mention the context at all.

This is also the precise sense in which Task 0's hoped-for structural argument is unavailable:
`Check.OK.map` **is** the induction on `Check`, it is already sorry-free, and it reduces the
whole obligation to one conversion-strengthening instance per `.defeq` clause.  Nothing
escapes the image of the lift; there is no syntactic residue to exploit. -/
theorem StrengtheningTarget.checkStrengthening (H : StrengtheningTarget env U) :
    CheckStrengthening env U := by
  intro n k Γ Γ' p ck m1 m2 W hΓ' h
  refine h.map fun a b hab => ?_
  rw [← Pattern.RHS.liftN_apply, ← Pattern.RHS.liftN_apply] at hab
  exact H W hΓ' hab

/-! ### The witness for the converse

A two-argument pattern with a single var-var `.defeq` clause.  Its check is
`fun m2 => defeq (m2 none) (m2 (some none))`, so instantiating `m2` at an arbitrary pair of
expressions recovers the hole's statement verbatim. -/

/-- `f a b` — the smallest pattern with two argument slots. -/
def witPat : Pattern := .var (.var (.const .anonymous))

/-- `a ≡ b`: one `.defeq` clause between the two argument slots of `witPat`.  This is exactly
the *shape* every `.defeq` clause of the kernel's ι- and quotient-rules has (see §2). -/
def witCheck : witPat.Check := .defeq (.var none) (.var (some none)) .true

/-- The argument assignment sending the two slots to `e1` and `e2`. -/
def witMap (e1 e2 : VExpr) : witPat.Path → VExpr
  | none => e1
  | some none => e2

theorem witCheck_OK {df : VExpr → VExpr → Prop} {m1 : witPat.LPath → List VLevel} {e1 e2} :
    witCheck.OK df m1 (witMap e1 e2) ↔ df e1 e2 := by
  simp [witCheck, Pattern.Check.OK, Pattern.RHS.apply, witMap]

theorem witMap_liftN {e1 e2 : VExpr} {n k : Nat} :
    (fun x => (witMap e1 e2 x).liftN n k) = witMap (e1.liftN n k) (e2.liftN n k) := by
  funext x; match x with | none => rfl | some none => rfl

/-- **Task 0, the decisive half: the converse.**  `CheckStrengthening` implies the hole.

So the `extra`-case obligation is not a weakening of `IsDefEqU.weakN_iff` in any degree: the
two are interderivable.  No induction on `Pattern.Check`, no injectivity of `liftN`, and no
cleverness about `Pattern.RHS` can close entry (2)'s `extra` case; the case *is* the hole. -/
theorem CheckStrengthening.target (H : CheckStrengthening env U) :
    StrengtheningTarget env U := by
  intro n k Γ Γ' e1 e2 W hΓ' h
  have := @H n k Γ Γ' witPat witCheck (fun _ => []) (witMap e1 e2) W hΓ' ?_
  · exact witCheck_OK.1 this
  · rw [witMap_liftN]; exact witCheck_OK.2 h

/-- The equivalence, stated as such. -/
theorem checkStrengthening_iff_target :
    CheckStrengthening env U ↔ StrengtheningTarget env U :=
  ⟨CheckStrengthening.target, StrengtheningTarget.checkStrengthening⟩

/-! ## 2. Restricting to the kernel's actual rule table

§1's witness pattern `witPat = .varN (.const _) 2` is not of the form `Params.pat_simple`
admits (`SimplePattern.toPattern` produces either `.const c` or
`.app (.varN (.const r) m) (.varN (.const c) n)`), so §1's equivalence does *not* say that the
obligation restricted to a fixed rule table is equivalent to the hole.  That restricted form is
genuinely narrower in scope: -/

/-- The `extra`-case obligation restricted to the patterns a given rule table registers. -/
def PatCheckStrengthening (env : VEnv) (U : Nat)
    (Pat : (p : Pattern) → p.RHS × p.Check → Prop) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {p : Pattern} {r : p.RHS × p.Check}
    {m1 : p.LPath → List VLevel} {m2 : p.Path → VExpr},
    Pat p r → Ctx.LiftN n k Γ Γ' → OnCtx Γ' (env.IsType U) →
    r.2.OK (env.IsDefEqU U Γ') m1 (fun x => (m2 x).liftN n k) →
    r.2.OK (env.IsDefEqU U Γ) m1 m2

theorem StrengtheningTarget.patCheckStrengthening {Pat} (H : StrengtheningTarget env U) :
    PatCheckStrengthening env U Pat :=
  fun _ W hΓ' h => H.checkStrengthening W hΓ' h

/-- Where the restriction *does* fire, as a sanity check: a rule whose check is `.true`
(every δ-rule; `PatternRules.lean:270`'s `Pat.delta`) contributes nothing. -/
theorem Pattern.Check.true_OK {p : Pattern} {df m1 m2} :
    (Pattern.Check.true (p := p)).OK df m1 m2 := trivial

/-! ### Non-vacuity of the restricted form

The restricted obligation is **not** vacuous, and the witness does not even need an inductive
declaration to be present in the environment: the quotient rule is always registered.

`PatternRules.lean:265` defines
`quotCheck = iotaCheck ``Quot.lift ``Quot.mk 5 3 2 5 [] [(0,0)]`, whose `np` argument is `2`.
`PatternDecode.lean`'s `iotaParamsCheck` emits one `.defeq (.var (Sum.inl x)) (.var (Sum.inr y))`
clause per parameter, so `quotCheck` carries two var-var `.defeq` clauses — the agreement of
`Quot.lift`'s `α` and `r` with `Quot.mk`'s.  Each is an instance of §1's `witCheck` shape with
the two slots pinned to arguments of a matched redex.

That pinning is the only thing the restriction buys, and it buys nothing directly: by
`Pattern.matches_liftN`, the matched arguments of a lifted redex are themselves lifts, so the
clause's endpoints are again `(·).liftN n k` of arbitrary expressions.  Which is why §3 does not
try to transport the checks at all.
-/

/-! ## 3. The reroute that avoids conversion strengthening — and why it is circular today

Transporting the checks downward is hopeless (§1).  But the `extra` case does not actually need
transport: it needs the checks *to hold* in `Γ`.  And the checks of a registered rule are
determined by the redex, because a rule only fires on a term it matches, and a well-typed
matching term already forces the agreements the check asserts (that is precisely what
`Params.pat_wf`'s converse direction is about).  Naming that: -/

/-- **The rule table's checks are consequences of typing.**  For every registered rule and
every well-typed term it matches, the rule's `Check` obligations hold.

This is a statement about the *rule table*, not about conversion: no lifting, no two contexts.
It is trivially true for δ-rules (`Check.true`), and for ι- and quotient-rules it is the
assertion that a well-typed redex has matching parameters, indices and levels between its
recursor spine and its constructor spine. -/
def PatCheckOfTyping (env : VEnv) (U : Nat)
    (Pat : (p : Pattern) → p.RHS × p.Check → Prop) : Prop :=
  ∀ {Γ : List VExpr} {p : Pattern} {r : p.RHS × p.Check} {e : VExpr}
    {m1 : p.LPath → List VLevel} {m2 : p.Path → VExpr},
    Pat p r → OnCtx Γ (env.IsType U) → p.Matches e m1 m2 → VExpr.WF env U Γ e →
    r.2.OK (env.IsDefEqU U Γ) m1 m2

variable! (henv : VEnv.WF env) in
/-- **The `extra` case, discharged without any conversion strengthening.**

Note what is *absent* from the hypotheses: the upstairs check `r.2.OK (IsDefEqU U Γ') m1 _` is
not used at all.  The checks are re-derived downstairs from the redex's typing, and the only
strengthening consumed is `TypingStrengthening` — the typing half, which
`StrengthenNarrow.lean` §5 shows carries no `trans` residual.

So entry (2)'s own edge to the hole is replaceable by `PatCheckOfTyping` + the typing half. -/
theorem PatCheckOfTyping.check_descend {Pat} {n k : Nat} {Γ Γ' : List VExpr}
    {p : Pattern} {r : p.RHS × p.Check} {e : VExpr}
    {m1 : p.LPath → List VLevel} {m2 : p.Path → VExpr}
    (H : PatCheckOfTyping env U Pat) (HT : TypingStrengthening env U)
    (hp : Pat p r) (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (hm : p.Matches e m1 m2) (hT : VExpr.WF env U Γ' (e.liftN n k)) :
    r.2.OK (env.IsDefEqU U Γ) m1 m2 :=
  H hp (HT.onCtx_inv henv W hΓ') hm (HT.wf_inv henv W hΓ' hT)

/-- The same, taking the match upstairs (the shape `ParRed.weakN_inv`'s `extra` case actually
has, before it inverts `Pattern.matches_liftN`). -/
theorem PatCheckOfTyping.check_descend' {Pat} {n k : Nat} {Γ Γ' : List VExpr}
    {p : Pattern} {r : p.RHS × p.Check} {e : VExpr}
    {m1 : p.LPath → List VLevel} {m2' : p.Path → VExpr}
    (henv : VEnv.WF env) (H : PatCheckOfTyping env U Pat) (HT : TypingStrengthening env U)
    (hp : Pat p r) (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U))
    (hm : p.Matches (e.liftN n k) m1 m2') (hT : VExpr.WF env U Γ' (e.liftN n k)) :
    ∃ m2, (∀ x, m2' x = (m2 x).liftN n k) ∧ r.2.OK (env.IsDefEqU U Γ) m1 m2 :=
  have ⟨m2, hm₀, heq⟩ := Pattern.matches_liftN.1 hm
  ⟨m2, heq, H.check_descend henv HT hp W hΓ' hm₀ hT⟩

/-! ### Verdict on the reroute

`PatCheckOfTyping` is *true* for the kernel's table, but the only proof available in this tree
goes through `constApp_inv_of_wf` (`Verify/Typing/ConstSpineWF.lean:61`), which is proved by
Church–Rosser and hence sits downstream of `ParRed.weakN_inv` — the very theorem entry (2) is
trying to prove.  The cone table in the module docstring records this: `patWF` and
`patWF_of_wf` are clean, `constApp_inv_of_patWF` and everything built on it are not.

Therefore:

* As a *reduction*, §3 is correct and useful: it shows entry (2)'s `extra` case needs only a
  rule-table fact plus the typing half, never the narrow `trans` residual.
* As a *closure*, it is a deferral.  Adding `PatCheckOfTyping` as a hypothesis moves the
  obligation; discharging it with today's machinery reintroduces the cycle.  A genuine
  closure needs const-application injectivity for a well-typed redex proved *without*
  confluence.
-/

/-! ## 4. Verdict on the proposed `Params` field

The proposal under evaluation was to add a `Params` field asserting *"the rule table's checks
are strengthening-stable"*.  Written out at `Params`'s own notation
(`ChurchRosser.lean:12`), the field would be

```
pat_check_strengthen :
  Pat p r → Ctx.LiftN n k Γ Γ' → OnCtx Γ' (IsType env univs) →
  r.2.OK (IsDefEqU env univs Γ') m1 (fun x => (m2 x).liftN n k) →
  r.2.OK (IsDefEqU env univs Γ) m1 m2
```

i.e. `PatCheckStrengthening Params.env Params.univs Params.Pat` (§2).  **This field should not
be added.**  Reasons, in order of weight:

1. *It is not dischargeable at the canonical table.*  `paramsOfWF` (`ParamsBuild.lean:52`) sets
   `Pat := Pat env`, so the field would have to be proved for `Pat.delta`, `Pat.iota` and
   `Pat.quot` (`PatternRules.lean:270`).  δ is free (`Check.true`).  ι and quot are not: their
   `.defeq` clauses relate arguments of the matched redex, and by `Pattern.matches_liftN` the
   arguments of a *lifted* redex are exactly the lifts of the arguments of the unlifted one —
   arbitrary expressions, with no extra structure.  So the clause obligation is a bare instance
   of `StrengtheningTarget`, and no route to it exists in the tree.  The field would sit
   undischarged in `paramsOfWF`, i.e. as a new `sorry`.

2. *It would push the census up, without freeing the hole.*  `IsDefEqU.weakN_iff` has 12 direct
   users; `ParRed.weakN_inv` is one of them.  Even a successful entry (2) leaves the other
   eleven, so the hole survives and the census gains one.  Net: 14 → 15.

3. *It is the wrong shape.*  §1 proves that, taken uniformly in the pattern, this obligation is
   *equivalent* to the hole.  A `Params` field is by construction quantified over `p` and `r`
   subject only to `Pat p r`; the only thing standing between it and §1's equivalence is the
   contingent shape of the current table.  A field that is provably the hole in disguise as soon
   as the table admits a second argument slot with an unconstrained check is not a good
   abstraction boundary.

4. *Cost to existing instances.*  `Params` is constructed at `ParamsBuild.lean:52` and `:105`,
   `PatWF.lean:402`, `PatWFIota.lean:638`, and `ParamsWitness.lean:132`/`:217`.  Only the last
   is hand-built, over `CycleConv.propLoopEnv`, whose table is δ-only, so it would discharge the
   field trivially — that objection is *not* fatal.  But `WeakNormRefute.not_forall_weakNorm`
   quantifies over all `Params`, and every added field weakens that refutation's statement.

### The field that would be worth adding, if it could be discharged

`PatCheckOfTyping Params.env Params.univs Params.Pat` (§3) — as `pat_check_of_typing`, sitting
directly beside `pat_wf`, of which it is the converse:

```
pat_check_of_typing :
  Pat p r → OnCtx Γ (IsType env univs) → p.Matches e m1 m2 →
  VExpr.WF env univs Γ e → r.2.OK (IsDefEqU env univs Γ) m1 m2
```

It has none of objections 1–3's shape problems: no lifting, one context, and it is a statement
purely about the rule table.  By `check_descend` it discharges entry (2)'s `extra` case using
only the *typing* half of strengthening.

What discharging it in `paramsOfWF` would take: for `Pat.delta`, nothing (`Check.true`).  For
`Pat.iota` and `Pat.quot`, it is exactly the statement that a well-typed redex
`rec.{ls} pars idxs … (ctor.{ls'} pars' …)` has `ls ≈ ls'` and `pars ≡ pars'` — that is,
`const_app_inv` at the redex's major premise.  That is available
(`Verify/Typing/ConstSpineWF.lean:61`) but **is proved by Church–Rosser**, hence downstream of
`ParRed.weakN_inv`: see the cone table above, where `patWF`/`patWF_of_wf` are clean and
`constApp_inv_of_patWF` is not.  Using it here closes the circle rather than breaking it.

**Conclusion.**  Drop the proposed field.  Do not replace it with `pat_check_of_typing` either,
until const-application injectivity for a well-typed redex is available without confluence:
today both fields would be undischarged obligations and the census would rise from 14 to 15.
The useful output of this file is §1 — entry (2) is *not* an independent attack surface on
`IsDefEqU.weakN_iff`, it is the hole restated — plus §3's identification of the one fact
(`PatCheckOfTyping`) whose non-circular proof would make it one.
-/

end VEnv
end Lean4Lean
