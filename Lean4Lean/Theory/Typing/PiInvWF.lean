import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.MutualDefUnsound

/-!
# `VEnv.PiInv` at `VEnv.WF`: what the environment class permits, and the one route in

`docs/handoff-injcensus.md` §V6 leaves `VEnv.PiInv` (`Theory/Typing/Injectivity.lean:347`) as the
one member of `RigidShapeUniqNS` with **no** `Ordered`-level insufficiency witness, and therefore
the one whose environment requirement is unmeasured.  Every refutation on that front is at
`Ordered`, and each proves its own witness lies outside `VEnv.WF`
(`InjCensus.not_wf_censusEnv`, `InjMethod.not_wf_injEnv`).  This file asks the next question —
**is `PiInv` true at `VEnv.WF`?** — by running the extremes instrument on `VEnv.WF` itself:
*what does `VEnv.WF` permit that the corner has been assuming it forbids?*

Two answers, both machine-checked here.

## §1 — `VEnv.WF` permits an **inconsistent** environment

`VEnv.WF env := ∃ ds, VEnv.WF' ds env` chains `VDecl.WF` steps with **no `isPure`/`noUnsafe`
filter**, and `VDecl.WF.unsafeDef` typechecks a block's values in the environment that already
carries the block's own constants.  `Theory/MutualDefUnsound.lean` machine-checks such a step and
its inconsistency; §1 composes them into `wf_permits_inconsistent`:

    ∃ env : VEnv, env.WF ∧ ¬ env.Consistent

`Theory/Consistency.lean`'s `leanTTConsistent` quantifies over `VEnv.LeanWF` — the *pure* fragment
— not over `VEnv.WF`, so this is not a contradiction with anything; it is a fact about the
environment class the corner's obligations are stated at.  **Consequence: no model argument can
prove `PiInv` at `VEnv.WF`**, since a soundness model would have to interpret an environment that
types an inhabitant of `∀ p : Prop, p`.  That is a second and independent reason the semantic route
is dead, on top of `Theory/SemanticRouteClosed.lean`'s (which is about the *shape of the
conclusion*, not about the environment class).

**And the limit of that witness, proved rather than confessed** (`unsafeSelfRule_refl`): the rule it
adds is `.const f [] ≡ .const f []`, i.e. `lhs = rhs`.  So it buys inconsistency and **no new
conversion between distinct terms**, and it cannot refute `PiInv` — or anything else about
conversion.  The `.unsafeDef` clause is a red herring for this question, and that is a theorem here,
not an impression.

## §2 — the one refutation route `VEnv.WF` leaves open, and it is self-defeating

`VEnv.WF`'s only sources of `env.defeqs` entries are `.def`, `.unsafeDef`, `.quot` and `.induct`
(`.axiom` and `.opaque` add a constant and no rule — a term is not a conversion — and `.example` leaves the environment unchanged), and
`addConst` fails on a name already present, so **every constant carries at most one δ-rule**.  There
is no `VEnv.WF` analogue of `InjPiRogue.roguePiEnv`'s two-rules-on-one-constant or of
`InjCensus.censusEnv`'s non-`const`-headed left-hand side.  δ + β + η at one rule per constant is
orthogonal; `.unsafeDef`'s circularity costs termination, not confluence.  `.induct`'s
large-elimination guard is present and closed (`VInductDecl'.WF.isLE` demands `LECond`: never-zero
level, or one type with ≤ 1 constructor whose fields are all `Prop`s or occur in the conclusion's
arguments), so no `VEnv.WF` environment large-eliminates a two-constructor `Prop` — the collapse
that would have made two unrelated ι-reducts convertible.

That leaves exactly one non-left-linear, type-directed rule in `IsDefEq`: **`proofIrrel`**.  §2
prices the route it opens, and the price is a trilemma:

| statement | content |
| --- | --- |
| `not_piInv_of_forallEProofPair` | two Π's with non-convertible domains inhabiting one `Prop` refutes `PiInv` outright |
| `sortZeroOneConv_of_piInv_of_propConv` | if the sort `Prop` is convertible to a proposition, `PiInv` forces `Sort 0 ≡ Sort 1` at a sort |
| `not_forallEProofPair_of_sortUniq`, `not_propConv_of_sortUniq`, `not_sortZeroOneConv_of_sortUniq` | `SortUniq` kills the route's **entry** and its **exit residual** alike |

Read together: a `proofIrrel` refutation of `PiInv` needs `SortUniq` to **fail** (to get a Π or a
sort into a `Prop`) *and* needs a `SortUniq` instance to **hold** (to discriminate the two domains
the refutation produces — `¬ SortZeroOneConv` in the canonical instantiation).  The tree has no
supplier of the discrimination other than `SortUniq`: `Theory/Typing/UnivDiscrim.lean` has no
`¬ IsDefEqU` between two sorts, and `docs/handoff-injcensus.md` §V3 measures that the tree's only
two ¬conversion techniques (`IsDefEq.closedN`; inversion at a bounded index) both fail on closed
unbounded conversions.  So the route is **self-defeating**, and this is why nobody has refuted
`PiInv` at `VEnv.WF` — a structural reason, not unfinished work.

Nothing here proves or refutes `PiInv`.  Every theorem is an implication between open statements,
and §2's `SortZeroConvProp`/`ForallEProofPair` are *hypotheses* with no instance in the tree — read them
the way `Theory/Typing/PiLevelPin.lean` reads `SortUniq`.
-/

namespace Lean4Lean
namespace VEnv

/-! ## §1 `VEnv.WF` permits an inconsistent environment, and that witness is inert -/

/-- **`VEnv.WF` does not forbid `.unsafeDef`, hence does not imply consistency.**

`VEnv.WF'` chains `VDecl.WF` steps with no purity filter, and `MutualDefUnsound.selfRef_wf` is a
`VDecl.WF` step over `∅`.  So the corner's environment class contains environments that prove
`falseProp`, and any *model* route to a corner obligation at `VEnv.WF` is dead on arrival. -/
theorem wf_permits_inconsistent : ∃ env : VEnv, env.WF ∧ ¬ env.Consistent := by
  have h : (∅ : VEnv).addConst `f ⟨0, falseProp⟩ = some
      { constants := fun n => if `f = n then some ⟨0, falseProp⟩ else none
        defeqs := fun _ => False } := rfl
  exact ⟨_, ⟨_, .decl (selfRef_wf h) .empty⟩, selfRef_inconsistent h⟩

/-- **…and the witness is inert for conversion.**  The rule `.unsafeDef` adds is
`.const f [] ≡ .const f []`: `lhs` and `rhs` are the *same* term, so `IsDefEq.extra` at this
environment yields nothing `IsDefEqU.refl` did not.  The limit of §1's witness, proved. -/
theorem unsafeSelfRule_refl : selfRefDV.toDefEq.lhs = selfRefDV.toDefEq.rhs := rfl

/-- The same fact in the form that matters: **every** rule of the witness environment is
reflexive, so no pair of distinct terms is related by `extra` there. -/
theorem unsafeSelfEnv_rules_refl {env env' : VEnv}
    (h : env.addConst `f ⟨0, falseProp⟩ = some env') (hnil : ∀ df, ¬ env.defeqs df) :
    ∀ df, (env'.addDefEqs [selfRefDV]).defeqs df → df.lhs = df.rhs := by
  intro df hdf
  simp only [VEnv.addDefEqs, List.foldl, VEnv.addDefEq] at hdf
  obtain rfl | hdf := hdf
  · exact unsafeSelfRule_refl
  · exact absurd hdf (by
      unfold VEnv.addConst at h; split at h
      · exact absurd h nofun
      · cases h; exact hnil df)

/-- **§1, packaged as the one statement worth quoting.**  `VEnv.WF` permits an environment that is
**inconsistent** and whose δ-rules are **all reflexive**.  The first half kills every model route to
a corner obligation stated at `VEnv.WF`; the second is why the `.unsafeDef` clause, having been
found, is *not* a way to refute `PiInv`. -/
theorem wf_permits_inconsistent_inert :
    ∃ env : VEnv, env.WF ∧ ¬ env.Consistent ∧ ∀ df, env.defeqs df → df.lhs = df.rhs := by
  have h : (∅ : VEnv).addConst `f ⟨0, falseProp⟩ = some
      { constants := fun n => if `f = n then some ⟨0, falseProp⟩ else none
        defeqs := fun _ => False } := rfl
  exact ⟨_, ⟨_, .decl (selfRef_wf h) .empty⟩, selfRef_inconsistent h,
    unsafeSelfEnv_rules_refl h (fun _ hd => hd)⟩

/-! ## §2 The `proofIrrel` route

The two entry hypotheses.  Neither has an instance anywhere in the tree; they are named so that the
route can be priced without asserting that it fires. -/

variable {env : VEnv} {U : Nat}

/-- **Two Π types, with non-convertible domains, inhabiting one `Prop`.**  This is precisely what
`proofIrrel` needs in order to relate two Π's without relating their domains, and therefore
precisely the shape of a `proofIrrel` refutation of `PiInv`. -/
def ForallEProofPair (env : VEnv) (U : Nat) : Prop :=
  ∃ (Γ : List VExpr) (p A B A' B' : VExpr),
    OnCtx Γ (env.IsType U) ∧ env.HasType U Γ p (.sort .zero) ∧
    env.HasType U Γ (.forallE A B) p ∧ env.HasType U Γ (.forallE A' B') p ∧
    ¬ ∃ u, env.IsDefEq U Γ A A' (.sort u)

/-- **The sort `Prop` is convertible to a proposition** — the weaker, level-only entry hypothesis:
some `p` with `p : Prop` is `IsDefEq`-convertible to `.sort .zero` at a sort.  It is enough, because
`VLevel.imax_zero` makes *every* Π with a `Prop` codomain a term of type `.sort .zero`, so the pair
of Π's §2 builds is available at **any** pair of domains once `.sort .zero` is retypable to `p`. -/
def SortZeroConvProp (env : VEnv) (U : Nat) : Prop :=
  ∃ (Γ : List VExpr) (p : VExpr) (z : VLevel),
    OnCtx Γ (env.IsType U) ∧ env.HasType U Γ p (.sort .zero) ∧
    env.IsDefEq U Γ (.sort .zero) p (.sort z)

/-- The route's **exit residual**: the two domains the canonical instantiation produces are
`Prop` and `Sort 1`, so refuting `PiInv` this way needs them to be non-convertible. -/
def SortZeroOneConv (env : VEnv) (U : Nat) : Prop :=
  ∃ (Γ : List VExpr) (u : VLevel),
    OnCtx Γ (env.IsType U) ∧
    env.IsDefEq U Γ (.sort .zero) (.sort (.succ .zero)) (.sort u)

/-- `∀ p : Prop, p` is a `Prop`, in every context and every environment. -/
theorem hasType_falseProp {Γ : List VExpr} :
    env.HasType U Γ (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) :=
  .defeqDF (.sortDF (l := VLevel.imax (.succ .zero) .zero) ⟨trivial, trivial⟩ trivial
      VLevel.imax_zero)
    (HasType.forallE (.sort trivial) (.bvar .zero))

/-- `∀ _ : Sort 1, (∀ p : Prop, p)` is also a `Prop` — the second Π, with a **different** domain
and the *same* type.  `VLevel.imax_zero` is what makes the domain free. -/
theorem hasType_piOne {Γ : List VExpr} :
    env.HasType U Γ
      (.forallE (.sort (.succ .zero)) (.forallE (.sort .zero) (.bvar 0))) (.sort .zero) :=
  .defeqDF (.sortDF (l := VLevel.imax (.succ (.succ .zero)) .zero) ⟨trivial, trivial⟩ trivial
      VLevel.imax_zero)
    (HasType.forallE (.sort trivial) hasType_falseProp)

/-- **The `proofIrrel` route, in its strongest form: it refutes `PiInv` outright.**

`proofIrrel` relates the two Π's at the shared `Prop`, `PiInv` then demands a conversion of their
domains at a sort, and the hypothesis denies it. -/
theorem not_piInv_of_forallEProofPair (h : ForallEProofPair env U) : ¬ PiInv env U := by
  obtain ⟨Γ, p, A, B, A', B', hΓ, hp, h1, h2, hne⟩ := h
  exact fun hpi => hne (hpi hΓ ⟨p, .proofIrrel hp h1 h2⟩).1

/-- **The level-only form: if any sort inhabits a `Prop`, `PiInv` forces `Sort 0 ≡ Sort 1`.**

The two Π's are `∀ p : Prop, p` and `∀ _ : Sort 1, (∀ p : Prop, p)`; both are `Prop`s by
`VLevel.imax_zero`, so `defeqDF` retypes both at `p` and `proofIrrel` relates them.  `PiInv`'s
*domain* conjunct then hands back a typed conversion between `Prop` and `Sort 1`. -/
theorem sortZeroOneConv_of_piInv_of_propConv (hpi : PiInv env U) (h : SortZeroConvProp env U) :
    SortZeroOneConv env U := by
  obtain ⟨Γ, p, z, hΓ, hp, hcv⟩ := h
  have h1 : env.HasType U Γ (.forallE (.sort .zero) (.bvar 0)) p :=
    .defeqDF hcv hasType_falseProp
  have h2 : env.HasType U Γ
      (.forallE (.sort (.succ .zero)) (.forallE (.sort .zero) (.bvar 0))) p :=
    .defeqDF hcv hasType_piOne
  obtain ⟨u, hu⟩ := (hpi hΓ ⟨p, .proofIrrel hp h1 h2⟩).1
  exact ⟨Γ, u, hΓ, hu⟩

/-- **`SortUniq` kills the route's entry**, at the Π form: `forallE_not_proof`. -/
theorem not_forallEProofPair_of_sortUniq (hord : Ordered env) (hsu : env.SortUniq U) :
    ¬ ForallEProofPair env U := by
  rintro ⟨Γ, p, A, B, _, _, hΓ, hp, h1, -, -⟩
  exact forallE_not_proof hsu hord hΓ hp h1

/-- **`SortUniq` kills the route's entry**, at the sort form.  `p` inhabits both `.sort .zero`
(hypothesis) and `.sort z` (the conversion's own type), while `.sort .zero` inhabits `.sort z` and
`.sort (.succ .zero)`; `SortUniq` twice gives `0 ≈ z ≈ 1`.  Cheaper than routing through
`sort_not_proof`, and it needs no `HasTypeStrong`. -/
theorem not_propConv_of_sortUniq (hord : Ordered env) (hsu : env.SortUniq U) :
    ¬ SortZeroConvProp env U := by
  rintro ⟨Γ, p, z, hΓ, hp, hcv⟩
  have hz : env.HasType U Γ p (.sort z) := hcv.hasType.2
  have hzw : z.WF U := have ⟨_, h⟩ := hz.isType hord hΓ; h.sort_inv hord
  have e1 : VLevel.zero ≈ z := hsu hΓ trivial hzw hp hz
  have e2 : z ≈ VLevel.succ .zero :=
    hsu hΓ hzw trivial hcv.hasType.1 (HasType.sort (l := VLevel.zero) trivial)
  exact absurd (congrFun (e1.trans e2) []) (by simp [VLevel.eval])

/-- **`SortUniq` also kills the route's exit residual.**  `Prop` and `Sort 1` inhabit their own
canonical sorts, so a common type for them makes `1 ≈ 2`. -/
theorem not_sortZeroOneConv_of_sortUniq (hord : Ordered env) (hsu : env.SortUniq U) :
    ¬ SortZeroOneConv env U := by
  rintro ⟨Γ, u, hΓ, hu⟩
  have hu0 : env.HasType U Γ (.sort .zero) (.sort u) := hu.hasType.1
  have hu1 : env.HasType U Γ (.sort (.succ .zero)) (.sort u) := hu.hasType.2
  have huw : u.WF U := have ⟨_, h⟩ := hu0.isType hord hΓ; h.sort_inv hord
  have e1 : u ≈ VLevel.succ .zero := hsu hΓ huw trivial hu0 (HasType.sort trivial)
  have e2 : u ≈ VLevel.succ (.succ .zero) := hsu hΓ huw trivial hu1 (HasType.sort trivial)
  exact absurd (congrFun (e1.symm.trans e2) []) (by simp [VLevel.eval])

/-- **The route is self-defeating.**  Both the entry hypothesis and the exit residual are refuted
by the *same* `SortUniq`, so a `proofIrrel` refutation of `PiInv` needs `SortUniq` to fail where it
enters and to hold where it leaves.  Since `SortUniq` is the tree's only supplier of a ¬conversion
fact between two sorts, the route cannot be walked in either configuration. -/
theorem proofIrrel_route_self_defeating (hord : Ordered env) (hsu : env.SortUniq U) :
    (¬ ForallEProofPair env U) ∧ (¬ SortZeroConvProp env U) ∧ (¬ SortZeroOneConv env U) :=
  ⟨not_forallEProofPair_of_sortUniq hord hsu, not_propConv_of_sortUniq hord hsu,
   not_sortZeroOneConv_of_sortUniq hord hsu⟩

/-- **The route, stated as the dichotomy it is.**  At any `Ordered` environment: either `SortUniq`
fails, or `PiInv`'s `proofIrrel` refutation route is empty.  Contrapositive of §2's three
negatives together with `sortZeroOneConv_of_piInv_of_propConv`. -/
theorem sortUniq_of_route_open (hord : Ordered env)
    (h : ForallEProofPair env U ∨ SortZeroConvProp env U) : ¬ env.SortUniq U :=
  fun hsu => h.elim (not_forallEProofPair_of_sortUniq hord hsu)
    (not_propConv_of_sortUniq hord hsu)

end VEnv
end Lean4Lean
