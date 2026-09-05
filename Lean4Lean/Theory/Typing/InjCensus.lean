import Lean4Lean.Theory.Typing.RigidNodeCircle
import Lean4Lean.Theory.Typing.InjPiRogue

/-!
# A census of `WF.rigidShapeUniqNS`'s five members, by environment strength

`RigidNodeCircle.rigidShapeUniqNS_iff_family` splits `Injectivity.WF.rigidShapeUniqNS` into
exactly five members.  Every previous round attacked the conjunction.  This file asks, member by
member, **what environment hypothesis the member actually needs** — and answers it the only way
that is not admiration: by exhibiting `Ordered` environments at which the member is false.

Nothing here closes a hole; no census number moves.

## The one witness environment, and what it kills

`censusEnv` declares **one** constant `C : Sort 1` with **one** universe parameter, and **three**
definitional equations, none of whose left-hand sides is `const`-headed:

    dfPi    :  ∀ (_ : Prop), Prop  ≡  C.{0}    at  Sort 1
    dfSort  :  Prop                ≡  C.{0}    at  Sort 1
    dfSort1 :  Prop                ≡  C.{1}    at  Sort 1

`Ordered.defeq` asks only `VDefEq.WF` — both sides typed at `df.type` in the empty context — and
all three satisfy it (`ordered_censusEnv`).  Because no left-hand side is `const`-headed,
`RuleFreeHead C` holds (`ruleFreeHead_cName`), so the `RigidShape.RuleFree` side condition that
`ConstInvWitness.lean`'s W1 was built to exclude is *satisfied* here — this is not that witness.

From those three rules, four of the five members fall out at `Ordered` strength:

| member | polarity | verdict at `Ordered` | witness |
|---|---|---|---|
| `PiInv` | positive | **not refutable by this idiom** — only modulo `RigidSortPiDisj` at a *different* environment (§5) | `roguePiEnv` |
| `RigidSortPiDisj` | negative | **false** | `not_rigidSortPiDisj` |
| `RigidConstAppInv` | positive | **false modulo one `¬ IsProof`** (§4); its `¬ IsProof`-free form is false outright | `not_rigidConstAppInvNP` |
| `RigidConstPiDisj` | negative | **false** | `not_rigidConstPiDisj` |
| `RigidConstSortDisj` | negative | **false** | `not_rigidConstSortDisj` |

and the witness is **not** `VEnv.WF` (`not_wf_censusEnv`), which is where every refutation here
must stop: the real obligation takes `VEnv.WF env`.

## Which clause of `VEnv.WF` separates them

`VEnv.RuleShape.delta` — *a δ-rule's left-hand side is `.const ci.name _`*.  One rule with a
non-`const`-headed lhs is enough, for all four members, and that is strictly cheaper than
`InjPiRogue.lean`'s separation, which needs **two** δ-rules on **one** constant and therefore
pins `DeltaUnique.DefEqHeadsUnique` — a clause logically posterior to `RuleShape.delta`.
`InjMethod.lean` already made this point for the *stratified* `SortForallEDisjN`; §3 below makes
it for the unstratified family member `RigidSortPiDisj` itself, which is the statement the family
actually contains, and §2/§3 extend it to the two spine-disjointness members, which no witness in
the tree had reached (their spine needs a declared constant, and `InjMethod.injEnv` has none).

## The asymmetry the census measures, and it is the headline

The three **negative** members are refuted by *producing* a conversion — one `IsDefEq.extra`
each.  The two **positive** members cannot be refuted that way: their conclusions *assert*
conversions, so refuting them needs a **¬conversion** fact, and `InjPiRogue.lean`'s
§"Why no refutation is constructible" enumerates the tree's two techniques for proving a
conversion absent (`IsDefEq.closedN`; inversion at a bounded index) and shows neither reaches
this shape.  Rules relate *closed* terms, so `closedN` is vacuous here, and an `extra` link
carries no index bound.

`RigidConstAppInv` is the exception that proves the rule: its conclusion has a **level**
conjunct, `List.Forall₂ (· ≈ ·) ls ls'`, and level inequivalence *is* decidable.  That is why §4
gets an unconditional refutation of the `¬ IsProof`-free form and a refutation of the real member
modulo exactly one `¬ IsProof` — measured, not guessed: `¬ IsProof` is the *only* residue.

`PiInv` has no level conjunct at all (`RigidNodeCircle.imax_dom_not_pinned` is the machine-checked
reason level data cannot reach its domain half), so §5 gets only the conditional form.

**Read §5's bound honestly.**  It is not a refutation of `PiInv` from `Ordered`.  It is the
implication *"if `Ordered` alone proved `PiInv`, then sort/Π disjointness would fail at an
`Ordered` environment"* — the same shape as `InjPiRogue.not_convPiFromEntry_of_convSortPiDisj`,
and conditional in the same way.  It must not be quoted as `¬ (Ordered → PiInv)`.
-/

namespace Lean4Lean
namespace VEnv
namespace InjCensus



/-! ## §1 The witness environment -/

/-- `Prop`. -/
def vProp : VExpr := .sort .zero
/-- `∀ (_ : Prop), Prop`. -/
def vPiProp : VExpr := .forallE (.sort .zero) (.sort .zero)
/-- `Sort 1`. -/
def sort1 : VExpr := .sort (.succ .zero)

/-- The one declared constant.  Its last component is deliberately **not** `rec`, which is what
kills `RuleShape.iota` in `not_wf_censusEnv`. -/
def cName : Lean.Name := `Lean4Lean.injCensusConst

/-- `C : Sort 1`, with one universe parameter that its type does not mention — so `C.{0}` and
`C.{1}` are two *distinct* level instantiations of one constant, both of type `Sort 1`. -/
def cCi : VConstant := ⟨1, sort1⟩

def envC : VEnv where
  constants n := if cName = n then some cCi else none
  defeqs _ := False

def dfPi : VDefEq := ⟨0, vPiProp, .const cName [.zero], sort1⟩
def dfSort : VDefEq := ⟨0, vProp, .const cName [.zero], sort1⟩
def dfSort1 : VDefEq := ⟨0, vProp, .const cName [.succ .zero], sort1⟩

def censusEnv : VEnv := ((envC.addDefEq dfPi).addDefEq dfSort).addDefEq dfSort1

theorem envC_constants : envC.constants cName = some cCi := by simp [envC]

theorem censusEnv_constants : censusEnv.constants cName = some cCi := envC_constants

theorem censusEnv_defeqs_pi : censusEnv.defeqs dfPi := by
  simp [censusEnv, VEnv.addDefEq, envC]

theorem censusEnv_defeqs_sort : censusEnv.defeqs dfSort := by
  simp [censusEnv, VEnv.addDefEq, envC]

theorem censusEnv_defeqs_sort1 : censusEnv.defeqs dfSort1 := by
  simp [censusEnv, VEnv.addDefEq, envC]

/-- `C.{l} : Sort 1` for any level list of length one, in any environment declaring `C`. -/
theorem cName_type {env : VEnv} {U : Nat} {Γ : List VExpr} {l : VLevel}
    (h : env.constants cName = some cCi) (hl : l.WF U) :
    env.HasType U Γ (.const cName [l]) sort1 := by
  have := IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) (ls := [l]) (ls' := [l])
    h (by simpa using hl) (by simpa using hl) rfl (.cons rfl .nil)
  exact by simpa [cCi, sort1, VExpr.instL, VLevel.inst, VEnv.HasType] using this

theorem addConst_envC : VEnv.empty.addConst cName cCi = some envC := by
  simp [VEnv.addConst, VEnv.empty, envC]

theorem ordered_envC : Ordered envC :=
  .const .empty ⟨_, rogueSort1Type⟩ addConst_envC

theorem vPiProp_type {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U Γ vPiProp sort1 := roguePi1_type

theorem ordered_censusEnv : Ordered censusEnv :=
  .defeq (.defeq (.defeq ordered_envC
      ⟨vPiProp_type, cName_type envC_constants trivial⟩)
    ⟨roguePropType, cName_type envC_constants trivial⟩)
    ⟨roguePropType, cName_type envC_constants trivial⟩

/-! ## §2 The three links -/

theorem link_pi : censusEnv.IsDefEq 0 [] vPiProp (.const cName [.zero]) sort1 := by
  have h := IsDefEq.extra (env := censusEnv) (uvars := 0) (Γ := []) (ls := []) (df := dfPi)
    censusEnv_defeqs_pi (by simp) rfl
  simpa [dfPi, vPiProp, sort1, VExpr.instL, VLevel.inst] using h

theorem link_sort : censusEnv.IsDefEq 0 [] vProp (.const cName [.zero]) sort1 := by
  have h := IsDefEq.extra (env := censusEnv) (uvars := 0) (Γ := []) (ls := []) (df := dfSort)
    censusEnv_defeqs_sort (by simp) rfl
  simpa [dfSort, vProp, sort1, VExpr.instL, VLevel.inst] using h

theorem link_sort1 : censusEnv.IsDefEq 0 [] vProp (.const cName [.succ .zero]) sort1 := by
  have h := IsDefEq.extra (env := censusEnv) (uvars := 0) (Γ := []) (ls := []) (df := dfSort1)
    censusEnv_defeqs_sort1 (by simp) rfl
  simpa [dfSort1, vProp, sort1, VExpr.instL, VLevel.inst] using h

/-- **The side condition the three shapes carry is satisfied.**  No rule of `censusEnv` has a
`const`-headed left-hand side, so `C` heads no rule. -/
theorem ruleFreeHead_cName : censusEnv.RuleFreeHead cName := by
  intro df hdf
  obtain rfl | rfl | rfl | h := (by simpa [censusEnv, VEnv.addDefEq] using hdf :
    df = dfSort1 ∨ df = dfSort ∨ df = dfPi ∨ envC.defeqs df)
  · simp [dfSort1, vProp, VExpr.headConst?]
  · simp [dfSort, vProp, VExpr.headConst?]
  · simp [dfPi, vPiProp, VExpr.headConst?]
  · exact absurd h (by simp [envC])

/-! ## §3 The three negative members are false at `censusEnv` -/

/-- **Member 2 is false.**  `Prop ≡ ∀ (_ : Prop), Prop` at an `Ordered` environment — the
*unstratified* statement the family actually contains, not `InjMethod.lean`'s stratified
`SortForallEDisjN`. -/
theorem not_rigidSortPiDisj : ¬ censusEnv.RigidSortPiDisj 0 := fun h =>
  h (Γ := []) (u := .zero) (A := .sort .zero) (B := .sort .zero) trivial
    ⟨sort1, link_sort.trans link_pi.symm⟩

/-- **Member 4 is false**: a rule-free constant spine convertible with a Π. -/
theorem not_rigidConstPiDisj : ¬ censusEnv.RigidConstPiDisj 0 := fun h =>
  h (Γ := []) (c := cName) (ls := [.zero]) (as := []) (A := .sort .zero) (B := .sort .zero)
    trivial ruleFreeHead_cName ⟨sort1, link_pi.symm⟩

/-- **Member 5 is false**: a rule-free constant spine convertible with a sort. -/
theorem not_rigidConstSortDisj : ¬ censusEnv.RigidConstSortDisj 0 := fun h =>
  h (Γ := []) (c := cName) (ls := [.zero]) (as := []) (u := .zero)
    trivial ruleFreeHead_cName ⟨sort1, link_sort.symm⟩

/-! ## §4 Member 3, and the exact residue -/

/-- The spine conversion the level argument runs on: `C.{0} ≡ C.{1}`, through `Prop`. -/
theorem link_levels :
    censusEnv.IsDefEq 0 [] (.const cName [.zero]) (.const cName [.succ .zero]) sort1 :=
  link_sort.symm.trans link_sort1

theorem not_levels_equiv : ¬ List.Forall₂ (· ≈ ·) [(.zero : VLevel)] [(.succ .zero : VLevel)] := by
  rintro (_ | ⟨h, -⟩)
  exact absurd (congrFun h []) (by simp [VLevel.eval])

/-- `RigidConstAppInv` with its `¬ IsProof` premise dropped.  Stated here so that the
unconditional half of the measurement has a name. -/
def RigidConstAppInvNP (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {c : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c →
    env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c ls').mkApp as') →
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as'

theorem RigidConstAppInv.np (h : env.RigidConstAppInv U)
    (hnp : ∀ {Γ c ls as}, ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as)) :
    RigidConstAppInvNP env U := fun hΓ hc hd => h hΓ hc hnp hd

/-- **The `¬ IsProof`-free form of member 3 is false at `censusEnv`**, unconditionally: the two
spines are `C.{0}` and `C.{1}`, and `0 ≉ 1`.

This is the only member whose conclusion contains data that is *decidably* refutable — a level
list.  Every other positive obligation in the family concludes a conversion, and refuting a
conversion is the fact this tree does not have. -/
theorem not_rigidConstAppInvNP : ¬ RigidConstAppInvNP censusEnv 0 := fun h =>
  not_levels_equiv (h (Γ := []) (c := cName) (ls := [.zero]) (ls' := [.succ .zero])
    (as := []) (as' := []) trivial ruleFreeHead_cName ⟨sort1, link_levels⟩).1

/-- **Member 3 is false at `censusEnv` modulo one `¬ IsProof`.**

The residue is exactly `¬ censusEnv.IsProof 0 [] C.{0}` — a single closed instance, at the very
term the refutation is about.  It is *not* discharged here, and the reason is structural rather
than lazy: the clean discharge is `Injectivity.not_isProof_of_sort'`, whose hypotheses are
`SortUniq ∧ Ordered ∧ ProofTransport`, and `SortUniq` at `censusEnv` is exactly as unavailable as
`SortUniq` anywhere else in this corner.  (`Injectivity.not_isProof_of_defeqU_sort` would
discharge it with no hypothesis at all, but that lemma is `sorryAx`-backed — see
`RigidNodeCircle.lean` §4, "`¬ IsProof` premises are *not* free".)

So the honest reading is: **`Ordered` fails member 3 too, unless an `Ordered` environment can
make `C.{0}` a proof** — and the second disjunct is the whole content of what is left. -/
theorem not_rigidConstAppInv_of_not_isProof
    (hnp : ¬ censusEnv.IsProof 0 [] (.const cName [.zero])) :
    ¬ censusEnv.RigidConstAppInv 0 := fun h =>
  not_levels_equiv (h (Γ := []) (c := cName) (ls := [.zero]) (ls' := [.succ .zero])
    (as := []) (as' := []) trivial ruleFreeHead_cName hnp ⟨sort1, link_levels⟩).1

/-- The same residue routed through the tree's named `¬ IsProof` supplier, so that the
hypothesis is a *family-external* one rather than a bespoke instance. -/
theorem not_rigidConstAppInv_of_sortUniq (hsu : censusEnv.SortUniq 0)
    (htr : censusEnv.ProofTransport 0) : ¬ censusEnv.RigidConstAppInv 0 :=
  not_rigidConstAppInv_of_not_isProof
    (not_isProof_of_sort' hsu ordered_censusEnv htr trivial ⟨_, link_sort.symm⟩)

/-! ## §5 Member 1: only a conditional bound, and at a different environment

At `censusEnv` no conditional bound on `PiInv` is worth stating, because `censusEnv` refutes
`RigidSortPiDisj` outright (§3), so any implication with that as its antecedent is vacuous
there.  The bound therefore has to be taken at an environment where the negative members
*survive*, and `InjPiRogue.roguePiEnv` is exactly that: two Π-valued rules for one constant, no
sort on either side of either rule. -/

theorem rogue_link1' : roguePiEnv.IsDefEq 0 [] (.const rogueC []) roguePi1 sort1 := by
  have h := IsDefEq.extra (env := roguePiEnv) (uvars := 0) (Γ := []) (ls := []) (df := rogueDf1)
    roguePiEnv_defeqs1 (by simp) rfl
  simpa [rogueDf1, roguePi1, sort1, VExpr.instL, VLevel.inst] using h

theorem rogue_link2' : roguePiEnv.IsDefEq 0 [] (.const rogueC []) roguePi2 sort1 := by
  have h := IsDefEq.extra (env := roguePiEnv) (uvars := 0) (Γ := []) (ls := []) (df := rogueDf2)
    roguePiEnv_defeqs2 (by simp) rfl
  simpa [rogueDf2, roguePi2, roguePi1, sort1, VExpr.instL, VLevel.inst] using h

/-- The two Π's are convertible at `roguePiEnv`, in the **empty** context. -/
theorem rogue_piPi' : roguePiEnv.IsDefEqU 0 [] roguePi1 roguePi2 :=
  ⟨sort1, rogue_link1'.symm.trans rogue_link2'⟩

/-- **`PiInv` at `roguePiEnv` forces a sort/Π conversion**, in the one-entry context `[Prop]`:
the two codomains are `Prop` and `∀ (_ : Prop), Prop`. -/
theorem piInv_forces (h : roguePiEnv.PiInv 0) :
    roguePiEnv.IsDefEqU 0 [vProp] (.sort .zero) roguePi1 :=
  let ⟨_, _u, hb⟩ := h (Γ := []) trivial rogue_piPi'
  ⟨_, hb⟩

theorem rogue_onCtx' : OnCtx [vProp] (roguePiEnv.IsType 0) := ⟨trivial, _, roguePropType⟩

/-- **The conditional bound on member 1.**  If `PiInv` held at `roguePiEnv`, member 2 would fail
there.  Since `roguePiEnv` is `Ordered`, a proof of `PiInv` from `Ordered` alone would refute
sort/Π disjointness at an `Ordered` environment — which is the thing nobody in this development
believes false.  **Conditional; do not quote as `¬ (Ordered → PiInv)`.** -/
theorem not_piInv_of_rigidSortPiDisj (hsp : roguePiEnv.RigidSortPiDisj 0) :
    ¬ roguePiEnv.PiInv 0 := fun h => hsp rogue_onCtx' (piInv_forces h)

/-- The same, as a statement about the *hypothesis* `Ordered` rather than about one environment. -/
theorem ordered_not_enough_for_piInv (hsp : roguePiEnv.RigidSortPiDisj 0) :
    ¬ ∀ (env : VEnv) (U : Nat), Ordered env → env.PiInv U :=
  fun h => not_piInv_of_rigidSortPiDisj hsp (h roguePiEnv 0 ordered_roguePiEnv)

/-! ## §6 …and the witness is not `VEnv.WF`, which is where all of this stops -/

/-- No rule of `censusEnv` can have any of the three legal shapes, and the argument is uniform:
`delta` needs a `const`-headed lhs, `quot` needs `Quot.lift` declared, and `iota` needs a
constant whose name ends in `rec`.  `censusEnv` declares exactly one constant, and its name ends
in `injCensusConst`. -/
theorem not_ruleShape {df : VDefEq} {l : VLevel} (h : censusEnv.RuleShape df) :
    df.lhs ≠ .sort l := by
  cases h with
  | delta ci _ => simp [VDefVal.toDefEq]
  | quot h1 _ => exact absurd h1 (by simp [censusEnv, VEnv.addDefEq, envC, cName])
  | iota D j q T C _ _ _ _ _ _ hrec _ _ _ _ _ _ =>
    exact absurd hrec (by simp [censusEnv, VEnv.addDefEq, envC, cName, Lean.mkRecName])

/-- **`censusEnv` is not `VEnv.WF`.**  So `Injectivity.WF.rigidShapeUniqNS` is *not* refuted by
anything in this file, and cannot be: the clause that repairs every refutation above is
`VEnv.RuleShape.delta`. -/
theorem not_wf_censusEnv : ¬ VEnv.WF censusEnv := fun h =>
  not_ruleShape (l := .zero) (h.ruleShape censusEnv_defeqs_sort) rfl

end InjCensus
end VEnv
end Lean4Lean
