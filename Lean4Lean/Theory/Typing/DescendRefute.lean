import Lean4Lean.Theory.Typing.ParamsBuild
import Lean4Lean.Theory.Typing.SortUniqFacts

/-!
# `NormalEq.descend` is false

`Theory/Typing/ChurchRosser.lean`'s `NormalEq.descend` carries **three** `sorry`s (at `:2074`,
`:2079`, `:2094`; this file said "five" in three places, measured stale 2026-08-31) and its own
inventory says of them: *"every one of them waits on a hypothesis -- there is no remaining
case that is merely unproved.  None of their goals is known false."*  **Three of the five
goals are false**, and this file exhibits a machine-checked witness for each.

## What is refuted, and how

`descend` quantifies over an **arbitrary** `q : Pattern` -- there is no hypothesis that `q`
is a rule the environment registers, nor even a subpattern of one.  So the three "E5"
branches, which all assert something about an *argument position* of an `.app` node, are
asserting it of a pattern nobody registered.  Each of the three is refuted by a term that is
`NormalEq` to a matching term, does not reduce to one, and is not a proof:

| `sorry` | `ChurchRosser.lean` | branch | witness |
|---|---|---|---|
| E5, argument is a proof | `:2074` | `not_descendStatement` | `C h` vs `C D` |
| E5, argument eta-expanded | `:2079` | `not_descendStatement_etaArg` | `F (fun x => E x)` vs `F E` |
| E5, function eta-expanded | `:2094` | `not_descendStatement_etaFun` | `(fun x => C h) D` vs `C D` |

(Those three line numbers are the `sorry`s' current positions, re-measured 2026-09-01.  This
table previously read `:1799` / `:1784` / `:1779`, which were stale by some 290 lines -- the
same drift the paragraph above flags for the *count*.  The three docstrings on the refutations
themselves carried the same stale numbers and are corrected too.)

The remaining two -- the "E3" branches, where the *function* side is a proof -- are **not**
refuted, and `NormalEq.appDF_proof_escape` at the end of this file closes them from
universe uniqueness alone.

## What the refutation costs, and why it is not circular

Each witness needs one step that is not syntactic: *the node is not a proof*.  That step
needs unique typing (`IsDefEq.uniq`) and universe uniqueness (`VEnv.SortUniq`), both of
which are `sorryAx`-tainted in this tree, so they are carried as **explicit hypotheses**
(`refEnv_sortUniq`, `refEnv_uniqTyping` record that they are no stronger than the family
they name).  Note `VEnv.SortUniq` *unqualified over `env`* is refuted
(`Theory/Typing/SortUniqDown.lean`'s `sortUniq_badEnv`, concurrent work); the instance used
here is at `refEnv`, which is `VEnv.WF`, i.e. the `∀ env, env.WF → env.SortUniq U` form that
is open.  The headline `descend_uniq_sortUniq_not_all` is therefore: `descend`, unique
typing and universe uniqueness cannot all three hold.  Unique typing and universe
uniqueness are theorems of Lean's type theory (`~/lean-type-theory/unique.tex`), and they
are what the Π/sort inversion family -- hence the whole confluence development -- exists to
deliver.  So the one that fails is `descend`.

## Does restricting `q` to registered patterns save it?

For the **δ fragment**, yes trivially: a δ-pattern is a bare `.const`, so `descend`'s `.app`
cases never arise.  For ι and quotient rules, **no** -- see `docs/handoff-weakn.md` §3.  An
ι-rule's argument position is the major premise, and for a large-eliminating `Prop`
inductive (`Eq`, `Acc`, `HEq`, and `Quot` at `Sort 0`) the major premise *is* a proof, which
is witness A's shape at a registered pattern.  That part is analysis, not machine-checked:
this tree has no environment carrying such a rule with a `Params` instance.
-/

namespace Lean4Lean
open VExpr

/-- `P : Prop`. -/
def refP : VConstant := ⟨0, .sort .zero⟩
/-- `D : P`, a proof of the proposition `P`. -/
def refD : VConstant := ⟨0, .const `P []⟩
/-- `T : Type`, a type that is not a proposition. -/
def refT : VConstant := ⟨0, .sort (.succ .zero)⟩
/-- `C : P → T`. -/
def refC : VConstant := ⟨0, .forallE (.const `P []) (.const `T [])⟩
/-- `E : P → P`.  Note `P → P` is itself a proposition, so `E` is a *proof* of it. -/
def refE : VConstant := ⟨0, .forallE (.const `P []) (.const `P [])⟩
/-- `F : (P → P) → T`. -/
def refF : VConstant := ⟨0, .forallE (.forallE (.const `P []) (.const `P [])) (.const `T [])⟩

def refEnv1 : VEnv :=
  { VEnv.empty with constants := fun n => if `P = n then some refP else VEnv.empty.constants n }
def refEnv2 : VEnv :=
  { refEnv1 with constants := fun n => if `D = n then some refD else refEnv1.constants n }
def refEnv3 : VEnv :=
  { refEnv2 with constants := fun n => if `T = n then some refT else refEnv2.constants n }
def refEnv4 : VEnv :=
  { refEnv3 with constants := fun n => if `C = n then some refC else refEnv3.constants n }
def refEnv5 : VEnv :=
  { refEnv4 with constants := fun n => if `E = n then some refE else refEnv4.constants n }
/-- The witness environment: six axioms, **no definitional-equality rules at all**. -/
def refEnv : VEnv :=
  { refEnv5 with constants := fun n => if `F = n then some refF else refEnv5.constants n }

theorem refEnv_P : refEnv.constants `P = some refP := rfl
theorem refEnv_D : refEnv.constants `D = some refD := rfl
theorem refEnv_T : refEnv.constants `T = some refT := rfl
theorem refEnv_C : refEnv.constants `C = some refC := rfl
theorem refEnv_E : refEnv.constants `E = some refE := rfl
theorem refEnv_F : refEnv.constants `F = some refF := rfl

theorem refEnv_no_defeqs {df} : ¬ refEnv.defeqs df := nofun

theorem refEnv1_eq : VEnv.empty.addConst `P refP = some refEnv1 := rfl
theorem refEnv2_eq : refEnv1.addConst `D refD = some refEnv2 := rfl
theorem refEnv3_eq : refEnv2.addConst `T refT = some refEnv3 := rfl
theorem refEnv4_eq : refEnv3.addConst `C refC = some refEnv4 := rfl
theorem refEnv5_eq : refEnv4.addConst `E refE = some refEnv5 := rfl
theorem refEnv6_eq : refEnv5.addConst `F refF = some refEnv := rfl

theorem refEnv_wf : refEnv.WF := by
  refine ⟨_, .decl (d := .axiom ⟨refF, `F⟩) (.axiom ?_ refEnv6_eq)
    (.decl (d := .axiom ⟨refE, `E⟩) (.axiom ?_ refEnv5_eq)
      (.decl (d := .axiom ⟨refC, `C⟩) (.axiom ?_ refEnv4_eq)
        (.decl (d := .axiom ⟨refT, `T⟩) (.axiom ⟨_, .sort trivial⟩ refEnv3_eq)
          (.decl (d := .axiom ⟨refD, `D⟩) (.axiom ?_ refEnv2_eq)
            (.decl (d := .axiom ⟨refP, `P⟩) (.axiom ⟨_, .sort trivial⟩ refEnv1_eq) .empty)))))⟩
  · exact ⟨_, .forallEDF (u := .imax .zero .zero) (v := .succ .zero)
      (.forallEDF (u := .zero) (v := .zero)
        (VEnv.IsDefEq.constDF (ci := refP) rfl nofun nofun rfl .nil)
        (VEnv.IsDefEq.constDF (ci := refP) rfl nofun nofun rfl .nil))
      (VEnv.IsDefEq.constDF (ci := refT) rfl nofun nofun rfl .nil)⟩
  · exact ⟨_, .forallEDF (u := .zero) (v := .zero)
      (VEnv.IsDefEq.constDF (ci := refP) rfl nofun nofun rfl .nil)
      (VEnv.IsDefEq.constDF (ci := refP) rfl nofun nofun rfl .nil)⟩
  · exact ⟨_, .forallEDF (u := .zero) (v := .succ .zero)
      (VEnv.IsDefEq.constDF (ci := refP) rfl nofun nofun rfl .nil)
      (VEnv.IsDefEq.constDF (ci := refT) rfl nofun nofun rfl .nil)⟩
  · exact ⟨_, VEnv.IsDefEq.constDF (ci := refP) rfl nofun nofun rfl .nil⟩


/-! ## The `Params` instance -/

theorem refEnv_deltaFragment : VEnv.DeltaFragment refEnv := by
  intro p r h; cases h <;> exact absurd ‹_› refEnv_no_defeqs

/-- The witness `Params` instance: `refEnv` has no rules, so it is (vacuously) a
δ-fragment environment and `paramsOfDelta` applies. -/
@[instance_reducible] def refParams : VEnv.Params :=
  VEnv.paramsOfDelta refEnv_wf 0 refEnv_deltaFragment

theorem refParams_env : (@VEnv.Params.env refParams) = refEnv := rfl
theorem refParams_univs : (@VEnv.Params.univs refParams) = 0 := rfl

theorem refNoPat {p r} : ¬ @VEnv.Params.Pat refParams p r := by
  intro h; cases h <;> exact absurd ‹_› refEnv_no_defeqs


/-! ## The witness -/

/-- One context entry: the proposition `P`.  Its inhabitant `.bvar 0` is a *proof*. -/
abbrev refCtx : List VExpr := [.const `P []]
/-- The left term: `C h` with `h` the context's proof variable. -/
abbrev refG : VExpr := .app (.const `C []) (.bvar 0)
/-- The right term: `C D`, which matches the pattern below. -/
abbrev refG' : VExpr := .app (.const `C []) (.const `D [])
/-- The pattern: an `.app` node whose **argument position** is a `const` leaf. -/
abbrev refQ : Pattern := .app (.const `C) (.const `D)

theorem refEnv_hasP {Γ} : refEnv.HasType 0 Γ (.const `P []) (.sort .zero) :=
  VEnv.IsDefEq.constDF (ci := refP) refEnv_P nofun nofun rfl .nil

theorem refEnv_hΓ : OnCtx refCtx (refEnv.IsType 0) := ⟨trivial, _, refEnv_hasP⟩

theorem refEnv_hasC {Γ} :
    refEnv.HasType 0 Γ (.const `C []) (.forallE (.const `P []) (.const `T [])) :=
  VEnv.IsDefEq.constDF (ci := refC) refEnv_C nofun nofun rfl .nil

theorem refEnv_hasD {Γ} : refEnv.HasType 0 Γ (.const `D []) (.const `P []) :=
  VEnv.IsDefEq.constDF (ci := refD) refEnv_D nofun nofun rfl .nil

theorem refEnv_hasBvar : refEnv.HasType 0 refCtx (.bvar 0) (.const `P []) :=
  VEnv.IsDefEq.bvar .zero

theorem refEnv_hasT {Γ} : refEnv.HasType 0 Γ (.const `T []) (.sort (.succ .zero)) :=
  VEnv.IsDefEq.constDF (ci := refT) refEnv_T nofun nofun rfl .nil

theorem refEnv_hasG : refEnv.HasType 0 refCtx refG (.const `T []) :=
  VEnv.IsDefEq.appDF refEnv_hasC refEnv_hasBvar

theorem refEnv_hasG' : refEnv.HasType 0 refCtx refG' (.const `T []) :=
  VEnv.IsDefEq.appDF refEnv_hasC refEnv_hasD

/-- The two terms are `NormalEq`: same function, and the two arguments are two proofs of
the same proposition, so `NormalEq.proofIrrel` relates them. -/
theorem refNormalEq : @VEnv.NormalEq refParams refCtx refG refG' := by
  letI := refParams
  exact .appDF refEnv_hasC refEnv_hasC refEnv_hasBvar refEnv_hasD
    (.refl refEnv_hasC) (.proofIrrel refEnv_hasP refEnv_hasBvar refEnv_hasD)

theorem refMatches : ∃ n1 n2, refQ.Matches refG' n1 n2 := ⟨_, _, .app .const .const⟩


/-! ## `refG` does not reduce

`refEnv` has no rules, so `ParRed.extra` never fires and `refG`'s head is a constant, so
`ParRed.beta` never fires either.  Hence `refG` is its own only reduct. -/

theorem refParRed_const {Γ c ls e} (H : @VEnv.ParRed refParams Γ (.const c ls) e) :
    e = .const c ls := by
  cases H with
  | const => rfl
  | extra h => exact absurd h refNoPat

theorem refParRed_bvar {Γ i e} (H : @VEnv.ParRed refParams Γ (.bvar i) e) :
    e = .bvar i := by
  cases H with
  | bvar => rfl
  | extra h => exact absurd h refNoPat

theorem refParRed_constBvar {Γ c ls i e}
    (H : @VEnv.ParRed refParams Γ (.app (.const c ls) (.bvar i)) e) :
    e = .app (.const c ls) (.bvar i) := by
  cases H with
  | app hf ha => rw [refParRed_const hf, refParRed_bvar ha]
  | extra h => exact absurd h refNoPat

theorem refParRed_G {e} (H : @VEnv.ParRed refParams refCtx refG e) : e = refG :=
  refParRed_constBvar H

theorem refParRedS_G {e} (H : @VEnv.ParRedS refParams refCtx refG e) : e = refG := by
  induction H with
  | rfl => rfl
  | tail _ h ih => cases ih; exact refParRed_G h


/-! ## …so the descent's *answer* disjunct is unavailable at every eta depth -/

theorem refNoDescentLam : ∀ {k : Nat} {n1 n2},
    ¬ @VEnv.DescentLam refParams k refCtx refQ refG refG' n1 n2
  | 0, _, _, ⟨_, _, _, hred, hmt, _⟩ => by
      cases refParRedS_G hred
      let .app _ h := hmt
      exact nomatch h
  | _+1, _, _, ⟨_, _, _, hred, _⟩ => by cases refParRedS_G hred


/-! ## …and `refG` is not a proof -/

namespace VEnv

/-- **Unique typing**, as a named hypothesis.  This is exactly `IsDefEq.uniq`
(`Theory/Typing/UniqueTyping.lean`) with `e₁ = e₂ = e₃`; it is stated separately here so
that the refutation below is `sorry`-free, since `IsDefEq.uniq` is `sorryAx`-tainted through
`IsDefEqU.sort_inv` and `IsDefEqU.forallE_inv_stratified`. -/
-- (A sibling of this definition, `VEnv.UniqTy`, was landed concurrently in
-- `Theory/Typing/SortUniqDown.lean` by the `SortUniq` stream; if both survive, dedupe.)
def UniqTyping (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ e A B}, OnCtx Γ (env.IsType U) →
    env.HasType U Γ e A → env.HasType U Γ e B → ∃ u, env.IsDefEq U Γ A B (.sort u)

end VEnv

/-- **Nothing of type `T` is a proof.**  `T` is declared at `Sort 1`; a term inhabiting both
`T` and a proposition would make `Sort 1` and `Sort 0` equivalent.  This is the one step that
needs the two open hypotheses, and it needs them for the same reason
`Theory/Typing/SortUniq.lean`'s `sort_not_proof` does. -/
theorem refNotProof (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0)
    {g P} (hP : refEnv.HasType 0 refCtx P (.sort .zero))
    (hgT : refEnv.HasType 0 refCtx g (.const `T []))
    (hg : refEnv.HasType 0 refCtx g P) : False := by
  obtain ⟨u, hPT⟩ := huq refEnv_hΓ hg hgT
  have huWF : u.WF 0 := hPT.sort_r refEnv_wf.ordered refEnv_hΓ
  have h1 : VLevel.zero ≈ u := hsu refEnv_hΓ trivial huWF hP hPT.hasType.1
  have h2 : u ≈ VLevel.succ VLevel.zero := hsu refEnv_hΓ huWF trivial hPT.hasType.2 refEnv_hasT
  exact absurd (congrFun (h1.trans h2) []) (by simp [VLevel.eval])


/-! ## Witness B: an argument position that **eta-expanded**

Same shape, but now the left argument is a `.lam` and the right argument is a constant of
Π type; `NormalEq.etaL` relates them because `P → P` is itself a proposition, so the
eta-expansion's body and `.bvar 0` are two proofs of `P`. -/

/-- The eta-expansion of `E`.  Its descent at the pattern `.const E` returns an answer
under **one** pending eta layer, which is what puts `descend` in its `ka+1` branch. -/
abbrev refId : VExpr := .lam (.const `P []) (.app (.const `E []) (.bvar 0))
abbrev refG2 : VExpr := .app (.const `F []) refId
abbrev refG2' : VExpr := .app (.const `F []) (.const `E [])
abbrev refQ2 : Pattern := .app (.const `F) (.const `E)

theorem refEnv_hasF {Γ} : refEnv.HasType 0 Γ (.const `F [])
    (.forallE (.forallE (.const `P []) (.const `P [])) (.const `T [])) :=
  VEnv.IsDefEq.constDF (ci := refF) refEnv_F nofun nofun rfl .nil

theorem refEnv_hasE {Γ} :
    refEnv.HasType 0 Γ (.const `E []) (.forallE (.const `P []) (.const `P [])) :=
  VEnv.IsDefEq.constDF (ci := refE) refEnv_E nofun nofun rfl .nil

theorem refEnv_hasIdBody :
    refEnv.HasType 0 (.const `P [] :: refCtx) (.app (.const `E []) (.bvar 0)) (.const `P []) := by
  exact VEnv.IsDefEq.appDF refEnv_hasE (VEnv.IsDefEq.bvar .zero)

theorem refEnv_hasId :
    refEnv.HasType 0 refCtx refId (.forallE (.const `P []) (.const `P [])) :=
  VEnv.IsDefEq.lamDF (u := .zero) refEnv_hasP refEnv_hasIdBody

theorem refEnv_hasG2 : refEnv.HasType 0 refCtx refG2 (.const `T []) :=
  VEnv.IsDefEq.appDF refEnv_hasF refEnv_hasId

theorem refNormalEq2 : @VEnv.NormalEq refParams refCtx refG2 refG2' := by
  letI := refParams
  exact .appDF refEnv_hasF refEnv_hasF refEnv_hasId refEnv_hasE
    (.refl refEnv_hasF) (.etaL refEnv_hasE (.refl refEnv_hasIdBody))

theorem refMatches2 : ∃ n1 n2, refQ2.Matches refG2' n1 n2 := ⟨_, _, .app .const .const⟩

theorem refParRed_id {Γ e} (H : @VEnv.ParRed refParams Γ refId e) : e = refId := by
  cases H with
  | lam hA hb => rw [refParRed_const hA, refParRed_constBvar hb]
  | extra h => exact absurd h refNoPat

theorem refParRed_G2 {e} (H : @VEnv.ParRed refParams refCtx refG2 e) : e = refG2 := by
  cases H with
  | app hf ha => rw [refParRed_const hf, refParRed_id ha]
  | extra h => exact absurd h refNoPat

theorem refParRedS_G2 {e} (H : @VEnv.ParRedS refParams refCtx refG2 e) : e = refG2 := by
  induction H with
  | rfl => rfl
  | tail _ h ih => cases ih; exact refParRed_G2 h

theorem refNoDescentLam2 : ∀ {k : Nat} {n1 n2},
    ¬ @VEnv.DescentLam refParams k refCtx refQ2 refG2 refG2' n1 n2
  | 0, _, _, ⟨_, _, _, hred, hmt, _⟩ => by
      cases refParRedS_G2 hred
      let .app _ h := hmt
      exact nomatch h
  | _+1, _, _, ⟨_, _, _, hred, _⟩ => by cases refParRedS_G2 hred

/-! ## Witness C: the **function** side eta-expanded at an `.app` node

`refF3` is an eta-expansion of `C` whose body applies `C` to the *outer* proof variable
rather than to the bound one -- legitimate, because both are proofs of `P`.  So the node is
a β-redex whose contractum puts the wrong proof in the argument position. -/

abbrev refF3 : VExpr := .lam (.const `P []) (.app (.const `C []) (.bvar 1))
abbrev refG3 : VExpr := .app refF3 (.const `D [])

theorem refEnv_hasBody :
    refEnv.HasType 0 (.const `P [] :: refCtx) (.app (.const `C []) (.bvar 1)) (.const `T []) := by
  exact VEnv.IsDefEq.appDF refEnv_hasC (VEnv.IsDefEq.bvar (.succ .zero))

theorem refEnv_hasF3 :
    refEnv.HasType 0 refCtx refF3 (.forallE (.const `P []) (.const `T [])) :=
  VEnv.IsDefEq.lamDF (u := .zero) refEnv_hasP refEnv_hasBody

theorem refEnv_hasG3 : refEnv.HasType 0 refCtx refG3 (.const `T []) :=
  VEnv.IsDefEq.appDF refEnv_hasF3 refEnv_hasD

theorem refNormalEq3 : @VEnv.NormalEq refParams refCtx refG3 refG' := by
  letI := refParams
  refine .appDF refEnv_hasF3 refEnv_hasC refEnv_hasD refEnv_hasD ?_ (.refl refEnv_hasD)
  refine .etaL refEnv_hasC (.appDF refEnv_hasC refEnv_hasC
    (VEnv.IsDefEq.bvar (.succ .zero)) (VEnv.IsDefEq.bvar .zero) (.refl refEnv_hasC) ?_)
  exact .proofIrrel refEnv_hasP (VEnv.IsDefEq.bvar (.succ .zero)) (VEnv.IsDefEq.bvar .zero)

theorem refParRed_F3 {Γ e} (H : @VEnv.ParRed refParams Γ refF3 e) : e = refF3 := by
  cases H with
  | lam hA hb => rw [refParRed_const hA, refParRed_constBvar hb]
  | extra h => exact absurd h refNoPat

theorem refParRed_G3 {e} (H : @VEnv.ParRed refParams refCtx refG3 e) : e = refG3 ∨ e = refG := by
  cases H with
  | app hf ha => exact .inl (by rw [refParRed_F3 hf, refParRed_const ha])
  | beta hb ha =>
    rw [refParRed_constBvar hb, refParRed_const ha]; exact .inr rfl
  | extra h => exact absurd h refNoPat

theorem refParRedS_G3 {e} (H : @VEnv.ParRedS refParams refCtx refG3 e) :
    e = refG3 ∨ e = refG := by
  induction H with
  | rfl => exact .inl rfl
  | tail _ h ih =>
    rcases ih with rfl | rfl
    · exact refParRed_G3 h
    · exact .inr (refParRed_G h)

theorem refNoDescentLam3 : ∀ {k : Nat} {n1 n2},
    ¬ @VEnv.DescentLam refParams k refCtx refQ refG3 refG' n1 n2
  | 0, _, _, ⟨_, _, _, hred, hmt, _⟩ => by
      rcases refParRedS_G3 hred with rfl | rfl
      · let .app h _ := hmt
        exact nomatch h
      · let .app _ h := hmt
        exact nomatch h
  | _+1, _, _, ⟨_, _, _, hred, _⟩ => by
      rcases refParRedS_G3 hred with h | h <;> cases h

/-! ## The refutation

Each of the three witnesses lands on a different one of `NormalEq.descend`'s three `sorry`s.
Tracing `descend` on witness A: `cases hne` takes the `appDF` branch, `cases hm` the `app`
branch, the function child's recursive call returns `.inl` (its `NormalEq` is `refl`) and the
argument child's returns `.inr` (its `NormalEq` is `proofIrrel`) -- which is the branch
commented "**E5**: an argument position that is a proof never matches `q₂`".
-/

theorem refNoDescentOut (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) {n1 n2} :
    ¬ @VEnv.DescentOut refParams refCtx refQ refG refG' n1 n2 := by
  rintro (⟨_, D⟩ | ⟨_, hP, hg, -⟩)
  · exact refNoDescentLam D
  · exact refNotProof hsu huq hP refEnv_hasG hg

theorem refNoDescentOut2 (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) {n1 n2} :
    ¬ @VEnv.DescentOut refParams refCtx refQ2 refG2 refG2' n1 n2 := by
  rintro (⟨_, D⟩ | ⟨_, hP, hg, -⟩)
  · exact refNoDescentLam2 D
  · exact refNotProof hsu huq hP refEnv_hasG2 hg

theorem refNoDescentOut3 (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) {n1 n2} :
    ¬ @VEnv.DescentOut refParams refCtx refQ refG3 refG' n1 n2 := by
  rintro (⟨_, D⟩ | ⟨_, hP, hg, -⟩)
  · exact refNoDescentLam3 D
  · exact refNotProof hsu huq hP refEnv_hasG3 hg

/-- **`NormalEq.descend`'s statement**, as a predicate on the `Params` instance, so that it
can be refuted without editing `ChurchRosser.lean`.  That this is the real statement and not
a strawman is checked by `descendStatement_holds` below, which proves it *by*
`NormalEq.descend`. -/
def DescendStatement (I : VEnv.Params) : Prop :=
  ∀ (N : Nat) {g : VExpr}, sizeOf g ≤ N →
    ∀ {Γ : List VExpr} {q : Pattern} {g' : VExpr}
      {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr},
      OnCtx Γ (VEnv.IsType I.env I.univs) → @VEnv.NormalEq I Γ g g' → q.Matches g' n1 n2 →
      @VEnv.DescentOut I Γ q g g' n1 n2

/-- **Anti-strawman check.**  `DescendStatement` is literally `NormalEq.descend`'s type.
`sorryAx`-tainted, inherited from `descend`'s three holes -- that is the point. -/
theorem descendStatement_holds {I : VEnv.Params} : DescendStatement I :=
  @VEnv.NormalEq.descend I

/-- **The refutation, at witness A** (`ChurchRosser.lean:2074`, "an argument position that is
a proof never matches `q₂`"). -/
theorem not_descendStatement (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) :
    ¬ DescendStatement refParams := by
  intro H
  obtain ⟨n1, n2, hm⟩ := refMatches
  exact refNoDescentOut hsu huq (H _ (Nat.le_refl _) refEnv_hΓ refNormalEq hm)

/-- **The refutation, at witness B** (`ChurchRosser.lean:2079`, "an argument position that
eta-expanded never matches `q₂`"). -/
theorem not_descendStatement_etaArg (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) :
    ¬ DescendStatement refParams := by
  intro H
  obtain ⟨n1, n2, hm⟩ := refMatches2
  exact refNoDescentOut2 hsu huq (H _ (Nat.le_refl _) refEnv_hΓ refNormalEq2 hm)

/-- **The refutation, at witness C** (`ChurchRosser.lean:2094`, "the function side
eta-expanded at an `.app` node"). -/
theorem not_descendStatement_etaFun (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) :
    ¬ DescendStatement refParams := by
  intro H
  obtain ⟨n1, n2, hm⟩ := refMatches
  exact refNoDescentOut3 hsu huq (H _ (Nat.le_refl _) refEnv_hΓ refNormalEq3 hm)

/-- The two hypotheses are **not** vacuous: they follow from the tree's own machinery.
`sorryAx`-tainted through `IsDefEqU.sort_inv` and `IsDefEqU.forallE_inv_stratified`, exactly
as `Theory/Typing/SortUniqFacts.lean`'s `WF.sortUniq` is -- so this is an *upper bound* on
their strength (they are no stronger than the Π/sort inversion family), not evidence that
they hold.  Together with `descend_uniq_sortUniq_not_all` this says: **`NormalEq.descend`
and `Theory/Typing/Injectivity.lean`'s open statements cannot both be filled.** -/
theorem refEnv_sortUniq : refEnv.SortUniq 0 := refEnv_wf.sortUniq

/-- See `refEnv_sortUniq`.  `sorryAx`-tainted; this is `IsDefEq.uniq` specialised. -/
theorem refEnv_uniqTyping : refEnv.UniqTyping 0 :=
  fun hΓ h1 h2 => h1.uniq refEnv_wf hΓ h2

/-- **The headline, `sorry`-free**: `NormalEq.descend`, unique typing and universe
uniqueness cannot all three hold.  The latter two are theorems of Lean's type theory
(`~/lean-type-theory/unique.tex`) and are exactly what the Π/sort inversion family exists to
deliver, so the one that fails is `descend`. -/
theorem descend_uniq_sortUniq_not_all :
    ¬ (DescendStatement refParams ∧ refEnv.SortUniq 0 ∧ refEnv.UniqTyping 0) :=
  fun ⟨h, hsu, huq⟩ => not_descendStatement hsu huq h

/-- **The two side hypotheses are satisfiable, so `descend` is simply false.**

`not_descendStatement` is conditional on `refEnv.SortUniq 0` and `refEnv.UniqTyping 0`, and a
conditional refutation is worth only as much as its hypotheses.  They are discharged here by
`refEnv_sortUniq` / `refEnv_uniqTyping`, whose only open input is
`IsDefEqU.forallE_inv_stratified` -- so this statement is `sorryAx`-tainted **through that
hole alone**, and in particular *not* through `NormalEq.descend`: the refutation is not
circular.  Three registers, kept apart:

* **[machine-checked]** `not_descendStatement` and `descend_uniq_sortUniq_not_all` are
  `sorryAx`-free; this corollary's hole cone is `forallE_inv_stratified` and nothing else, and
  `NormalEq.descend` is **not** in it (measured on the value cone, not read off the source).
* **[machine-checked, and it cuts against the first bullet]** `PiLevelPin.lean`'s
  `piInvStratApp_iff_sortUniq` shows that hole is, **given `VEnv.PiInv`**, *equivalent* to
  `VEnv.SortUniq` at the same environment and index.  So deriving `refEnv.SortUniq 0` from it
  is **no independent evidence of satisfiability** -- it assumes the very statement.

  *Correction, 2026-08-31.*  This bullet used to say "modulo `WF.rigidShapeUniq`", which reads
  as though the side condition were already discharged.  It is not: the side condition is
  `PiInv env U`, an explicit hypothesis of `sortUniq_iff_piInvStratApp`
  (`Injectivity.lean:620`), and `PiInv` is a **second open node**, not a lemma -- see
  `Injectivity.lean:1221-1225`, and `RigidNodeCircle.lean`'s `rigidPiUniq_iff_piInv`, which
  shows the `pi`/`pi` entry of the bridge *is* `PiInv` on the nose.  The wording here caused a
  brief to be written on the premise that the two large holes were one hole seen twice; they
  are not, and `SortUniq` alone does not finish the corner.  What the
  first bullet does establish is only non-circularity with `descend`.  The evidence that the
  hypothesis is satisfiable is the next bullet.
* **[not evidence, recorded so nobody re-derives it]** "the only known failure route
  (`SortUniqDown.lean`'s `sortUniq_badEnv`, a `.sort`-headed defeq rule) is closed here,
  because `refEnv_no_defeqs`" is **worthless as evidence**: what closes that route is
  `WF.instL_lhs_ne_sort` (`DeclRules.lean`), proved for *every* `env.WF` with no hypothesis on
  the rule set -- `badEnv_not_wf` is literally that lemma applied to `badEnv`.  So the argument
  reduces to "the general fact holds", which is the open problem.  An earlier version of this
  docstring rested on it; retracted.
* **[what is actually specific to `refEnv`, and it is a target rather than a verdict]**
  `refEnv_no_defeqs` kills the `extra` constructor outright, so at `refEnv` one whole case of
  the judgment is dead: no δ, no ι, no quotient rules.  `SortUniq refEnv 0` therefore reduces
  to beta/eta/proof-irrelevance/`trans` confluence over a pure calculus with six axioms and no
  rewrite rules -- the first *finite, self-contained* instance of this circle in the tree.
  Proving it outright would be the first non-vacuity witness for `SortUniq`, and by
  `PiLevelPin.lean`'s `piInvStratApp_iff_sortUniq` would make `PiInvStratApp refEnv 0` a
  theorem at the same time.  Not attempted here: `proofIrrel` and `trans` are the hard cases.
* **[the honest status; the escape's price is machine-checked]** satisfiability is therefore
  **open**, not settled.  What *is* settled, and unconditionally, is the price of the escape:
  rescuing `descend` requires *refuting* `SortUniq` or `UniqTyping` at a defeq-free six-axiom
  environment, and `PiLevelPin.lean`'s `not_piInvStratApp_of_not_sortUniq` -- axioms
  `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**, since only the *converse*
  direction of the equivalence routes through `WF.rigidShapeUniq` -- turns any such refutation
  into a refutation of `PiInvStratApp`, hence of `forallE_inv_stratified` and the whole Π/sort
  inversion family, *without anyone having to settle `rigidShapeUniq` first*.  Nobody should
  plan around that escape.

**This is not a proof of `False`.**  Composing it with `descendStatement_holds` derives `False`
*from `sorryAx`*, which says nothing: it is the ordinary meaning of "an open `sorry` stands
where a false statement was assumed".  The content is that `descend` must be **restated**
(`Theory/Typing/KDescend.lean` does so), not that the theory is inconsistent. -/
theorem not_descendStatement_of_wf : ¬ DescendStatement refParams :=
  not_descendStatement refEnv_sortUniq refEnv_uniqTyping


/-! ## The two `sorry`s that are **not** refuted: E3 closes from `SortUniq`

`descend`'s two "the function side is a proof" branches (`ChurchRosser.lean:1769` and
`:1801`) are the only ones this file does not refute, and they close outright from universe
uniqueness -- the same hypothesis `NormalEq.appDF_proofIrrel` already takes as `hsu`.  The
lemma is stated here rather than landed in `descend` because `descend`'s statement is
refuted and has to be restated first; this is the piece a restatement can reuse. -/

namespace VEnv

section
variable [Params]
open Params
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
set_option hygiene false in
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

/-- **The proof escape climbs an application node.**  If the function side of an `appDF`
node is a proof then the node is one too, so `descend`'s `.inr` disjunct is available at the
node above.  This is the first half of `NormalEq.appDF_proofIrrel`, split out because
`descend`'s E3 branches need the *escape*, not the `NormalEq`. -/
-- Renamed from `appDF_proof_escape`: `ChurchRosser.lean` grew a version of the same
-- conclusion that needs no `hsu`, and two identical names make the two modules
-- un-importable together (fifth occurrence of that class in this session; it is invisible
-- to a narrowed `lake build` and fatal to both measurement scripts). This is the weaker,
-- `hsu`-taking form, kept because `KDescend.lean` consumes it; it should be retired in
-- favour of the hypothesis-free one once that file settles.
theorem NormalEq.appDF_proof_escape_of_sortUniq {Γ : List VExpr} {f₁ f₂ a₁ a₂ A B P : VExpr}
    (hsu : ∀ {Δ e u v}, OnCtx Δ (IsType env univs) →
      Δ ⊢ e : .sort u → Δ ⊢ e : .sort v → u ≈ v)
    (hΓ : OnCtx Γ (IsType env univs))
    (l1 : Γ ⊢ f₁ : .forallE A B) (l2 : Γ ⊢ f₂ : .forallE A B)
    (l3 : Γ ⊢ a₁ : A) (l4 : Γ ⊢ a₂ : A) (l6 : Γ ⊢ a₁ ≡ₚ a₂)
    (hP : Γ ⊢ P : .sort .zero) (hf : Γ ⊢ f₁ : P) :
    ∃ P', (Γ ⊢ P' : .sort .zero) ∧ (Γ ⊢ .app f₁ a₁ : P') ∧ (Γ ⊢ .app f₂ a₂ : P') := by
  obtain ⟨u, hPBu⟩ := hf.uniq henv hΓ l1
  have hu0 : u ≈ .zero := hsu hΓ hPBu.hasType.1 hP
  obtain ⟨⟨uA, hA⟩, v, hB⟩ := IsType.forallE_inv henv.ordered ⟨u, hPBu.hasType.2⟩
  have himax : VLevel.imax uA v ≈ u := hsu hΓ (hA.forallE hB) hPBu.hasType.2
  have hv0 : v ≈ .zero := VLevel.imax_eq_zero.1 (himax.trans hu0)
  have hΓA : OnCtx (A::Γ) (IsType env univs) := by exact ⟨hΓ, _, hA⟩
  have hB0 : HasType env univs (A::Γ) B (.sort .zero) :=
    (IsDefEq.sortDF (hB.sort_r henv.ordered hΓA)
      (show VLevel.WF univs VLevel.zero from trivial) hv0).defeq hB
  refine ⟨B.inst a₁, hB0.instN henv.ordered .zero l3, l1.app l3, ?_⟩
  have hab := IsDefEqU.of_l henv hΓ (l6.defeq hΓ) l3
  exact (IsDefEq.instDF henv.ordered hΓ hB hab).defeq' (l2.app l4)

end

end VEnv

end Lean4Lean
