import Lean4Lean.Verify.Inductive.TrSpineProducer
import Lean4Lean.Verify.Inductive.ArgsTypedSupply
import Lean4Lean.Verify.Inductive.SortWitEnv

/-!
# The remainder of the nested flip: the datum at `e₂`, and the `ResultSortInhab` residue

`TrSpineProducer.lean` produced `TrIndDeclN.trSpine` in general, hole-free, and left exactly two
premises undischarged (its §4):

1. **`VInductDecl'.ResultSortInhab`** — sufficient, four clauses, with a residue: a block whose
   `D.lvl` is `.param i`, with no telescope binder at that level, in an environment declaring no
   `Sort u`-valued constant.  That last conjunct is not idle: `SortWitEnv.lean` *refutes*
   `VEnv.SortWitness` at the environments this corner runs at.  For such a block the producer's
   `↔` says the cost is exactly the forward direction of `VEnv.IsDefEqU.weakN_iff`.
2. **`D.ArgsTypedK K e₂ occ`**, the datum at `e₂` — carried as a premise, with the general
   extraction named (`VInductDecl'.WF.recField_canonResult`) but "the last step to `ArgsTypedH`"
   existing only at the two concrete witnesses.

## The headline: **the residue is not where it was thought to be, and the reason has nothing to
## do with `weakN_iff`**

`ResultSortInhab` was being read at the **pre-block** environment, where the only inhabitants of
`Sort D.lvl` available are a sort (`_of_succ`), a `∀ p : Prop, p` (`_of_zero`), a telescope binder
(`_of_lookup`), or a declared `Sort u`-valued constant (`_of_const`, the one `SortWitEnv.lean`
refutes).  But the bypass does not need it there.  It needs the junk value typed at **`e₁`**, and
`e₁ = env.addIndTypesC D K` **declares the block's own non-companion members**.  A member of the
block, saturated at the parameters, is a term of type `Sort D.lvl` by `VIndType.WF.canon` — the
block supplies its own `Sort u`-valued constant.

§2's `resultSortInhab_of_memberSat`/`_of_member` is that, in general: **no level condition and no
environment condition**, only that some non-companion member of `D` has an inhabited (in particular
an empty) index telescope.  §3 re-bases the whole
bypass at `e₁` so the clause can be consumed there, and §3's `spineHargsN_of_head_indexFree`
sharpens "some non-companion member" to "the **head** member", because `hcomp` makes member `0`
non-companion whenever the user's declaration list is non-empty.

`resultSortInhab_of_memberSat` is the general form, and it does not stop at index-free members:
**any** non-companion member serves, given a spine that instantiates its index telescope over the
parameters.  So the residue's final form is

> `D.lvl` neither `≈ .succ _` nor `≈ .zero`, no telescope binder at `Sort D.lvl`, no `Sort u`-valued
> constant in the environment, **and no non-companion member of the block has an index telescope
> inhabited at stage 1** — i.e. `∀ T₀ ∈ D.types, T₀.name ∉ K → ¬ ∃ is,
> e₁.HasArgs D.uvars D.params.reverse T₀.indices is`.

Index-free members are the `is = []` case, so every non-indexed nested block — which is every nested
block Lean's own elimination has ever been run on, `List`/`Option`/`Prod` nestings included — is
outside the residue for `D.lvl` **completely arbitrary**.  So is `inductive T : Nat → Sort u` nesting
(`is = [Nat.zero]` at any environment holding `Nat`).  What survives is a block all of whose own
members are indexed over telescopes with no stage-1 inhabitant at all.

**What is *not* claimed**: that the residue is empty.  No proof is offered that an index telescope
with no stage-1 inhabitant cannot occur — `inductive T : Empty → Sort u` is not refuted here.  What
*is* established is that the residue's remaining conjunct is an **inhabitation** question about the
block's own index telescopes, not a strengthening one: nothing above touches `weakN_iff`,
`AxiomConservativityWF` or `SortWitness`, and the `↔` that priced the old residue at `weakN_iff`
is simply not reached on this route.

## Item 2, the datum at `e₂`

§1's `argsTypedK_iff_hargs` is an `↔`: under the *syntactic, environment-free* side condition
`OccTeleAgree` (each foreign constructor's parameter telescope agrees with the foreign member's —
`ArgsTypedSupply.lean` §8's condition, which both witnesses satisfy by `decide`), the three-part
`ArgsTypedK` at `e₂` collapses to **one `HasArgs` per companion member**.  The `lvls` component is
not assumed, it is *read off the configuration* (`RestrictStepCfg.lvls` composed with
`Built.tyLvls`).  The forward direction needs no side condition at all.

§4 then supplies that one `HasArgs` from `D.WF` **in general** — for a foreign block presenting a
single parameter, when the recursive field nesting manufactures sits at declaration position `0`
with no binders and the foreign parameter's sort is the block's level.  `e₂` is *exactly*
`env.addIndTypes D` (the configuration's `stage₂`), which is where `WF.ctors` is staged, so the
environment mismatch `ArgsTypedSupply.lean` §9 records for §8.7's consumer does not arise here.

**The precise content of "the last step to `ArgsTypedH`", and whether it generalises.**  It is
this, and it does not generalise past position `0`: `recField_canonResult` types
`r.canonResult D i` in the context `r.binders.reverse ++ ((C.fields.take i).map (·.type)).reverse
++ D.params.reverse`, while `ArgsTypedH.ty` wants the typing in `D.params.reverse` alone.  For
`i = 0` with `r.binders = []` those two contexts are *equal*, which is why §4 is unconditional
there.  For `i > 0` the earlier field types are in the way and removing them is **strengthening** —
the forward direction of `weakN_iff`, the same statement item 1 used to bottom out at.  The
substitution trick that discharges strengthening elsewhere (substitute an inhabitant) is not
available: the binders being removed are constructor *field* types, which may be uninhabited.
A foreign block needing position `i > 0` is one whose nested parameter is not its first
constructor field — `ArgsTypedSupply.lean` §9's coincidence 1, now priced.

## Deliberately not used

No `VEnv.HasArgs.of_mkApp`, no `VEnv.IsDefEq.uniq`/`uniqU`, no `VEnv.AxiomConservativityWF`, no
`VEnv.StrengtheningTarget`, no `VEnv.SortWitness`.  `SortWitEnv.lean` is **not imported**,
deliberately: naming `not_sortWitness_of_restrictStepCfg₃` in a statement here would put
`VEnv.SortWitness` into these declarations' cones, and the point of §2 is that this route does not
touch it.  No structure gains a field and no frozen file is touched.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkApp bvars instAll splitPis liftTele)

/-! ## §1 The datum at `e₂`, reduced to ONE `HasArgs` per companion member -/

namespace VInductDecl'

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
  {occ : Nat → VNestedOcc}

/-- The syntactic side condition. -/
def OccTeleAgree (occ : Nat → VNestedOcc) (D : VInductDecl') (K : List Name) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ C' ∈ (occ j).src.ctors,
      (splitPis (occ j).decl.np ((C'.type (occ j).decl (occ j).idx).instL (occ j).lvls)).1
        = (splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1

theorem argsTypedK_iff_hargs (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (hag : OccTeleAgree occ D K) :
    D.ArgsTypedK K e₂ occ ↔
      ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
        e₂.HasArgs D.uvars D.params.reverse
          (splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1 (occ j).args := by
  refine ⟨fun h j T hT hK => (h j T hT hK).ty, fun h j T hT hK => ?_⟩
  refine VNestedOcc.argsTypedH_of_ty ?_ (hag j T hT hK) (h j T hT hK)
  rw [← C.built.tyLvls j T hT hK]
  exact C.lvls j T hT hK

/-! ## §2 `ResultSortInhab` from the block's OWN member constant -/

/-- **THE GENERAL FORM: an INDEXED member also serves, given any inhabiting spine for its index
telescope.**  `is` is a spine over the parameters alone; the block's own member saturated at the
parameters and at `is` is a term of type `Sort D.lvl`.  `resultSortInhab_of_member` is `is = []`. -/
theorem resultSortInhab_of_memberSat {e : VEnv} {j : Nat} {T₀ : VIndType} {is : List VExpr}
    (henv : e.Ordered) (hD : D.WF env) (hle : env ≤ e)
    (hj : D.types[j]? = some T₀)
    (hc : e.constants T₀.name = some ⟨D.uvars, T₀.type⟩)
    (hsat : e.HasArgs D.uvars D.params.reverse T₀.indices is) :
    D.ResultSortInhab e
      (fun T => D.tyApp j T.indices.length (is.map (·.liftN T.indices.length 0))) := by
  have hmem : T₀ ∈ D.types := List.mem_of_getElem? hj
  have hp : OnCtx D.params.reverse (e.IsType D.uvars) :=
    OnCtx.mono (fun hh => hh.mono hle) hD.params
  have hT₀ : VIndType.WF e D T₀ := (hD.types T₀ hmem).mono hle
  have hlw : T₀.type.LevelWF D.uvars := by
    obtain ⟨_, hu⟩ := hT₀.isType
    exact (hu.levelWF trivial).1
  have hconst : e.HasType D.uvars [] (.const T₀.name D.ownLvls) T₀.type := by
    have h0 := VEnv.HasType.const (Γ := ([] : List VExpr)) (U := D.uvars)
      (ls := D.ownLvls) hc (fun _ h => VLevel.params_wf h) (by simp)
    rwa [show VExpr.instL D.ownLvls T₀.type = T₀.type from hlw.instL_id] at h0
  obtain ⟨_, hcanon⟩ := hT₀.canon
  have hf : e.HasType D.uvars [] (.const T₀.name D.ownLvls)
      (mkPi D.params (mkPi T₀.indices (.sort D.lvl))) := by
    rw [← VExpr.mkPi_append]; exact hcanon.defeq hconst
  intro T hT
  have hΓ₁ : OnCtx (T.indices.reverse ++ D.params.reverse) (e.IsType D.uvars) :=
    ((hD.types T hT).mono hle).indices
  have W : Ctx.LiftN T.indices.length 0 (D.params.reverse ++ [])
      (T.indices.reverse ++ D.params.reverse) := by
    simpa using Ctx.LiftN.zero T.indices.reverse (by simp)
  have hfc : VExpr.ClosedN (VExpr.const T₀.name D.ownLvls) 0 := trivial
  have h1 := VEnv.HasType.appBVars (env := e) (U := D.uvars) (As := D.params)
    (Γ := ([] : List VExpr)) henv (by simpa using hp) hf
  rw [hfc.liftN_eq (Nat.zero_le _)] at h1
  have h2 := h1.weakN henv W
  rw [VExpr.liftN_mkApp_bvars_lo (Nat.le_refl 0), hfc.liftN_eq (Nat.zero_le _),
    VExpr.liftN_mkPi, Nat.zero_add] at h2
  have hsat' : e.HasArgs D.uvars (D.params.reverse ++ []) T₀.indices is := by
    simpa using hsat
  have h3 := VEnv.HasType.mkApp' (VEnv.HasArgs.weakN henv W hsat') h2
  rw [← VExpr.mkApp_append] at h3
  rw [show VExpr.liftN T.indices.length (VExpr.sort D.lvl) T₀.indices.length
    = VExpr.sort D.lvl from rfl, VExpr.instAll_sort] at h3
  simpa [VInductDecl'.tyApp, VInductDecl'.np, hj] using h3

/-- **The block's own index-free member, saturated at the parameters, inhabits `Sort D.lvl`.**
`is = []` of the general form below. -/
theorem resultSortInhab_of_member {e : VEnv} {j : Nat} {T₀ : VIndType}
    (henv : e.Ordered) (hD : D.WF env) (hle : env ≤ e)
    (hj : D.types[j]? = some T₀) (hni : T₀.indices = [])
    (hc : e.constants T₀.name = some ⟨D.uvars, T₀.type⟩) :
    D.ResultSortInhab e (fun T => D.tyApp j T.indices.length []) :=
  resultSortInhab_of_memberSat (is := []) henv hD hle hj hc
    (by rw [hni]; exact VEnv.HasArgs.nil)

/-- The member constant is declared at stage 1 when the member is not a companion. -/
theorem constants_stage₁_of_not_mem_K (C : RestrictStepCfg D R K env e₂ e₁ occ)
    {T₀ : VIndType} (hmem : T₀ ∈ D.types) (hK : T₀.name ∉ K) :
    e₁.constants T₀.name = some ⟨D.uvars, T₀.type⟩ := by
  refine VEnv.addConstList_constants C.stage₁ (T₀.name, ⟨D.uvars, T₀.type⟩) ?_
  rw [VInductDecl'.typeConstsC, List.mem_filterMap]
  exact ⟨(T₀.name, ⟨D.uvars, T₀.type⟩),
    List.mem_map.2 ⟨T₀, hmem, rfl⟩, if_neg hK⟩

/-- **THE RESIDUE'S PREMISE, DISCHARGED AT STAGE 1** with no level and no environment
condition: the block's own index-free non-companion member is the witness. -/
theorem resultSortInhab_stage₁_of_member (C : RestrictStepCfg D R K env e₂ e₁ occ)
    {j : Nat} {T₀ : VIndType} (hj : D.types[j]? = some T₀) (hni : T₀.indices = [])
    (hK : T₀.name ∉ K) :
    D.ResultSortInhab e₁ (fun T => D.tyApp j T.indices.length []) :=
  resultSortInhab_of_member C.ordered₁ C.wf C.le₁ hj hni
    (constants_stage₁_of_not_mem_K C (List.mem_of_getElem? hj) hK)

/-- The general form at stage 1: any non-companion member whose index telescope is inhabited over
the parameters. -/
theorem resultSortInhab_stage₁_of_memberSat (C : RestrictStepCfg D R K env e₂ e₁ occ)
    {j : Nat} {T₀ : VIndType} {is : List VExpr} (hj : D.types[j]? = some T₀)
    (hK : T₀.name ∉ K) (hsat : e₁.HasArgs D.uvars D.params.reverse T₀.indices is) :
    D.ResultSortInhab e₁
      (fun T => D.tyApp j T.indices.length (is.map (·.liftN T.indices.length 0))) :=
  resultSortInhab_of_memberSat C.ordered₁ C.wf C.le₁ hj
    (constants_stage₁_of_not_mem_K C (List.mem_of_getElem? hj) hK) hsat

/-! ## §3 The bypass at stage 1 is ALREADY IN THE TREE — and its own verdict on it is false

`SortWitEnv.lean` §2a already re-bases the bypass at `e₁`
(`VInductDecl'.junkVal_hasType₁`, `VInductDecl'.companionVals_junk₁`,
`VIndRestore.argsTypedK_of_resultSortInhab₁`), so nothing of that is re-proved here — a first draft
of this file did re-prove all three, and `scripts/sorry-census-all.lean` caught the duplicate names
outright.  They are used verbatim below.

**But the docstring that introduces them draws the wrong conclusion**, and §5's witness refutes it:

> Note what this does *not* buy at a nested block: `e₁` is `env` plus the block's **non**-companion
> type constants, whose declared types are `Π params indices, Sort D.lvl` — a sort only when the
> block has no parameters and the member no indices.  At `ntreeAux` (params `[Type u]`) they are
> `.forallE`s, so the `e₁` form fails there exactly as the `env` form does (§1).

The premise is right and the inference is not.  `ResultSortInhab` does not ask for a constant *whose
type is a sort*; it asks for a **term** of type `Sort D.lvl` over each member's telescope.  A member
constant whose type is `Π params indices, Sort D.lvl` supplies one as soon as it is **saturated** —
and the parameters and indices are exactly what the telescope `ResultSortInhab` quantifies over
provides.  So the `e₁` form buys precisely what §2 extracts, at `ntreeAux` included
(`InductiveDeclExamples.ntreeAux_trSpine_of_member`, §5, arity 0).  The search for a `SortWitness`
was a search for the wrong thing. -/

end VInductDecl'

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
  {occ : Nat → VNestedOcc}

/-- The general form: the field from any non-companion member whose index telescope is inhabited
over the parameters. -/
theorem spineHargsN_of_memberSat {types : List Lean.InductiveType}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    {j : Nat} {T₀ : VIndType} {is : List VExpr} (hj : D.types[j]? = some T₀)
    (hK : T₀.name ∉ K) (hsat : e₁.HasArgs D.uvars D.params.reverse T₀.indices is)
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    R.SpineHargsN D K env types := by
  refine spineHargsN_of_spineHargsC hcomp fun e h₁ => ?_
  cases Option.some.inj (h₁.symm.trans C.stage₁)
  exact .of_spineHargsK C.built (cyc_datum_to_spine
    (argsTypedK_of_resultSortInhab₁ C H₂
      (VInductDecl'.resultSortInhab_stage₁_of_memberSat C hj hK hsat)).2)

/-- **THE RESIDUE, BOUNDED, IN ITS FINAL FORM.**  The head member of the block, with any inhabiting
spine for its index telescope at stage 1.  `types ≠ []` makes member `0` non-companion. -/
theorem spineHargsN_of_head_sat {types : List Lean.InductiveType}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    {T₀ : VIndType} {is : List VExpr} (hj : D.types[0]? = some T₀)
    (hsat : e₁.HasArgs D.uvars D.params.reverse T₀.indices is) (hty : types ≠ [])
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    R.SpineHargsN D K env types :=
  spineHargsN_of_memberSat C H₂ hj
    (fun hK => hty (List.eq_nil_of_length_eq_zero (Nat.le_zero.1 ((hcomp 0 T₀ hj).1 hK))))
    hsat hcomp

/-- The index-free specialisation, kept because it is the shape every nesting Lean's own
elimination runs on has. -/
theorem spineHargsN_of_member {types : List Lean.InductiveType}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    {j : Nat} {T₀ : VIndType} (hj : D.types[j]? = some T₀) (hni : T₀.indices = [])
    (hK : T₀.name ∉ K)
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    R.SpineHargsN D K env types :=
  spineHargsN_of_memberSat (is := []) C H₂ hj hK (by rw [hni]; exact VEnv.HasArgs.nil) hcomp

/-- **THE RESIDUE, BOUNDED.**  If the *head* member of the block is index-free, the field holds —
whatever `D.lvl` is, and whatever the environment declares.  `types ≠ []` makes member `0`
non-companion through `hcomp`, so no separate `∉ K` premise is needed. -/
theorem spineHargsN_of_head_indexFree {types : List Lean.InductiveType}
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    {T₀ : VIndType} (hj : D.types[0]? = some T₀) (hni : T₀.indices = [])
    (hty : types ≠ [])
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    R.SpineHargsN D K env types :=
  spineHargsN_of_member C H₂ hj hni
    (fun hK => hty (List.eq_nil_of_length_eq_zero (Nat.le_zero.1 ((hcomp 0 T₀ hj).1 hK)))) hcomp

end VIndRestore

/-- **`trSpine` DISCHARGED AT A CONSTRUCTION SITE, WITH NO LEVEL PREMISE.**  The companion of
`TrSpineProducer.lean`'s `trIndDeclN_of_succLevel`: where that one needs `D.lvl ≈ .succ v`, this
one needs only that the block's head member is index-free. -/
theorem trIndDeclN_of_head_indexFree {env e₂ e₁ : VEnv} {Us : List Name}
    {nparams numNested : Nat} {types : List Lean.InductiveType} {iu : Bool}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore} {occ : Nat → VNestedOcc}
    {T₀ : VIndType}
    (hrest : R.SpineHargsN D K env types →
      TrIndDeclN env Us nparams types iu numNested D K R)
    (C : RestrictStepCfg D R K env e₂ e₁ occ) (H₂ : D.ArgsTypedK K e₂ occ)
    (hj : D.types[0]? = some T₀) (hni : T₀.indices = []) (hty : types ≠ [])
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      (T.name ∈ K ↔ types.length ≤ j)) :
    TrIndDeclN env Us nparams types iu numNested D K R :=
  hrest (VIndRestore.spineHargsN_of_head_indexFree C H₂ hj hni hty hcomp)

/-! ## §4 The general `D.WF` route to the ONE `HasArgs`, and its exact gap -/

namespace VNestedOcc

/-- **THE DATUM AT `e₂` FROM `D.WF`, IN GENERAL** for a foreign block presenting a single
parameter, when the manufactured recursive field sits at declaration position `0` with no
binders.  This is `VInductDecl'.WF.recField_canonResult` with the telescope arithmetic done once
and for all, instead of at each witness. -/
theorem argsTypedH_ty_of_recField {N : VNestedOcc} {D : VInductDecl'} {env e₂ : VEnv}
    (hwf : D.WF env) (het : env.addIndTypes D = some e₂)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors)
    {F : VIndField} (hF : C.fields[0]? = some F) {r : VIndRecArg} (hr : F.recArg = some r)
    (hb : r.binders = [])
    (htele : (splitPis N.decl.np (N.src.type.instL N.lvls)).1 = [.sort D.lvl])
    (hargs : N.args = [r.canonResult D 0]) :
    e₂.HasArgs D.uvars D.params.reverse
      (splitPis N.decl.np (N.src.type.instL N.lvls)).1 N.args := by
  have h := hwf.recField_canonResult het hT hC hF hr
  rw [hb] at h
  simp only [List.take_zero, List.map_nil, List.reverse_nil, List.nil_append] at h
  rw [htele, hargs]
  exact .cons h .nil

end VNestedOcc

/-! ## §5 The witness at the parameterised nested block, arity 0, general route only -/

namespace InductiveDeclExamples

/-- **THE FIELD AT `ntreeAux`, THROUGH THE LEVEL-FREE ROUTE.**  Nothing hypothesised.  Compare
`TrSpineProducer.lean` §3's `ntreeAux_trSpine`, which fires `resultSortInhab_of_succ` and so
needs `ntreeAux.lvl ≈ .succ _`: this one supplies the same field with **no premise about
`ntreeAux.lvl` at all**, from the block's own head member `NTree` being index-free. -/
theorem ntreeAux_trSpine_of_member :
    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      ntreeRestore.SpineHargsN ntreeAux ntreeK env₁ [ntreeIndType] := by
  obtain ⟨env₁, env₂, -, env₃, -, h, h₂, -, h₃, -⟩ := ntree_stage₂_exists
  exact ⟨env₁, h, VIndRestore.spineHargsN_of_head_indexFree
    (ntreeAux_restrictStepCfg h h₂ h₃) (ntreeAux_argsTypedK_of_wf h₂)
    (T₀ := ntreeAux.types.getD 0 default) rfl (by decide) (by decide) ntreeAux_companions⟩

/-- …and the `trSpine` field text itself, at the witness, from the same route. -/
theorem ntreeAux_trSpine_text_of_member :
    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      ∀ e, env₁.addIndTypesC ntreeAux ntreeK = some e →
        ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T →
          ([ntreeIndType] : List Lean.InductiveType).length ≤ j →
          ∀ ci : VConstant, env₁.constants (ntreeRestore.tyName j) = some ci →
            e.HasArgs ntreeAux.uvars ntreeAux.params.reverse
              (splitPis (ntreeRestore.tyArgs j).length (ci.type.instL (ntreeRestore.tyLvls j))).1
              (ntreeRestore.tyArgs j) := by
  obtain ⟨env₁, h, hs⟩ := ntreeAux_trSpine_of_member
  exact ⟨env₁, h, hs⟩

/-- **THE `D.WF` ROUTE OF §4, FIRING AT THE WITNESS.**  So `argsTypedH_ty_of_recField` is not a
statement about an empty class: at `ntreeAux`/`listOcc` the manufactured recursive field of
`_nested.List_1.cons` sits at position `0` with no binders, `List`'s parameter telescope is
`[Sort (u+1)]`, and `r.canonResult` **is** the spine's only argument. -/
theorem ntree_hargs_of_recField {env₁ e₂ : VEnv} (het : env₁.addIndTypes ntreeAux = some e₂) :
    e₂.HasArgs ntreeAux.uvars ntreeAux.params.reverse
      (splitPis listOcc.decl.np (listOcc.src.type.instL listOcc.lvls)).1 listOcc.args :=
  VNestedOcc.argsTypedH_ty_of_recField ntreeAux_WF' het
    (show ntreeAux.types[1]? = some (ntreeAux.types.getD 1 default) from rfl)
    (C := nlistCons) (List.mem_cons_of_mem _ List.mem_cons_self)
    (F := nlistCons.fields.getD 0 default) rfl
    (r := ⟨[], 0, []⟩) rfl rfl (by decide) (by decide)

/-- …hence the datum at `e₂` at the witness, through §1's `↔` and §4's general route rather than
through the two block-specific `listOcc_argsTypedH_of_wf`/`pfnOcc_argsTypedH_of_wf`. -/
theorem ntree_argsTypedK_of_recField {env₁ env₂ env₃ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (h₂ : env₁.addIndTypes ntreeAux = some env₂)
    (h₃ : env₁.addIndTypesC ntreeAux ntreeK = some env₃) :
    ntreeAux.ArgsTypedK ntreeK env₂ (fun _ => listOcc) :=
  (VInductDecl'.argsTypedK_iff_hargs (ntreeAux_restrictStepCfg h h₂ h₃)
    (fun _ _ _ _ => listOcc_ctorTele_agree)).2 fun _ _ _ _ => ntree_hargs_of_recField h₂

/-- **THE INHABITANT IS THE BLOCK'S OWN HEAD MEMBER**, computed: `NTree #0`, at the parameter
telescope.  So the value the bypass substitutes for the companion is a λ-abstraction of the
*declared* member, not a sort — which is why no level condition enters. -/
example : ntreeAux.tyApp 0 ((ntreeAux.types.getD 1 default).indices.length) []
    = .app (.const ``NTree [.param 0]) (.bvar 0) := rfl

/-- Non-degeneracy: the head member really is index-free and really is outside `ntreeK`, and the
companion really is inside it — so the route is not firing on an empty side condition. -/
example : (ntreeAux.types.getD 0 default).indices = [] := rfl
example : (ntreeAux.types.getD 0 default).name ∉ ntreeK := by decide
example : (ntreeAux.types.getD 1 default).name ∈ ntreeK := by decide
/-- And for contrast, the block this file is **not** using. -/
example : nfnAux.uvars = 0 ∧ nfnAux.params = [] := ⟨rfl, rfl⟩

end InductiveDeclExamples

end Lean4Lean

/-! ## §6 Grading: hole-freeness, per declaration -/

#print axioms Lean4Lean.VInductDecl'.argsTypedK_iff_hargs
#print axioms Lean4Lean.VInductDecl'.resultSortInhab_of_memberSat
#print axioms Lean4Lean.VInductDecl'.resultSortInhab_of_member
#print axioms Lean4Lean.VInductDecl'.resultSortInhab_stage₁_of_memberSat
#print axioms Lean4Lean.VIndRestore.spineHargsN_of_memberSat
#print axioms Lean4Lean.VIndRestore.spineHargsN_of_head_sat
#print axioms Lean4Lean.VInductDecl'.constants_stage₁_of_not_mem_K
#print axioms Lean4Lean.VInductDecl'.resultSortInhab_stage₁_of_member
#print axioms Lean4Lean.VIndRestore.spineHargsN_of_member
#print axioms Lean4Lean.VIndRestore.spineHargsN_of_head_indexFree
#print axioms Lean4Lean.trIndDeclN_of_head_indexFree
#print axioms Lean4Lean.VNestedOcc.argsTypedH_ty_of_recField
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine_of_member
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_trSpine_text_of_member
#print axioms Lean4Lean.InductiveDeclExamples.ntree_hargs_of_recField
#print axioms Lean4Lean.InductiveDeclExamples.ntree_argsTypedK_of_recField
