import Lean4Lean.Verify.Inductive.FragmentWiden

/-!
# The narrow conversion step, and what the checker route would cost

`Verify/Inductive/FragmentWiden.lean` §5b exhibits a real `inductive` block — `FragEx.WithConv`,
`mk : idf Nat → WithConv` with `idf : Arr` and `Arr : Type 1 := Type → Type` — that lies inside
the syntactic fragment (`inFragment = true`, `inFragmentW = true`) and that **both** inferencers
still reject, because `piOf? (.const Arr []) = none`: the applied function's stored type is a
constant that is a `∀` only after δ.  That file's §8 concludes that repairing it "needs
`VEnv.IsDefEq`", "poisons the cone", and recommends abandoning the inferencer for the checker's
own inference run.

**This file measures that costing and finds it wrong in one direction and right in another.**

## §0 The two findings, up front

1. **The narrow conversion step is clean and it is three lines.**  `VEnv.IsDefEq.extra` is the δ
   rule — a *constructor* of `VEnv.IsDefEq` — and `VEnv.IsDefEq.defeq` (`Theory/Typing/Lemmas.lean`,
   cone **10**, zero holes, zero watched statements) is the transport.  §1's
   `hasType_delta_sort` composes them with no environment hypothesis, no `VEnv.WF`, no `Ordered`,
   no uniqueness of types, and therefore none of `IsDefEq.uniq` / `uniqU` / `checkType.WF` /
   `TrExprS.weakFV_inv`.  There is even a precedent on the very same path:
   `VEnv.isDefEq_annotationHead` (`Verify/Inductive/Add.lean:826`, cone 715, clean) already does
   δ-unfold-then-transport for `outParam`, and its own docstring says "what could have been
   unavailable is the conversion, and it is not".  *Using a constructor of the conversion relation
   is not the same as invoking the checker's `isDefEq` procedure*, and that conflation is what made
   the conversion step look expensive.
2. **What is *not* free is the side condition, and it is a genuine narrowing of the inferencer's
   premise.**  §1's lemma needs the δ-rule's *stored type* to be **syntactically** a `.sort`
   (§1.3 shows why: without it the step needs `HasType`'s uniqueness, which is exactly `uniq`).
   And to *find* the rule at all, the inferencer's premise must grow from `ConstLookup` — stored
   **types** only — to something that also exposes stored **values**.  That is a strictly stronger
   hypothesis than the one `TrExprSGeneral.lean` §7 boasts about, and it is the honest price of
   route (i).

So the design choice is not "clean fragment vs. contaminated checker".  It is "a slightly stronger
lookup premise, staying clean" vs. "no new premise, reusing contamination the artifact already
carries".  `docs/handoff-checkerroute.md` §2 has the measured numbers for both.

## §1 What the lemma needs, and what it does not

`hasType_delta_sort` takes: the rule is in the environment, its levels are well-formed and of the
right count, its instantiated **type** is a `.sort`, and the term has the rule's instantiated
**lhs** as a type.  It concludes the term has the instantiated **rhs** as a type.  Nothing else.

Note that its hypothesis and conclusion have the *same shape*, so it composes with itself: a δ
**chain** `c₁ ↝ c₂ ↝ … ↝ ∀` is handled by iterating it, with each step needing only its own rule's
type to be a sort.  No confluence, no normalisation, no fuel-correctness argument.

## §2 The arity-0 instantiation, at the real block

§2 builds `convEnv`, whose `constants` field is **literally `FragEx.convGc`** — the faithful
transcription of Lean's own stored types, which `FragmentWiden.lean` §5b checked against `repr` —
and whose single δ-rule is `Arr ↝ Type → Type`.  `convEnv_arrRule_wf` proves that rule is
`VDefEq.WF`, so the environment is not a fabrication built to make the lemma fire.  Then
`withConv_field_isType` types the **field type of the real constructor** (`idf Nat`), and
`withConv_ctorType_isType` types the whole stored constructor type, both at that environment and
both through §1's single δ step.  `withConv_conversion_witness` is the arity-0 conjunction, and its
first component re-states `FragEx.withConv_ctorTr?_none`, so the witness carries its own evidence
that this is precisely the term the inferencers cannot reach.
-/

set_option autoImplicit false

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 The narrow conversion step -/

/-- **δ at a sort-typed rule, transported into `HasType`.**  If the environment carries a δ-rule
whose instantiated type is *syntactically* a sort, then any term typed by the rule's instantiated
lhs is typed by its instantiated rhs.

This is `VEnv.IsDefEq.extra` (the δ constructor) followed by `VEnv.IsDefEq.defeq` (which is
`.defeqDF`, another constructor).  It assumes **no** `VEnv.WF`, **no** `Ordered`, and no
uniqueness of types. -/
theorem hasType_delta_sort {env : VEnv} {U : Nat} {Γ : List VExpr} {df : VDefEq}
    {ls : List VLevel} {u : VLevel} {a b e : VExpr}
    (hdf : env.defeqs df) (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = df.uvars)
    (hlhs : df.lhs.instL ls = a) (hrhs : df.rhs.instL ls = b)
    (hty : df.type.instL ls = .sort u)
    (h : env.HasType U Γ e a) : env.HasType U Γ e b := by
  have hx := VEnv.IsDefEq.extra (Γ := Γ) hdf hls hlen
  rw [hlhs, hrhs, hty] at hx
  exact hx.defeq h

/-- **The shape the brief asks for**: `HasType f (.const c ls')` plus "`c`'s stored value unfolds
to a product" gives `HasType f (.forallE A B)`.  A specialisation of `hasType_delta_sort`, spelled
out so the statement can be matched against the `piOf?` failure verbatim. -/
theorem hasType_forallE_of_delta_const {env : VEnv} {U : Nat} {Γ : List VExpr} {df : VDefEq}
    {ls ls' : List VLevel} {u : VLevel} {c : Name} {A B f : VExpr}
    (hdf : env.defeqs df) (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = df.uvars)
    (hlhs : df.lhs.instL ls = .const c ls') (hrhs : df.rhs.instL ls = .forallE A B)
    (hty : df.type.instL ls = .sort u)
    (h : env.HasType U Γ f (.const c ls')) : env.HasType U Γ f (.forallE A B) :=
  hasType_delta_sort hdf hls hlen hlhs hrhs hty h

/-- **…and the `.app` case's conclusion, which is what the inferencer actually needs.**  This is
exactly the step `ctorTr?`/`ctorTrW?` cannot take: `piOf?` returns `none`, so the `.app` case dies
(`ctorTr?_app_eq_none_of_not_piOf`), yet the application *is* typed. -/
theorem hasType_app_of_delta_const {env : VEnv} {U : Nat} {Γ : List VExpr} {df : VDefEq}
    {ls ls' : List VLevel} {u : VLevel} {c : Name} {A B f x : VExpr}
    (hdf : env.defeqs df) (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = df.uvars)
    (hlhs : df.lhs.instL ls = .const c ls') (hrhs : df.rhs.instL ls = .forallE A B)
    (hty : df.type.instL ls = .sort u)
    (hf : env.HasType U Γ f (.const c ls')) (hx : env.HasType U Γ x A) :
    env.HasType U Γ (.app f x) (B.inst x) :=
  (hasType_forallE_of_delta_const hdf hls hlen hlhs hrhs hty hf).app hx

/-! ### §1.3 Why the "type is syntactically a sort" side condition cannot simply be dropped

The obvious weakening — replace `df.type.instL ls = .sort u` by `env.IsType U Γ (df.lhs.instL ls)`
— is *not* available cheaply.  `IsType` gives `HasType (lhs) (.sort u)` for **some** `u`, while
`.extra` gives the δ-equation at `df.type.instL ls`; identifying the two is uniqueness of types,
i.e. `VEnv.IsDefEq.uniq`, which is one of the watched statements.  So the side condition is not
bookkeeping: it is exactly the boundary between the clean route and the contaminated one, and it is
**decidable** (a syntactic test on the rule the lookup returns). -/

/-! ## §2 The arity-0 instantiation at `FragEx.WithConv` -/

namespace FragEx

/-- `Arr ↝ Type → Type`, at `Arr`'s stored type `Type 1`.  This is Lean's own δ-rule for the `def`
in `FragmentWiden.lean` §5b, transcribed. -/
def arrRule : VDefEq where
  uvars := 0
  lhs := .const ``FragEx.Arr []
  rhs := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  type := .sort (.succ (.succ .zero))

/-- The faithful environment: **`constants` is `convGc` itself**, plus the one δ-rule. -/
def convEnv : VEnv where
  constants := convGc
  defeqs := (· = arrRule)

theorem convEnv_constants : convEnv.constants = convGc := rfl

theorem convEnv_defeqs_arrRule : convEnv.defeqs arrRule := rfl

/-- `Type` is a type, at every context. -/
private theorem hsort0 {Γ : List VExpr} :
    convEnv.HasType 0 Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sortDF trivial trivial (VLevel.equiv_def'.2 rfl)

/-- **The δ-rule is well-formed at `convEnv`.**  So §2's environment is not rigged: both sides of
the rule really do have the stated type. -/
theorem convEnv_arrRule_wf : arrRule.WF convEnv := by
  refine ⟨?_, ?_⟩
  · exact VEnv.HasType.const (ci := ⟨0, .sort (.succ (.succ .zero))⟩) rfl nofun rfl
  · have hpi := VEnv.HasType.forallE (u := .succ (.succ .zero)) (v := .succ (.succ .zero))
      (hsort0 (Γ := [])) (hsort0 (Γ := [.sort (.succ .zero)]))
    refine VEnv.IsDefEq.defeq (u := .succ (.imax (.succ (.succ .zero)) (.succ (.succ .zero))))
      (.sortDF ⟨trivial, trivial⟩ trivial VLevel.imax_self) hpi

/-- `idf`'s **stored** type is the bare constant `Arr` — this is `convGc`'s row, unchanged. -/
theorem idf_hasType_const :
    convEnv.HasType 0 [] (.const ``FragEx.idf []) (.const ``FragEx.Arr []) :=
  VEnv.HasType.const (ci := ⟨0, .const ``FragEx.Arr []⟩) rfl nofun rfl

/-- **The conversion fires.**  One δ step turns the un-unfolded constant into the `∀` that
`piOf?` demanded and could not find. -/
theorem idf_hasType_forallE :
    convEnv.HasType 0 [] (.const ``FragEx.idf [])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  hasType_forallE_of_delta_const (ls := []) convEnv_defeqs_arrRule nofun rfl rfl rfl rfl
    idf_hasType_const

/-- **The real constructor's field type is a type.**  `WithConv.mk : idf Nat → WithConv`, so
`idf Nat` is the field; here it is, typed, at the faithful environment. -/
theorem withConv_field_isType : convEnv.IsType 0 [] (.app (.const ``FragEx.idf []) (.const ``Nat [])) :=
  ⟨_, idf_hasType_forallE.app (VEnv.HasType.const (ci := ⟨0, .sort (.succ .zero)⟩) rfl nofun rfl)⟩

/-- …and so is the whole stored constructor type `idf Nat → WithConv`. -/
theorem withConv_ctorType_isType :
    convEnv.IsType 0 []
      (.forallE (.app (.const ``FragEx.idf []) (.const ``Nat [])) (.const ``FragEx.WithConv [])) :=
  withConv_field_isType.forallE
    ⟨_, VEnv.HasType.const (ci := ⟨0, .sort (.succ .zero)⟩) rfl nofun rfl⟩

/-- **The arity-0 witness.**  Component 1 is the predecessor round's failure, restated; components
2-3 say the environment is faithful and its δ-rule well-formed; components 4-6 are the conversion
and its payoff at the real block. -/
theorem withConv_conversion_witness :
    ctorTr? convGc [] (exprOf% FragEx.WithConv.mk) [] = none ∧
    ctorTrW? convGc [] (exprOf% FragEx.WithConv.mk) [] = none ∧
    convEnv.constants = convGc ∧
    arrRule.WF convEnv ∧
    convEnv.HasType 0 [] (.const ``FragEx.idf []) (.const ``FragEx.Arr []) ∧
    convEnv.HasType 0 [] (.const ``FragEx.idf [])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) ∧
    convEnv.IsType 0 []
      (.forallE (.app (.const ``FragEx.idf []) (.const ``Nat [])) (.const ``FragEx.WithConv [])) :=
  ⟨withConv_ctorTr?_none, withConv_ctorTrW?_none, convEnv_constants, convEnv_arrRule_wf,
    idf_hasType_const, idf_hasType_forallE, withConv_ctorType_isType⟩

end FragEx

/-! ## §3 One δ step is not the general case either — two more real escapes

§2 closes the *exhibited* counterexample.  It does not close the class, and the honest way to say so
is to exhibit the next two escapes rather than to reason about them.  Both blocks below are accepted
by Lean's own kernel (their presence in this file is the certificate), both have stored constructor
types built from `.app`, `.forallE`, `.const` **only** — so both are inside the *original*
syntactic fragment, `inFragment = true` — and neither is reachable by §1's single δ step.

* `WithBeta`: `g3`'s stored type is the bare constant `Arr3`, and `Arr3`'s stored **value** is
  `@id (Sort 2) (Type → Type)` — an *application*, not a `∀`.  So `hasType_forallE_of_delta_const`'s
  `hrhs` premise is **false at the real rule** (`arr3Rule_rhs_not_forallE`).  Closing it needs δ on
  `id` and then two β steps.
* `WithProj`: `g5`'s stored type is `Box.fld bx`, which is not even a `.const`
  (`g5Type_not_const`), so §1 does not apply in *shape*.  Reducing it needs δ on `Box.fld`, β, and
  then a **projection reduction** — and projection reduction in the translated world is
  `TrProj`, whose `TrProj.weak'_inv` is one of the thirteen census holes.

Read together with §2 this is the pricing result: each widening of `piOf?` closes one reduction rule
and exposes the next, and the fixpoint of that process is `whnf`.  A verified `whnf` is
`TypeChecker`.  `docs/handoff-checkerroute.md` §3 draws the conclusion. -/

namespace DeltaBoundary

/-- `Arr3 : Type 1 := id (Type → Type)` — unfolds to an application, not a `∀`. -/
def Arr3 : Type 1 := id (Type → Type)
/-- …and an inhabitant, whose stored type is the bare constant `Arr3`. -/
def g3 : Arr3 := fun α => α

/-- Accepted by Lean's kernel. -/
inductive WithBeta : Type where
  | mk : g3 Nat → WithBeta

/-- A structure, so that a field type can hide behind a projection. -/
structure Box where
  fld : Type 1
def bx : Box := ⟨Type → Type⟩
/-- `g5`'s stored type is `Box.fld bx`, an application. -/
def g5 : bx.fld := fun (α : Type) => α

/-- Accepted by Lean's kernel. -/
inductive WithProj : Type where
  | mk : g5 Nat → WithProj

/-- The faithful lookup for the β escape (each row transcribed from the stored type). -/
def betaGc : Name → Option VConstant := fun n =>
  if n = ``Arr3 then some ⟨0, .sort (.succ (.succ .zero))⟩
  else if n = ``g3 then some ⟨0, .const ``Arr3 []⟩
  else if n = ``Nat then some ⟨0, .sort (.succ .zero)⟩
  else if n = ``WithBeta then some ⟨0, .sort (.succ .zero)⟩
  else none

/-- The faithful lookup for the projection escape. -/
def projGc : Name → Option VConstant := fun n =>
  if n = ``g5 then some ⟨0, .app (.const ``Box.fld []) (.const ``bx [])⟩
  else if n = ``Nat then some ⟨0, .sort (.succ .zero)⟩
  else if n = ``WithProj then some ⟨0, .sort (.succ .zero)⟩
  else none


/-- **Faithfulness of `betaGc`'s `g3` row**, against Lean's own stored type. -/
theorem g3_storedType : (exprOf% g3) = Lean.Expr.const ``Arr3 [] := rfl
/-- **Faithfulness of `projGc`'s `g5` row**, against Lean's own stored type. -/
theorem g5_storedType :
    (exprOf% g5) = Lean.Expr.app (.const ``Box.fld []) (.const ``bx []) := rfl

theorem withBeta_inFragment : inFragment (exprOf% WithBeta.mk) = true := rfl
theorem withBeta_inFragmentW : inFragmentW (exprOf% WithBeta.mk) = true := rfl
theorem withBeta_ctorTr?_none : ctorTr? betaGc [] (exprOf% WithBeta.mk) [] = none := rfl
theorem withBeta_ctorTrW?_none : ctorTrW? betaGc [] (exprOf% WithBeta.mk) [] = none := rfl

theorem withProj_inFragment : inFragment (exprOf% WithProj.mk) = true := rfl
theorem withProj_inFragmentW : inFragmentW (exprOf% WithProj.mk) = true := rfl
theorem withProj_ctorTr?_none : ctorTr? projGc [] (exprOf% WithProj.mk) [] = none := rfl
theorem withProj_ctorTrW?_none : ctorTrW? projGc [] (exprOf% WithProj.mk) [] = none := rfl


/-- `Arr3`'s δ-rule, transcribed from its stored value. -/
def arr3Rule : VDefEq where
  uvars := 0
  lhs := .const ``Arr3 []
  rhs := .app (.app (.const ``id [.succ (.succ (.succ .zero))]) (.sort (.succ (.succ .zero))))
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
  type := .sort (.succ (.succ .zero))

/-- **§1's `hrhs` premise is false at the real rule**: one δ step yields an application. -/
theorem arr3Rule_rhs_not_forallE : ∀ A B : VExpr, arr3Rule.rhs ≠ .forallE A B := by
  rintro A B ⟨⟩

/-- …so `piOf?` still fails after the δ step. -/
theorem piOf?_arr3Rule_rhs : piOf? arr3Rule.rhs = none := rfl

/-- `g5`'s stored type, transcribed. -/
def g5Type : VExpr := .app (.const ``Box.fld []) (.const ``bx [])

/-- **§1 does not apply in shape**: the type to convert is not a `.const` at all. -/
theorem g5Type_not_const : ∀ (c : Name) (ls : List VLevel), g5Type ≠ .const c ls := by
  rintro c ls ⟨⟩

theorem piOf?_g5Type : piOf? g5Type = none := rfl

/-! ### §3a Positive controls: the failure is the `piOf?` step, not a missing lookup

A `= none` is worthless as evidence unless the lookup table is adequate — a table missing a constant
returns `none` for a completely different reason.  So: the **function part alone** infers, at these
very tables, and returns exactly the stored type that `piOf?` then chokes on. -/

theorem betaGc_g3_infers :
    ctorTr? betaGc [] (.const ``g3 []) [] = some (.const ``g3 [], .const ``Arr3 []) := rfl
theorem betaGc_nat_infers :
    ctorTr? betaGc [] (.const ``Nat []) [] = some (.const ``Nat [], .sort (.succ .zero)) := rfl
theorem projGc_g5_infers :
    ctorTr? projGc [] (.const ``g5 []) [] = some (.const ``g5 [], g5Type) := rfl
theorem projGc_nat_infers :
    ctorTr? projGc [] (.const ``Nat []) [] = some (.const ``Nat [], .sort (.succ .zero)) := rfl


/-- **The arity-0 statement of §3.**  Both blocks are in the fragment, both inferencers reject
both, and neither is reachable by a single δ step at a sort-typed rule. -/
theorem delta_not_general_witness :
    (inFragment (exprOf% WithBeta.mk) = true ∧ inFragmentW (exprOf% WithBeta.mk) = true ∧
      ctorTr? betaGc [] (exprOf% WithBeta.mk) [] = none ∧
      ctorTrW? betaGc [] (exprOf% WithBeta.mk) [] = none ∧
      (∀ A B : VExpr, arr3Rule.rhs ≠ .forallE A B) ∧ piOf? arr3Rule.rhs = none ∧
      ctorTr? betaGc [] (.const ``g3 []) [] = some (.const ``g3 [], .const ``Arr3 []) ∧
      ctorTr? betaGc [] (.const ``Nat []) [] = some (.const ``Nat [], .sort (.succ .zero)) ∧
      (exprOf% g3) = Lean.Expr.const ``Arr3 []) ∧
    (inFragment (exprOf% WithProj.mk) = true ∧ inFragmentW (exprOf% WithProj.mk) = true ∧
      ctorTr? projGc [] (exprOf% WithProj.mk) [] = none ∧
      ctorTrW? projGc [] (exprOf% WithProj.mk) [] = none ∧
      (∀ (c : Name) (ls : List VLevel), g5Type ≠ .const c ls) ∧ piOf? g5Type = none ∧
      ctorTr? projGc [] (.const ``g5 []) [] = some (.const ``g5 [], g5Type) ∧
      ctorTr? projGc [] (.const ``Nat []) [] = some (.const ``Nat [], .sort (.succ .zero)) ∧
      (exprOf% g5) = Lean.Expr.app (.const ``Box.fld []) (.const ``bx [])) :=
  ⟨⟨withBeta_inFragment, withBeta_inFragmentW, withBeta_ctorTr?_none, withBeta_ctorTrW?_none,
      arr3Rule_rhs_not_forallE, piOf?_arr3Rule_rhs, betaGc_g3_infers, betaGc_nat_infers,
      g3_storedType⟩,
    ⟨withProj_inFragment, withProj_inFragmentW, withProj_ctorTr?_none, withProj_ctorTrW?_none,
      g5Type_not_const, piOf?_g5Type, projGc_g5_infers, projGc_nat_infers, g5_storedType⟩⟩

end DeltaBoundary

end Lean4Lean
