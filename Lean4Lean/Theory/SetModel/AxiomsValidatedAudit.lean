import Lean4Lean.Theory.SetModel.CnstRecursion

/-!
# `AxiomsValidated` is not an independent obligation

`docs/soundness-ledger.md` lists `AxiomsValidated` (`SetModel/InterpSound.lean:1011`) as one
of the two items still open on the model side.  This file measures it, and the measurement is
that it is **not new work at all** — which is what its own docstring claims ("the place where
work already done gets attached") but which nothing in the tree had checked.

Three results:

1. `VEnv.WF'.constants_axiom` — an `.axiom` step of a well-formed history really does leave its
   constant in the final environment, at the declared type.  This is the missing link; the
   analogous facts for `.induct` steps (`VEnv.WF'.constants_induct_type`,
   `WF'.exists_addInduct'`, `Theory/Inductive/Nested.lean`) were already there, the `.axiom`
   one was not.
2. `axiomsValidated_of_coherentOn` — **`AxiomsValidated M L ds` follows from
   `CoherentOn M L env` at any `env` with `VEnv.WF' ds env`.**  So it adds nothing to
   `CnstRecursion.lean`'s `OracleFits`, whose `.axiom` clause already carries the same content
   at the one place the recursion consumes it.  It is a *consequence* of the construction, not
   an input to it, and the soundness ledger's "Full ingredient list" should carry it as such.
3. Both bounds, per `docs/vacuity-ledger.md` §5 check 2:
   * **not trivially true** — `not_axiomsValidated_falseProp`: a history declaring
     `axiom bad : ∀ p : Prop, p` has none, because `⟦∀ p : Prop, p⟧ ∅ = ∅`;
   * **satisfiable, and not only at `ds = []`** — `axiomsValidated_extAx`: the history
     `[.axiom (Ext : Prop)]` has one, with `Ext` denoting `∅ ∈ UProp`.  The ledger notes the
     `ds = []` case is vacuous; this one is not.

One thing the measurement turns up that is worth recording separately.  Every other
model-side obligation in `InterpSound.lean` is stated under `Above M` — the "for some
threshold `m`, if `κ` carries a chain of length `m`" truncation.  `AxiomsValidated.axioms` is
**not**; it asserts the membership outright.  So it is strictly stronger than what
`CoherentOn.const_type` supplies, and the two are bridged only by `hκ : ∀ m,
IsInaccessibleChain m M.κ` — the single-`κ`-good-for-every-length input that
`CnstRecursion.InaccModelInput`'s docstring flags as a real gap ("**one `κ` per `n`**").
`axiomsValidatedAbove_of_coherentOn` is the `hκ`-free half, so the dependence is isolated
rather than hidden.
-/

namespace Lean4Lean

/-- **An `.axiom` step of a history leaves its constant in the final environment.**  The
`.induct` analogues (`VEnv.WF'.constants_induct_type`, `constants_induct_ctor`) already
existed; this one did not, and it is what `AxiomsValidated` needs. -/
theorem VEnv.WF'.constants_axiom {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    ∀ ci : VConstVal, VDecl.axiom ci ∈ ds → env.constants ci.name = some ci.toVConstant := by
  induction H with
  | empty => intro _ h; cases h
  | decl hd hds ih =>
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · cases hd with
      | «axiom» _ h => exact VEnv.addConst_self h
    · exact hd.le.constants (ih ci hci)

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

section

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

/-- **The `hκ`-free half.**  `CoherentOn` delivers the axiom obligation up to the `Above`
truncation, with no input about the chain. -/
theorem axiomsValidatedAbove_of_coherentOn {env : VEnv} {ds : List VDecl}
    (hC : CoherentOn M L env) (hwf : VEnv.WF' ds env) :
    ∀ ci : VConstVal, VDecl.axiom ci ∈ ds → ∀ {ls : List VLevel}, (∀ l ∈ ls, l.WF nv) →
      ls.length = ci.toVConstant.uvars →
      Above M (M.cnst ci.name ls ∈ (interp M L [] (ci.toVConstant.type.instL ls)).toFun ∅) :=
  by intro ci hci _ls hwfl hlen; exact hC.const_type (hwf.constants_axiom ci hci) hwfl hlen

/-- **`AxiomsValidated` is a consequence of the construction, not an input to it.**  Given
coherence at an environment the history builds, every axiom of the history is validated. -/
theorem axiomsValidated_of_coherentOn (hκ : ∀ m : ℕ, IsInaccessibleChain m M.κ)
    {env : VEnv} {ds : List VDecl} (hC : CoherentOn M L env) (hwf : VEnv.WF' ds env) :
    AxiomsValidated M L ds where
  axioms {ci} hci {_ls} hwfl hlen :=
    let ⟨m, hm⟩ := axiomsValidatedAbove_of_coherentOn hC hwf ci hci hwfl hlen
    hm (hκ m)

/-! ## Bounds

`not_axiomsValidated_falseProp` is the `AxiomsValidated` counterpart of
`CnstRecursion.not_oracleOK_falseProp`, and for the same reason: `VDecl.WF`'s `.axiom` case
asks that the declared type *be* a type, never that it be inhabited. -/

/-- **Not trivially true.**  A history declaring an axiom of type `∀ p : Prop, p` has no
`AxiomsValidated`.

Note what is *absent*: `CnstRecursion.not_oracleOK_falseProp` needs
`hκ : ∀ m, IsInaccessibleChain m κ` to collapse `Above`, and this does not — because
`AxiomsValidated.axioms` is stated without the `Above` truncation.  The asymmetry is the same
one recorded in this file's header: un-truncated makes the obligation harder to *satisfy* and
easier to *refute*. -/
theorem not_axiomsValidated_falseProp
    {ds : List VDecl} {n : Name} (hn : VDecl.axiom ⟨⟨0, falseProp⟩, n⟩ ∈ ds) :
    ¬ AxiomsValidated M L ds := by
  intro h
  have := h.axioms hn (ls := []) (by simp) rfl
  rw [show (VConstant.mk 0 falseProp).type.instL [] = falseProp from rfl,
    interp_falseProp] at this
  simp at this

/-- **Satisfiable, and not only at `ds = []`.**  `axiom Ext : Prop`, with `Ext` denoting `∅`.
The value has to lie in `⟦Sort 0⟧ = UProp`, and `∅ ∈ UProp`. -/
theorem axiomsValidated_extAx (κ : ℕ → V) (lvls : List ℕ) :
    AxiomsValidated (V := V) ⟨κ, lvls, fun _ _ ↦ ∅⟩ L [.axiom ⟨⟨0, .sort .zero⟩, `Ext⟩] where
  axioms {ci} hci {ls} _ hlen := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
    cases hci
    simp only [List.length_eq_zero_iff] at hlen
    subst hlen
    rw [show (VConstant.mk 0 (VExpr.sort .zero)).type.instL [] = VExpr.sort .zero from rfl,
      interp_falseProp_dom]
    exact empty_mem_UProp

end

end SetModel

end Lean4Lean
