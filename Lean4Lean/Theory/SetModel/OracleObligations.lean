import Lean4Lean.Theory.SetModel.InterpMkPi
import Lean4Lean.Theory.SetModel.TeleWFBridge

/-!
# The two residual obligations of structure eta, characterised against `InductOracleOK`

`SetModel.cnst_eq_singleton_of_mem_interp_recTyG` (`Theory/SetModel/InterpMkPi.lean` §5)
derives structure eta from the recursor's type obligation for an arbitrary declaration shape,
with all four `interp` equations and the three `IsProp` conditions handled elsewhere.  Two
hypotheses remain, and both are oracle data:

    hmk : M.cnst cc cus ∈ M.cnst tc tus
    hf  : f ∈ (interp M L Γ (recTyG tc cc tus cus w)).toFun ρ

This file says exactly what supplies each, and then supplies both from `InductOracleOK` alone.

## Correction to the framing this file was written against

The brief this round opened with described the second obligation as "`hf` — naming
`M.cnst cc cus` concretely, if a consumer wants a specific set (e.g. `{•}`)".  That merges two
different things, and `InterpMkPi.lean`'s own docstring already separates them:

* `hf` is **inhabitation of the recursor's type**, not a naming problem.  It is `OracleOK.type`
  at the recursor constant.
* *Naming* `M.cnst cc cus` is a third item, and it is **not a hypothesis of the eta theorem at
  all**: the conclusion `M.cnst tc tus = {M.cnst cc cus}` is already closed without it.  A
  consumer who wants `{•}` on the right rewrites with the oracle's *definition*
  (`unitOracleL_mk`), which is not an obligation on the oracle but a fact about a particular one.

So the model side's residual is **two cells of one field**, not two fields and not three items.

## What is proved here

1. **`OracleTypeCell`** (§1) — one cell of `OracleOK.type`: the obligation at one name and one
   level instantiation.  `OracleOK.type` is exactly the `∀ us`-closure of this, so a cell is the
   smallest fragment of `InductOracleOK` there is: it is one instantiation of one of the two
   fields of one of the two fields.

2. **`hmk` is that cell, up to identities — an `↔`** (§2, `mem_cnst_iff_oracleTypeCell`).  Both
   directions are the same proposition after `interp_const`, the assignment/oracle agreement at
   the constructor, and `above_iff_of_chain`.  Nothing weaker than the cell can supply `hmk`,
   because `hmk` *is* the cell.  This settles the question the brief asked to settle: there is no
   route from typing, and no smaller fragment to look for.

3. **`hf` is strictly weaker than its cell** (§3).  `f` occurs in no other hypothesis and not in
   the conclusion, so only *nonemptiness* of the recursor type's denotation is used
   (`cnst_eq_singleton_of_nonempty_interp_recTyG`).  The cell supplies it with the witness
   `o rc rus`; the converse fails, so unlike `hmk` there is deliberately no `↔` here — and that
   is a finding, not a gap: `hf` as stated asks for more than the proof consumes.

4. **Structure eta from `InductOracleOK`, with no residual model-side hypothesis** (§4,
   `cnst_eq_singleton_of_inductOracleOK`).  The oracle obligation's `consts` field at two names
   is the whole model-side input; `rules` is not consumed, and neither is `congr`.

4b. **And from `OracleFits`** (§4b, `cnst_eq_singleton_of_oracleFits`) — the form
   `coherentOn_cnstOf` actually quantifies over.  The assignment/oracle agreement §2 needs is
   free there, because `cnstOf` at an `.induct` step *is* `oracleExtend o D.allNames`
   (`cnstOf_induct_eq_oracle`).  So the model-side input reduces to one `OracleFits`.

5. **Fired at `unitDeclLE`** (§5), through `UnitAudit.inductOracleOKL` — the block's
   `InductOracleOK` witness — rather than through the unit-specific `interp` computations that
   `RecTypePeel.lean` §10 uses.  That is the difference from
   `UnitAudit.unitL_denot_eq_singleton_of_zero`: the same conclusion, but with the abstract
   obligation as the only input, so §4's bundle is checked satisfiable at a real declaration and
   the route it advertises is the route that was taken.  `unitL_denot_eq_singleton_of_oracleFits`
   does the same from `OracleFits`, and `unitL_denot_eq_singleton_omegaChain` discharges the
   chain side condition `hκ` outright at `InaccChainOmega.omegaChain`, so no hypothesis anywhere
   in the chain is left unsatisfiable.

6. **Why `ntreeAux` is not reachable** (§6), machine-checked rather than asserted: §4 inherits
   `cnst_eq_singleton_of_mem_interp_recTyG`'s three-binder shape, whose availability condition is
   `VInductDecl'.recPiTele_length_eq_three`'s `D.np = 0 ∧ D.nm = 1 ∧ D.nmin = 1`, and `ntreeAux`
   fails all three.  `ntreeAux_recPiTele_length` already records the telescope as 7 entries; §6
   records that the *hypothesis* fails, which is the actionable half.

## Foundation

Nothing here needs a Foundation lemma.  Both obligations are membership facts inside the
oracle's own data, moved across `interp`'s defining equation for `.const` and across the `Above`
wrapper; no set-theoretic construction is performed.  So the Foundation interface is not exercised
and the pin is untouched.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF env₀ : VEnv} {nv : ℕ} {κ : ℕ → V} {ls : List ℕ}

/-! ## 1. The smallest fragment: one cell of `OracleOK.type` -/

/-- **One cell of `OracleOK.type`**: what the oracle owes at *one* name and *one* level
instantiation.  `OracleOK.type` is literally the `∀ us`-closure of this, so there is no smaller
piece of `InductOracleOK` to state an obligation against. -/
def OracleTypeCell (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o c : Name → List VLevel → V) (n : Name) (ci : VConstant) (us : List VLevel) : Prop :=
  Above (V := V) ⟨κ, ls, c⟩
    (o n us ∈ (interp (⟨κ, ls, c⟩ : ModelData V) L [] (ci.type.instL us)).toFun ∅)

/-- The cell is obtained from the field by instantiating; this is the only direction used. -/
theorem OracleOK.cell {L : PropSplit envF nv} {o c : Name → List VLevel → V} {n : Name}
    {ci : VConstant} (h : OracleOK L κ ls o c n ci) {us : List VLevel}
    (hw : ∀ l ∈ us, l.WF nv) (hlen : us.length = ci.uvars) :
    OracleTypeCell L κ ls o c n ci us := h.type hw hlen

/-- The field is the cell's `∀ us`-closure, together with `congr`.  Recorded so "the cell is the
smallest fragment" is a checked statement and not a reading of the source. -/
theorem oracleOK_iff_congr_and_cells (L : PropSplit envF nv) (o c : Name → List VLevel → V)
    (n : Name) (ci : VConstant) :
    OracleOK L κ ls o c n ci ↔
      ((∀ {us us' : List VLevel}, (∀ l ∈ us, l.WF nv) → (∀ l ∈ us', l.WF nv) →
          List.Forall₂ (· ≈ ·) us us' → Above (V := V) ⟨κ, ls, c⟩ (o n us = o n us')) ∧
        ∀ us : List VLevel, (∀ l ∈ us, l.WF nv) → us.length = ci.uvars →
          OracleTypeCell L κ ls o c n ci us) :=
  ⟨fun h ↦ ⟨fun hw hw' hd ↦ h.congr hw hw' hd, fun _ hw hlen ↦ h.cell hw hlen⟩,
   fun h ↦ ⟨fun {_ _} hw hw' hd ↦ h.1 hw hw' hd, fun {_} hw hlen ↦ h.2 _ hw hlen⟩⟩

/-! ## 2. `hmk` **is** the constructor's cell — the `↔`

`hmk` has no route from typing: a typing derivation `Γ ⊢ mk : T` is interpreted *through*
`M.cnst`, so it cannot constrain which set `M.cnst` chose.  The precise replacement for a route
is this equivalence, whose point is that the two propositions differ only by `interp`'s defining
equation for `.const`, the agreement of the assignment with the oracle at the constructor, and
the `Above` wrapper.  So nobody should look for a weaker supplier. -/

/-- **`hmk` is equivalent to the constructor's `OracleOK.type` cell.**

`hty` is the shape condition — the constructor's declared type, level-instantiated, is the
saturated type former — which for a parameter-free index-free block is `rfl`.  `hco` is agreement
of the block's assignment with the oracle at the constructor, which is what `oracleExtend` gives
at a name of the block (and is `rfl` when the witness is stated at `o = c`, as
`UnitAudit.inductOracleOKL` is). -/
theorem mem_cnst_iff_oracleTypeCell (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (L : PropSplit envF nv) (o c : Name → List VLevel → V)
    {tc cc : Name} {tus cus : List VLevel} {cci : VConstant}
    (hco : c cc cus = o cc cus) (hty : cci.type.instL cus = .const tc tus) :
    OracleTypeCell L κ ls o c cc cci cus ↔
      (⟨κ, ls, c⟩ : ModelData V).cnst cc cus ∈ (⟨κ, ls, c⟩ : ModelData V).cnst tc tus := by
  rw [OracleTypeCell, above_iff_of_chain hκ, hty, interp_const]
  exact hco ▸ Iff.rfl

/-- The same read as a supply lemma, which is how §4 uses it. -/
theorem mem_cnst_of_oracleTypeCell (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (L : PropSplit envF nv) (o c : Name → List VLevel → V)
    {tc cc : Name} {tus cus : List VLevel} {cci : VConstant}
    (hco : c cc cus = o cc cus) (hty : cci.type.instL cus = .const tc tus)
    (h : OracleTypeCell L κ ls o c cc cci cus) :
    (⟨κ, ls, c⟩ : ModelData V).cnst cc cus ∈ (⟨κ, ls, c⟩ : ModelData V).cnst tc tus :=
  (mem_cnst_iff_oracleTypeCell hκ L o c hco hty).1 h

/-! ## 3. `hf` is strictly weaker than the recursor's cell

`f` occurs in exactly one hypothesis of `cnst_eq_singleton_of_mem_interp_recTyG` and not in its
conclusion, so the theorem is invariant under replacing `f` + `hf` by nonemptiness.  Stating that
is what makes "no `↔` for `hf`" precise: the cell names a particular inhabitant, the proof needs
only that there is one, so the two cannot be equivalent. -/

variable {M : ModelData V} {L : PropSplit envF nv}

/-- **The eta theorem needs only that the recursor type's denotation is nonempty.**  Identical to
`cnst_eq_singleton_of_mem_interp_recTyG` except that `f` and `hf` are replaced by an
existential. -/
theorem cnst_eq_singleton_of_nonempty_interp_recTyG (hle : env₀ ≤ envF)
    {Γ : List VExpr} {tc cc : Name} {tus cus : List VLevel} {w v0 : VLevel} {ρ : V}
    (hΓ : OnCtx Γ (env₀.IsType nv)) (hρ : ρ ∈ interpCtx M L Γ)
    (hw : w.WF nv) (hv0 : v0.WF nv) (h0 : w.eval M.ls = 0)
    (hT : ∀ Δ : List VExpr, env₀.HasType nv Δ (.const tc tus) (.sort v0))
    (hC : ∀ Δ : List VExpr, env₀.HasType nv Δ (.const cc cus) (.const tc tus))
    (hpm : L.IsProp M (motTyG tc tus w :: Γ)
      (VExpr.mkPi [minTyG cc cus, .const tc tus] recBodyG))
    (hpp : L.IsProp M (minTyG cc cus :: motTyG tc tus w :: Γ)
      (VExpr.mkPi [.const tc tus] recBodyG))
    (hpx : L.IsProp M (.const tc tus :: minTyG cc cus :: motTyG tc tus w :: Γ) recBodyG)
    (hmk : M.cnst cc cus ∈ M.cnst tc tus)
    (hf : ∃ f : V, f ∈ (interp M L Γ (recTyG tc cc tus cus w)).toFun ρ) :
    M.cnst tc tus = ({M.cnst cc cus} : V) :=
  let ⟨_, hf⟩ := hf
  cnst_eq_singleton_of_mem_interp_recTyG hle hΓ hρ hw hv0 h0 hT hC hpm hpp hpx hmk hf

/-- **The recursor's cell supplies `hf`**, with `o rc rus` as the witness.  `hty` is the shape
condition: the recursor's declared type, level-instantiated, is the three-binder eta shape. -/
theorem exists_mem_interp_of_oracleTypeCell (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (L : PropSplit envF nv) (o c : Name → List VLevel → V)
    {rc : Name} {rci : VConstant} {rus : List VLevel} {e : VExpr}
    (hty : rci.type.instL rus = e) (h : OracleTypeCell L κ ls o c rc rci rus) :
    ∃ f : V, f ∈ (interp (⟨κ, ls, c⟩ : ModelData V) L [] e).toFun ∅ :=
  ⟨o rc rus, hty ▸ (above_iff_of_chain hκ).1 h⟩

/-! ## 4. Structure eta from `InductOracleOK`, with no residual model-side hypothesis -/

/-- `∅` is a valuation of the empty context — the `hρ` the eta theorem needs at `Γ = []`,
declaration-quantified.  (`UnitAudit.interpCtxL_nil` is this at one model.) -/
theorem mem_interpCtx_nil (M : ModelData V) (L : PropSplit envF nv) :
    (∅ : V) ∈ interpCtx M L [] := by rw [interpCtx_nil]; simp

/-- **Structure eta, with `InductOracleOK` as the only model-side input.**

Everything else is typing data (`hT`, `hC`), level data (`hw`, `hv0`, `h0`), the three `IsProp`
conditions that `TeleWFBridge.isProp_recType_iff` collapses to one, and two *shape* equations
identifying the constructor's and the recursor's declared types.  The oracle obligation is
consumed only through its `consts` field, only at the constructor and the recursor, and only
through the `type` half of each: `rules` and `congr` are not used.

This is the answer to "what supplies the two residuals": one field, two names, and nothing
else. -/
theorem cnst_eq_singleton_of_inductOracleOK (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (hle : env₀ ≤ envF) {L : PropSplit envF nv} {o c : Name → List VLevel → V}
    {D : VInductDecl'} (hOK : InductOracleOK L κ ls o c D)
    {tc cc rc : Name} {cci rci : VConstant} {tus cus rus : List VLevel} {w v0 : VLevel}
    (hcmem : (cc, cci) ∈ D.allConsts) (hrmem : (rc, rci) ∈ D.allConsts)
    (hcw : ∀ l ∈ cus, l.WF nv) (hclen : cus.length = cci.uvars)
    (hrw : ∀ l ∈ rus, l.WF nv) (hrlen : rus.length = rci.uvars)
    (hco : c cc cus = o cc cus)
    (hcty : cci.type.instL cus = .const tc tus)
    (hrty : rci.type.instL rus = recTyG tc cc tus cus w)
    (hw : w.WF nv) (hv0 : v0.WF nv) (h0 : w.eval ls = 0)
    (hT : ∀ Δ : List VExpr, env₀.HasType nv Δ (.const tc tus) (.sort v0))
    (hC : ∀ Δ : List VExpr, env₀.HasType nv Δ (.const cc cus) (.const tc tus))
    (hpm : L.IsProp (⟨κ, ls, c⟩ : ModelData V) [motTyG tc tus w]
      (VExpr.mkPi [minTyG cc cus, .const tc tus] recBodyG))
    (hpp : L.IsProp (⟨κ, ls, c⟩ : ModelData V) [minTyG cc cus, motTyG tc tus w]
      (VExpr.mkPi [.const tc tus] recBodyG))
    (hpx : L.IsProp (⟨κ, ls, c⟩ : ModelData V)
      [.const tc tus, minTyG cc cus, motTyG tc tus w] recBodyG) :
    c tc tus = ({c cc cus} : V) :=
  cnst_eq_singleton_of_nonempty_interp_recTyG (M := (⟨κ, ls, c⟩ : ModelData V)) hle
    (Γ := []) trivial (mem_interpCtx_nil _ L) hw hv0 h0 hT hC hpm hpp hpx
    (mem_cnst_of_oracleTypeCell hκ L o c hco hcty
      ((hOK.consts _ hcmem).cell hcw hclen))
    (exists_mem_interp_of_oracleTypeCell hκ L o c hrty
      ((hOK.consts _ hrmem).cell hrw hrlen))

/-! ## 4b. `hco` is free at the assignment the recursion actually uses

§4 asks for `c cc cus = o cc cus`.  That is not an extra burden at the site that consumes
`InductOracleOK`: `OracleFits` states the `.induct` obligation at
`cnstOf L κ ls o (.induct D :: ds)`, which is `oracleExtend o D.allNames` of the tail's
assignment, and `oracleExtend` is the oracle at every name of the block.  So the corollary below
takes structure eta all the way to `OracleFits`, the form `coherentOn_cnstOf` consumes. -/

/-- `cnstOf` at an `.induct` step is the oracle at every name the block declares. -/
theorem cnstOf_induct_eq_oracle (L : PropSplit envF nv) (o : Name → List VLevel → V)
    {D : VInductDecl'} {ds : List VDecl} {n : Name} (hn : n ∈ D.allNames) (us : List VLevel) :
    cnstOf L κ ls o (.induct D :: ds) n us = o n us := by
  show oracleExtend o D.allNames (cnstOf L κ ls o ds) n us = _
  rw [NEAudit.oracleExtend_apply, if_pos hn]

/-- A declared constant's name is one of the block's names. -/
theorem mem_allNames_of_mem_allConsts {D : VInductDecl'} {p : Name × VConstant}
    (hp : p ∈ D.allConsts) : p.1 ∈ D.allNames :=
  List.mem_map_of_mem hp

/-- **Structure eta at the recursion's own assignment**, from `OracleFits` at the `.induct` step.
The `hco` of §4 is discharged by §4b, so the model-side input is exactly the oracle obligation
the outer recursion already quantifies over. -/
theorem cnst_eq_singleton_of_oracleFits (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (hle : env₀ ≤ envF) {L : PropSplit envF nv} {o : Name → List VLevel → V}
    {D : VInductDecl'} {ds : List VDecl}
    (hfits : OracleFits L κ ls o (.induct D :: ds))
    {tc cc rc : Name} {cci rci : VConstant} {tus cus rus : List VLevel} {w v0 : VLevel}
    (hcmem : (cc, cci) ∈ D.allConsts) (hrmem : (rc, rci) ∈ D.allConsts)
    (hcw : ∀ l ∈ cus, l.WF nv) (hclen : cus.length = cci.uvars)
    (hrw : ∀ l ∈ rus, l.WF nv) (hrlen : rus.length = rci.uvars)
    (hcty : cci.type.instL cus = .const tc tus)
    (hrty : rci.type.instL rus = recTyG tc cc tus cus w)
    (hw : w.WF nv) (hv0 : v0.WF nv) (h0 : w.eval ls = 0)
    (hT : ∀ Δ : List VExpr, env₀.HasType nv Δ (.const tc tus) (.sort v0))
    (hC : ∀ Δ : List VExpr, env₀.HasType nv Δ (.const cc cus) (.const tc tus))
    (hpm : L.IsProp (⟨κ, ls, cnstOf L κ ls o (.induct D :: ds)⟩ : ModelData V)
      [motTyG tc tus w] (VExpr.mkPi [minTyG cc cus, .const tc tus] recBodyG))
    (hpp : L.IsProp (⟨κ, ls, cnstOf L κ ls o (.induct D :: ds)⟩ : ModelData V)
      [minTyG cc cus, motTyG tc tus w] (VExpr.mkPi [.const tc tus] recBodyG))
    (hpx : L.IsProp (⟨κ, ls, cnstOf L κ ls o (.induct D :: ds)⟩ : ModelData V)
      [.const tc tus, minTyG cc cus, motTyG tc tus w] recBodyG) :
    cnstOf L κ ls o (.induct D :: ds) tc tus
      = ({cnstOf L κ ls o (.induct D :: ds) cc cus} : V) :=
  cnst_eq_singleton_of_inductOracleOK hκ hle hfits.1 hcmem hrmem hcw hclen hrw hrlen
    (cnstOf_induct_eq_oracle L o (mem_allNames_of_mem_allConsts hcmem) cus)
    hcty hrty hw hv0 h0 hT hC hpm hpp hpx

end

/-! ## 5. Fired at `unitDeclLE`, through its `InductOracleOK` witness -/

namespace UnitAudit

open Lean4Lean.SetModel.UnitAudit

section
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF)

include L hu hle in
/-- **Structure eta at `inductive Unit1 : Prop | mk`, from `InductOracleOK` and nothing else.**

`RecTypePeel.lean` §10's `unitL_denot_eq_singleton_of_zero` reaches the same conclusion by
discharging `hf` with `pt_mem_interpL_recType_of_zero` and rewriting the left-hand side with
`interpL_Unit1` — i.e. through the unit block's own `interp` computations.  This goes through
`§4` instead, so the only model-side input is `UnitAudit.inductOracleOKL`, the block's abstract
oracle witness.  That is the check that §4's hypothesis bundle is satisfiable at a real
declaration, and that the advertised route is the route taken. -/
theorem unitL_denot_eq_singleton_of_inductOracleOK
    (hκ : ∀ m : ℕ, IsInaccessibleChain m κ) (h0 : u.eval ls = 0) :
    unitOracleL κ ls `Unit1 [] = ({unitOracleL κ ls `Unit1.mk []} : V) :=
  cnst_eq_singleton_of_inductOracleOK (V := V) hκ hle
    (L := L) (o := unitOracleL κ ls) (c := unitOracleL κ ls)
    (D := unitDeclLE) (inductOracleOKL L κ ls hle)
    (tc := `Unit1) (cc := `Unit1.mk) (rc := recN)
    (cci := ⟨0, .const `Unit1 []⟩) (rci := ⟨1, unitDeclLE.recType 0⟩)
    (tus := []) (cus := []) (rus := [u]) (w := u) (v0 := .zero)
    (by rw [unitDeclLE_allConsts]; simp) (by rw [unitDeclLE_allConsts]; simp)
    nofun rfl (fun l hl ↦ by simp only [List.mem_singleton] at hl; exact hl ▸ hu) rfl rfl rfl
    ((recTyG_eq_unitDeclLE_recType u).symm) hu trivial h0
    (fun _ ↦ hasTypeL_Unit1) (fun _ ↦ hasTypeL_mk)
    ((isPropL_recB1_iff L κ ls hu hle [] trivial).mpr h0)
    ((isPropL_recB2_iff L κ ls hu hle [] trivial).mpr h0)
    ((isPropL_recB3_iff L κ ls hu hle [] trivial).mpr h0)

include L hu hle in
/-- The same with both sides evaluated: `{•} = {•}`.  Recorded because the conclusion above is
stated in the oracle's *unevaluated* form, and a reader should be able to see that the theorem
says something true rather than something vacuous. -/
theorem unitL_denot_eq_singleton_pt_of_inductOracleOK
    (hκ : ∀ m : ℕ, IsInaccessibleChain m κ) (h0 : u.eval ls = 0) :
    unitOracleL κ ls `Unit1 [] = ({pt} : V) := by
  rw [unitL_denot_eq_singleton_of_inductOracleOK L κ ls hu hle hκ h0, unitOracleL_mk]

include L hu hle in
/-- **The same from `OracleFits`** — the exact form the outer recursion `coherentOn_cnstOf`
quantifies over, at the assignment it builds.  This is the strongest instantiation available: the
model-side input is one `OracleFits` at one declaration list, and `hco` is discharged by §4b
rather than assumed. -/
theorem unitL_denot_eq_singleton_of_oracleFits
    (hκ : ∀ m : ℕ, IsInaccessibleChain m κ) (h0 : u.eval ls = 0) :
    cnstOf L κ ls (unitOracleL κ ls) [VDecl.induct unitDeclLE] `Unit1 []
      = ({cnstOf L κ ls (unitOracleL κ ls) [VDecl.induct unitDeclLE] `Unit1.mk []} : V) := by
  have hc : (⟨κ, ls, cnstOf L κ ls (unitOracleL κ ls) [VDecl.induct unitDeclLE]⟩ : ModelData V)
      = unitML κ ls := by
    rw [show unitML κ ls = (⟨κ, ls, unitOracleL κ ls⟩ : ModelData V) from rfl, cnstOfL]
  refine cnst_eq_singleton_of_oracleFits hκ hle (oracleFitsL L κ ls hle)
    (tc := `Unit1) (cc := `Unit1.mk) (rc := recN)
    (cci := ⟨0, .const `Unit1 []⟩) (rci := ⟨1, unitDeclLE.recType 0⟩)
    (tus := []) (cus := []) (rus := [u]) (w := u) (v0 := .zero)
    (by rw [unitDeclLE_allConsts]; simp) (by rw [unitDeclLE_allConsts]; simp)
    nofun rfl (fun l hl ↦ by simp only [List.mem_singleton] at hl; exact hl ▸ hu) rfl
    rfl ((recTyG_eq_unitDeclLE_recType u).symm) hu trivial h0
    (fun _ ↦ hasTypeL_Unit1) (fun _ ↦ hasTypeL_mk) ?_ ?_ ?_
  · rw [hc]; exact (isPropL_recB1_iff L κ ls hu hle [] trivial).mpr h0
  · rw [hc]; exact (isPropL_recB2_iff L κ ls hu hle [] trivial).mpr h0
  · rw [hc]; exact (isPropL_recB3_iff L κ ls hu hle [] trivial).mpr h0

end

section Omega
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]
variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (ls : List ℕ)
variable {u : VLevel} (hu : u.WF nv) (hle : unitEnvLE ≤ envF)

include L hu hle in
/-- **The chain side condition is satisfiable, so nothing above is vacuous.**  §2's `↔`, §4 and
§4b all carry `hκ : ∀ m, IsInaccessibleChain m κ`, which is what collapses `Above`.  Firing at
`InaccChainOmega.omegaChain V` discharges it outright, so the whole chain — oracle cell to
structure eta at the recursion's own assignment — holds with no unsatisfiable hypothesis left in
it.  (`not_isInaccessibleChain_const` records that `hκ` is real information and not free.) -/
theorem unitL_denot_eq_singleton_omegaChain (h0 : u.eval ls = 0) :
    cnstOf L (omegaChain V) ls (unitOracleL (omegaChain V) ls)
        [VDecl.induct unitDeclLE] `Unit1 []
      = ({cnstOf L (omegaChain V) ls (unitOracleL (omegaChain V) ls)
        [VDecl.induct unitDeclLE] `Unit1.mk []} : V) :=
  unitL_denot_eq_singleton_of_oracleFits L (omegaChain V) ls hu hle
    omegaChain_isInaccessibleChain h0

end Omega

end UnitAudit

/-! ## 6. Why `ntreeAux` is not reachable, checked -/

namespace InductiveDeclExamples

open Lean4Lean.InductiveDeclExamples

/-- **The three-binder availability condition fails at `ntreeAux`, on all three counts.**
`VInductDecl'.recPiTele_length_eq_three` is what makes the eta shape apply, and it wants
`D.np = 0`, `D.nm = 1`, `D.nmin = 1`.  The parameterised nested block has `np = 1`, `nm = 2`,
`nmin = 3` — hence the 7-entry telescope `ntreeAux_recPiTele_length` records.  So §4 does not
reach it, and the obstruction is the *consumer's* arity, not the oracle obligation. -/
theorem ntreeAux_not_three_binder :
    ntreeAux.np ≠ 0 ∧ ntreeAux.nm ≠ 1 ∧ ntreeAux.nmin ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end InductiveDeclExamples

end Lean4Lean.SetModel

/-! ## Status -/

#print axioms Lean4Lean.SetModel.OracleTypeCell
#print axioms Lean4Lean.SetModel.OracleOK.cell
#print axioms Lean4Lean.SetModel.oracleOK_iff_congr_and_cells
#print axioms Lean4Lean.SetModel.mem_cnst_iff_oracleTypeCell
#print axioms Lean4Lean.SetModel.mem_cnst_of_oracleTypeCell
#print axioms Lean4Lean.SetModel.cnst_eq_singleton_of_nonempty_interp_recTyG
#print axioms Lean4Lean.SetModel.exists_mem_interp_of_oracleTypeCell
#print axioms Lean4Lean.SetModel.mem_interpCtx_nil
#print axioms Lean4Lean.SetModel.cnst_eq_singleton_of_inductOracleOK
#print axioms Lean4Lean.SetModel.cnstOf_induct_eq_oracle
#print axioms Lean4Lean.SetModel.mem_allNames_of_mem_allConsts
#print axioms Lean4Lean.SetModel.cnst_eq_singleton_of_oracleFits
#print axioms Lean4Lean.SetModel.UnitAudit.unitL_denot_eq_singleton_of_inductOracleOK
#print axioms Lean4Lean.SetModel.UnitAudit.unitL_denot_eq_singleton_pt_of_inductOracleOK
#print axioms Lean4Lean.SetModel.UnitAudit.unitL_denot_eq_singleton_of_oracleFits
#print axioms Lean4Lean.SetModel.UnitAudit.unitL_denot_eq_singleton_omegaChain
#print axioms Lean4Lean.SetModel.InductiveDeclExamples.ntreeAux_not_three_binder
