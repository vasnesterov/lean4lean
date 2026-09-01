import Lean4Lean.Theory.SetModel.InductOracleAudit

/-!
# The `.induct` residual, satisfied at a **well-formed, reachable** block

`InductOracleAudit.lean` §5 records the residual's two-way bound field by field and marks
one cell open:

| field | not trivially true | satisfiable |
|---|---|---|
| `consts` | `not_inductOracleOK_falseProp` | **open at a `WF` block** |
| `rules` | open | free at a block with no constructors |

and adds that *both* of the entries it does have are at blocks that are **not**
`VInductDecl'.WF`, so the pair is a check on the statement rather than a measurement at a
block the soundness induction visits.  That is row 11a's weakness, recorded but not
repaired.

**This file repairs the `consts` cell, and the `rules` cell with it**, at `boxDecl` — the
`VInductDecl'.WF` block on the certified two-declaration history `boxDecl_history`.  In
fact it does more: `oracleFits_zero` gives `OracleFits` for the *whole* list
`[.induct boxDecl, .axiom extAx]`, so `coherentOn_boxDecl_history_of`'s two inhabitation
hypotheses are both discharged and `coherentOn_zero` produces `CoherentOn` at the block's
environment from the proof-split inputs alone.

## How, and what it does and does not show

The oracle is `zeroOracle = fun _ _ ↦ ∅`, which assigns `∅` to every name — in particular
to `Ext`, making the axiom `Ext : Prop` **false in the model**.  That is a legitimate
choice: `VDecl.WF`'s `.axiom` rule asks only that the type be a type, and `∅ ∈ UProp`.
Every constant `boxDecl` declares — the type former `Box : ∀ e : Ext, Prop`, the
constructor `Box.mk : ∀ e : Ext, Box e`, and the recursor, whose `recType` begins with the
same parameter binder — is then a `∀` over an **empty** domain, and its ι-rule's two sides
are `λ`s over the same empty domain.

So the honest statement of what is measured:

* **`Above`-free, which for this residual is the load-bearing check.**  `Above M P` is
  `∃ m, IsInaccessibleChain m M.κ → P`, so it is **trivially true at any `κ` that is not a
  chain of every finite length** — and every field of `OracleOK`/`DefEqOK` is an `Above`.
  A positive bound that went through the wrapper would therefore say nothing.  Every proof
  here goes through `Above.pure`; §5's `mem_interp_consts_zero` and `defEq_rules_zero`
  restate the obligations with the wrapper removed, at an arbitrary `κ`, as the check.
* **Real.** The block is `VInductDecl'.WF` over `extEnv` (`boxDecl_WF`), the list is
  `VEnv.WF'` (`boxDecl_history`) and `noUnsafe` (`boxDecl_noUnsafe`), and *every* field of
  `InductOracleOK` is discharged — three `OracleOK`s and one `DefEqOK`, none of them
  vacuous as a *statement*: `not_inductOracleOK_falseProp` shows the same fields are
  refutable elsewhere.  Nothing here is at a non-`WF` block, which is what §5 lacked.
* **Weak, and deliberately flagged.** The obligations are met *because* the parameter
  domain is empty.  So this does not exercise the content the residual is a residual for:
  inhabiting a recursor type over a **nonempty** parameter domain.  `docs/vacuity-ledger.md`
  row 24's lesson applies to the bound itself, so it is stated with its own limitation
  attached — `not_forall_params_nonempty_zero` records exactly which hypothesis a stronger
  bound would have to keep, and `exists_uninhabited_param_of_zero` says the mechanism is
  emptiness and nothing else.

What remains open after this file is therefore sharper than "`consts` at a `WF` block":
it is `consts` at a `WF` block **all of whose parameter and index domains are inhabited**.
`inductive Unit1 : Prop | mk` is the smallest such block, and its recursor needs a genuine
`mkLam`, i.e. `SetModel/IndInterp.lean`'s work.

## The three model lemmas

They are stated with **no typing hypotheses at all**, which is what makes them cheap: the
`forallE` and `lam` clauses of `interp` branch on `L.IsProp` / `L.IsProof`, which are
decidable syntactic predicates, so both branches can be taken directly.

* `mkLam_eq_empty_of_empty` — a `λ` over an empty domain is the empty function, `∅ = pt`.
* `interp_lam_of_empty_dom` — hence `⟦λ x : A, b⟧ = pt` whenever `⟦A⟧ = ∅`, in *both*
  branches (the proof branch gives `pt` outright, the other gives `∅`).
* `pt_mem_interp_forallE_of_empty_dom` — and `pt ∈ ⟦∀ x : A, B⟧` whenever `⟦A⟧ = ∅`, again
  in both branches: `mkForallProp` because the intersection is vacuous, `mkForallType`
  because `∅` is the empty function and `∅ ∈ Y ^ ∅`.

The coincidence that makes this uniform is `pt = ∅` (`Universe.lean:53`): the propositional
witness and the empty function are the same element, so no case split leaks into the
oracle's definition.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-! ## 1. Empty-domain `λ` and `∀`, with no typing hypotheses -/

section EmptyDom

variable {envF : VEnv} {nv : ℕ} {M : ModelData V} {L : PropSplit envF nv}

/-- A `mkLam` over an empty domain is the empty function. -/
theorem mkLam_eq_empty_of_empty {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {ρ : V} (hG0 : G ρ = ∅) :
    mkLam G hG F hF ρ = ∅ := by
  rw [mem_ext_iff]
  intro y
  simp only [not_mem_empty, iff_false]
  intro hy
  obtain ⟨v, hv, -⟩ := mem_mkLam_iff.mp hy
  rw [hG0] at hv
  exact not_mem_empty hv

/-- **A `λ` over an empty domain denotes `pt`** — in both branches of the `lam` clause, and
with no hypothesis on `b`.  The proof branch gives `pt` by definition; the other gives the
empty function, and `pt = ∅`. -/
theorem interp_lam_of_empty_dom {Γ : List VExpr} {A b : VExpr} {ρ : V}
    (hA : (interp M L Γ A).toFun ρ = ∅) :
    (interp M L Γ (.lam A b)).toFun ρ = pt := by
  by_cases h : L.IsProof M (A :: Γ) b
  · exact interp_lam_proof M L h ρ
  · rw [interp_lam_type M L h, mkLam_eq_empty_of_empty hA]; rfl

/-- **A `∀` over an empty domain is inhabited by `pt`** — again in both branches, and with
no hypothesis on `B`.  `mkForallProp` because `⋂_{v ∈ ∅} = {•}`; `mkForallType` because the
empty function belongs to `Y ^ ∅`. -/
theorem pt_mem_interp_forallE_of_empty_dom {Γ : List VExpr} {A B : VExpr} {ρ : V}
    (hA : (interp M L Γ A).toFun ρ = ∅) :
    (pt : V) ∈ (interp M L Γ (.forallE A B)).toFun ρ := by
  by_cases h : L.IsProp M (A :: Γ) B
  · refine (mem_interp_forallE_prop_iff M L h).2 ⟨rfl, fun v hv ↦ ?_⟩
    rw [hA] at hv; exact absurd hv (by simp)
  · rw [interp_forallE_type M L h]
    have := mkLam_mem_mkForallType (V := V)
      (G := (interp M L Γ A).toFun) (hG := (interp M L Γ A).definable)
      (F := fun _ _ ↦ (∅ : V)) (hF := by definability)
      (Fb := fun ρ v ↦ (interp M L (A :: Γ) B).toFun (snoc ρ v))
      (hFb := by have := (interp M L (A :: Γ) B).definable; definability)
      (ρ := ρ) (fun v hv ↦ by rw [hA] at hv; exact absurd hv (by simp))
    rwa [mkLam_eq_empty_of_empty hA] at this

end EmptyDom

/-! ## 2. The zero oracle -/

/-- **The oracle that assigns `∅` to everything.**  `∅ = pt`, so this is simultaneously the
propositional witness and the empty function; §1 is what makes that enough. -/
noncomputable def zeroOracle (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Name → List VLevel → V := fun _ _ ↦ ∅

@[simp] theorem zeroOracle_apply (n : Name) (us : List VLevel) :
    zeroOracle V n us = (∅ : V) := rfl

omit [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
theorem cnstUpdate_zero (n : Name) :
    cnstUpdate (zeroOracle V) n (zeroOracle V n) = zeroOracle V := by
  funext m us
  by_cases h : m = n <;> simp [cnstUpdate, h, zeroOracle]

omit [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] in
theorem oracleExtend_zero : ∀ ns : List Name,
    oracleExtend (zeroOracle V) ns (zeroOracle V) = zeroOracle V
  | [] => rfl
  | _ :: ns => by rw [oracleExtend, cnstUpdate_zero]; exact oracleExtend_zero ns

section Assignment

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

open SetModelAudit

/-- The assignment the recursion builds from the zero oracle along `boxDecl`'s history is
the zero assignment itself.  Both steps are name updates — `.axiom` and `.induct` are the
two `cnstOf` clauses that consult the oracle rather than compute — so nothing else can
enter. -/
theorem cnstOf_zero_boxDecl :
    cnstOf L κ ls (zeroOracle V) [.induct boxDecl, .axiom extAx] = zeroOracle V := by
  show oracleExtend (zeroOracle V) boxDecl.allNames
      (cnstUpdate (cnstOf L κ ls (zeroOracle V) []) extAx.name (zeroOracle V extAx.name))
    = zeroOracle V
  rw [show cnstOf L κ ls (zeroOracle V) [] = zeroOracle V from rfl, cnstUpdate_zero,
    oracleExtend_zero]

theorem cnstOf_zero_extAx :
    cnstOf L κ ls (zeroOracle V) [.axiom extAx] = zeroOracle V := by
  show cnstUpdate (cnstOf L κ ls (zeroOracle V) []) extAx.name (zeroOracle V extAx.name)
    = zeroOracle V
  rw [show cnstOf L κ ls (zeroOracle V) [] = zeroOracle V from rfl, cnstUpdate_zero]

/-- `Ext` denotes `∅` under the zero assignment: the axiom is **false** in the model. -/
theorem interp_ext_zero (Γ : List VExpr) (ρ : V) :
    (interp ⟨κ, ls, zeroOracle V⟩ L Γ (.const `Ext [])).toFun ρ = ∅ := by
  rw [interp_const]; rfl

end Assignment

/-! ## 3. Every obligation at `boxDecl`'s history -/

section Obligations

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

open SetModelAudit

/-- **The generic step**: a constant whose type is, at every level instantiation, a `∀`
whose domain is `Ext` is inhabited by the zero oracle's value. -/
theorem oracleOK_zero_of_ext {n : Name} {ci : VConstant}
    (h : ∀ us : List VLevel, ∃ B, ci.type.instL us = .forallE (.const `Ext []) B) :
    OracleOK L κ ls (zeroOracle V) (zeroOracle V) n ci := by
  refine oracleOK_of (fun _ _ _ ↦ rfl) (fun {us} _ _ ↦ ?_)
  obtain ⟨B, hB⟩ := h us
  rw [zeroOracle_apply, hB]
  exact pt_mem_interp_forallE_of_empty_dom (interp_ext_zero L κ ls _ _)

/-- `axiom Ext : Prop` itself: `∅ ∈ UProp`, so the false proposition is a legal value. -/
theorem oracleOK_zero_extAx :
    OracleOK L κ ls (zeroOracle V) (zeroOracle V) extAx.name extAx.toVConstant := by
  refine oracleOK_of (fun _ _ _ ↦ rfl) (fun {us} _ hlen ↦ ?_)
  have : us = [] := List.eq_nil_of_length_eq_zero hlen
  subst this
  rw [zeroOracle_apply, show (extAx.toVConstant.type.instL []) = .sort .zero from rfl,
    interp_sort]
  exact empty_mem_UProp

/-- **The `consts` field, at a `WF` block, all three constants.**  Each of the type
former's, the constructor's and the recursor's stored type begins with the block's one
parameter binder `(e : Ext)`. -/
theorem inductOracleOK_consts_zero :
    ∀ p ∈ boxDecl.allConsts, OracleOK L κ ls (zeroOracle V) (zeroOracle V) p.1 p.2 := by
  intro p hp
  rw [boxDecl_allConsts] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp <;>
    exact oracleOK_zero_of_ext L κ ls (fun _ ↦ ⟨_, rfl⟩)

/-- **The `rules` field.**  `boxDecl` has one ι-rule; both of its sides are `λ`s over `Ext`
and its type is a `∀` over `Ext`, so the two sides denote `pt` and `pt` lies in the type. -/
theorem inductOracleOK_rules_zero :
    ∀ df ∈ boxDecl.iotaRules, DefEqOK L (⟨κ, ls, zeroOracle V⟩ : ModelData V) df := by
  intro df hdf
  rw [show boxDecl.iotaRules =
      [boxDecl.iotaRule 0 0
        { name := `Box.mk, params := [.const `Ext []], fields := [], args := [] }] from rfl]
    at hdf
  simp only [List.mem_singleton] at hdf
  subst hdf
  refine fun {us} _ _ ↦ ⟨Above.pure ?_, Above.pure ?_⟩
  · obtain ⟨bl, hl⟩ : ∃ b, (boxDecl.iotaRule 0 0
        { name := `Box.mk, params := [.const `Ext []], fields := [], args := [] }).lhs.instL us
      = .lam (.const `Ext []) b := ⟨_, rfl⟩
    obtain ⟨br, hr⟩ : ∃ b, (boxDecl.iotaRule 0 0
        { name := `Box.mk, params := [.const `Ext []], fields := [], args := [] }).rhs.instL us
      = .lam (.const `Ext []) b := ⟨_, rfl⟩
    rw [hl, hr, interp_lam_of_empty_dom (interp_ext_zero L κ ls _ _),
      interp_lam_of_empty_dom (interp_ext_zero L κ ls _ _)]
  · obtain ⟨bl, hl⟩ : ∃ b, (boxDecl.iotaRule 0 0
        { name := `Box.mk, params := [.const `Ext []], fields := [], args := [] }).lhs.instL us
      = .lam (.const `Ext []) b := ⟨_, rfl⟩
    obtain ⟨bt, ht⟩ : ∃ b, (boxDecl.iotaRule 0 0
        { name := `Box.mk, params := [.const `Ext []], fields := [], args := [] }).type.instL us
      = .forallE (.const `Ext []) b := ⟨_, rfl⟩
    rw [hl, ht, interp_lam_of_empty_dom (interp_ext_zero L κ ls _ _)]
    exact pt_mem_interp_forallE_of_empty_dom (interp_ext_zero L κ ls _ _)

/-- **The residual, satisfied at a well-formed block on a certified history.**  This is the
`consts`/`rules` positive bound `InductOracleAudit.lean` §5 records as open, now at a block
that `VInductDecl'.WF` accepts and `VEnv.WF'` reaches. -/
theorem inductOracleOK_zero :
    InductOracleOK L κ ls (zeroOracle V) (zeroOracle V) boxDecl :=
  ⟨inductOracleOK_consts_zero L κ ls, inductOracleOK_rules_zero L κ ls⟩

/-- **`OracleFits` for the whole two-declaration list.**  Both of
`coherentOn_boxDecl_history_of`'s inhabitation hypotheses hold at the zero oracle. -/
theorem oracleFits_zero :
    OracleFits L κ ls (zeroOracle V) [.induct boxDecl, .axiom extAx] := by
  refine ⟨?_, ?_, trivial⟩
  · show InductOracleOK L κ ls (zeroOracle V)
      (cnstOf L κ ls (zeroOracle V) [.induct boxDecl, .axiom extAx]) boxDecl
    rw [cnstOf_zero_boxDecl]
    exact inductOracleOK_zero L κ ls
  · show OracleOK L κ ls (zeroOracle V) (cnstOf L κ ls (zeroOracle V) [.axiom extAx])
      extAx.name extAx.toVConstant
    rw [cnstOf_zero_extAx]
    exact oracleOK_zero_extAx L κ ls

end Obligations

/-! ## 4. Coherence at the block's environment, with no residual left -/

section Coherence

variable {envF : VEnv} {nv : ℕ} {κ : ℕ → V} {ls : List ℕ}

open SetModelAudit

/-- **`CoherentOn` at `boxDecl`'s environment from the proof-split inputs alone.**  Every
oracle obligation on the list — the `.induct` residual included — is discharged, so what is
left is exactly `L.Stable`, `CtxInvariant` and the `envF` bound, i.e. the *other* open
model-side item (`docs/model-interface.md`'s `PropSplit env 0` with `Stable`).

This is the sharpest form of the measurement: at this list the `.induct` residual costs
nothing, and the only thing still standing between the recursion and `CoherentOn` is the
proof split. -/
theorem coherentOn_zero (L : PropSplit envF nv)
    {R : List VExpr → List VExpr → Prop} (hS : L.Stable) (hR : CtxInvariant L R)
    (hRdF : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
      envF.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))
    {env : VEnv} (hwf : VEnv.WF' [.induct boxDecl, .axiom extAx] env) (hle : env ≤ envF) :
    CoherentOn
      (⟨κ, ls, cnstOf L κ ls (zeroOracle V) [.induct boxDecl, .axiom extAx]⟩ : ModelData V)
      L env :=
  coherentOn_cnstOf L (zeroOracle V) hS hR hRdF _ hwf hle boxDecl_noUnsafe
    (oracleFits_zero L κ ls)

end Coherence

/-! ## 5. The bound's own limitation, recorded

Row 24's lesson turned on a hypothesis being satisfiable only because a class was empty.
That *is* the mechanism here, so it is stated rather than left for a reader to discover. -/

section Limitation

variable {envF : VEnv} {nv : ℕ} (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)

open SetModelAudit

/-- **The mechanism is emptiness.**  The block's one parameter denotes `∅` under the zero
assignment, so every obligation above was met over an empty domain.  A bound that exercised
the residual's real content would have to keep this set nonempty. -/
theorem boxDecl_params : boxDecl.params = [.const `Ext []] := rfl

theorem interp_param_zero_eq_empty :
    (interp (⟨κ, ls, zeroOracle V⟩ : ModelData V) L [] (.const `Ext [])).toFun ∅ = ∅ :=
  interp_ext_zero L κ ls _ _

/-- …and the value the oracle hands each constant is `pt` in every case, never anything
built from the block's fixed point.  So `IndInterp.lean`'s construction is untouched by
this file: the measurement says the residual's *statement* is satisfiable at a `WF` block,
not that the intended oracle satisfies it. -/
theorem zeroOracle_boxDecl_values :
    ∀ p ∈ boxDecl.allConsts, ∀ us, zeroOracle V p.1 us = (pt : V) :=
  fun _ _ _ ↦ rfl

/-! ### `Above`'s escape hatch is **not** used

`Above M P` is `∃ m, IsInaccessibleChain m M.κ → P` (`InterpSound.lean:696`), so it is
**trivially true whenever `M.κ` is not an inaccessible chain of every finite length** — take
`m = 2` and any constant `κ`, refuted by `InaccChainOmega.not_isInaccessibleChain_const`.
Every field of `OracleOK` and `DefEqOK` is an `Above`, so *any* positive bound on the
residual stated only through them is worthless unless it goes through `Above.pure`.

The two theorems below are the check that this file's does.  They are the same obligations
with the wrapper **removed**, at an arbitrary `κ` — no chain hypothesis anywhere — so
`inductOracleOK_zero` survives the unwrapping at the `κ` of
`exists_inaccessibleChain_omega`, which is the only `κ` the reduction ever uses. -/

/-- **The `consts` obligation, `Above`-free.** -/
theorem mem_interp_consts_zero :
    ∀ p ∈ boxDecl.allConsts, ∀ us : List VLevel,
      zeroOracle V p.1 us
        ∈ (interp (⟨κ, ls, zeroOracle V⟩ : ModelData V) L [] (p.2.type.instL us)).toFun ∅ := by
  intro p hp us
  rw [boxDecl_allConsts] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp <;>
    exact pt_mem_interp_forallE_of_empty_dom (interp_ext_zero L κ ls _ _)

/-- **The `rules` obligation, `Above`-free**: the two sides are *equal*, and the common value
lies in the equated type, with no threshold. -/
theorem defEq_rules_zero :
    ∀ df ∈ boxDecl.iotaRules, ∀ us : List VLevel,
      (interp (⟨κ, ls, zeroOracle V⟩ : ModelData V) L [] (df.lhs.instL us)).toFun ∅
          = (interp (⟨κ, ls, zeroOracle V⟩ : ModelData V) L [] (df.rhs.instL us)).toFun ∅ ∧
        (interp (⟨κ, ls, zeroOracle V⟩ : ModelData V) L [] (df.lhs.instL us)).toFun ∅
          ∈ (interp (⟨κ, ls, zeroOracle V⟩ : ModelData V) L [] (df.type.instL us)).toFun ∅ := by
  intro df hdf us
  rw [show boxDecl.iotaRules =
      [boxDecl.iotaRule 0 0
        { name := `Box.mk, params := [.const `Ext []], fields := [], args := [] }] from rfl]
    at hdf
  simp only [List.mem_singleton] at hdf
  subst hdf
  obtain ⟨bl, hl⟩ : ∃ b, (boxDecl.iotaRule 0 0
      { name := `Box.mk, params := [.const `Ext []], fields := [], args := [] }).lhs.instL us
    = .lam (.const `Ext []) b := ⟨_, rfl⟩
  obtain ⟨br, hr⟩ : ∃ b, (boxDecl.iotaRule 0 0
      { name := `Box.mk, params := [.const `Ext []], fields := [], args := [] }).rhs.instL us
    = .lam (.const `Ext []) b := ⟨_, rfl⟩
  obtain ⟨bt, ht⟩ : ∃ b, (boxDecl.iotaRule 0 0
      { name := `Box.mk, params := [.const `Ext []], fields := [], args := [] }).type.instL us
    = .forallE (.const `Ext []) b := ⟨_, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hl, hr, interp_lam_of_empty_dom (interp_ext_zero L κ ls _ _),
      interp_lam_of_empty_dom (interp_ext_zero L κ ls _ _)]
  · rw [hl, ht, interp_lam_of_empty_dom (interp_ext_zero L κ ls _ _)]
    exact pt_mem_interp_forallE_of_empty_dom (interp_ext_zero L κ ls _ _)

end Limitation

end Lean4Lean.SetModel
