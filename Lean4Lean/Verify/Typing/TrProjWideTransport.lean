import Lean4Lean.Verify.Typing.TrProjWide

/-!
# The eleventh field through `instN`, `instL`, `defeqDFC`

`TrProjWide.lean` measured `mono` (free) and `weak'`/`weakN` (available at `VEnv.Ordered` +
`Ctx.Lift'`, **not** `VEnv.WF`).  This file finishes the structural cluster of ledger row 107d
option (d): the three remaining transport lemmas `TrProj.instN` / `.instL` / `.defeqDFC`
(`Verify/Typing/Lemmas.lean:2141`, `:2421`, `:931`) restated for `TrProjG`, with the eleventh
field carried.
-/

namespace Lean4Lean

open VExpr

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr}

/-! ## `instN` -/

/-- **`instN` transports the eleventh field**, at exactly `TrProj.instN`'s own hypotheses:
`VEnv.Ordered env`, a `Ctx.InstN`, and the substituted term's typing.  **No `VEnv.WF`, no
`OnCtx`** — same measurement as `weak'`. -/
theorem TrProjG.instN {Γ₀ Γ₁ : List VExpr} {k : Nat} {e₀ A₀ : VExpr} (henv : VEnv.Ordered env)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (t₀ : env.HasType U Γ₀ e₀ A₀)
    (H : TrProjG env U Γ₁ s i e e') :
    TrProjG env U Γ s i (e.inst e₀ k) (e'.inst e₀ k) := by
  obtain @⟨_, D, T, C, us, ps, ιs, _, _, _, j, h1, hrec, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11⟩ := H
  have hcl := h1.projClosedG henv
  have hclN := hcl.toProjClosed h1.types (by rw [h1.ctors]; exact List.mem_singleton_self _)
  rw [D.projTermG_instN T C us hcl h1.types h1.ctors h4 h5 h6]
  refine .mk h1 hrec ?_ h3 (by simp [h4]) (by simp [h5]) h6 h7 ?_ ?_ h10 ?_
  · simpa [VExpr.inst_mkApp, List.map_append, VExpr.inst] using h2.instN henv W t₀
  · have := h8.instN henv W t₀
    rwa [VExpr.instTele_eq_self (VExpr.ClosedTele.map_instL hclN.params) (Nat.zero_le _)] at this
  · have := h9.instN henv W t₀
    rwa [VExpr.inst_instAllTele₀
      (by simpa [h4] using VExpr.ClosedTele.map_instL hclN.indices)] at this
  · have hty := h11.instN henv W t₀
    rw [D.projTermG_instN T C us hcl h1.types h1.ctors h4 h5 h6] at hty
    have hget : (C.fields.map (·.type))[i]? = some (C.fields.getD i default).type := by
      rw [List.getElem?_map, List.getElem?_eq_getElem h6]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h6]
    have hfcl : ((C.fields.getD i default).type.instL us).ClosedN
        (0 + (ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e).length) := by
      have := (VExpr.ClosedTele.getElem? hclN.fields hget).instL (ls := us)
      simpa [h4] using this
    have heq : (VExpr.instAll ((C.fields.getD i default).type.instL us)
          (ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e) 0).inst e₀ k
        = VExpr.instAll ((C.fields.getD i default).type.instL us)
          ((ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e).map
            (·.inst e₀ k)) 0 :=
      VExpr.inst_instAll (j := 0) (m := k) hfcl
    have hmap : (ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e).map
          (·.inst e₀ k)
        = ps.map (·.inst e₀ k) ++ (List.range i).map
            fun m => D.projTermG T C us (ps.map (·.inst e₀ k)) (ιs.map (·.inst e₀ k)) m j
              (e.inst e₀ k) := by
      rw [List.map_append, List.map_map]
      congr 1
      refine List.map_congr_left fun m hm => ?_
      exact D.projTermG_instN T C us hcl h1.types h1.ctors h4 h5
        (Nat.lt_trans (List.mem_range.1 hm) h6)
    rw [heq, hmap] at hty
    exact hty

/-! ## `instL` -/

/-- **`instL` transports the eleventh field**, and it takes exactly what `TrProj.instL`
(`Verify/Typing/Lemmas.lean:2421`) takes: `∀ l ∈ ls, l.WF U'` and **nothing else** — no
`VEnv.Ordered`, no `VEnv.WF`, no `OnCtx`.  `projTermG_instL` is unconditional, and
`VExpr.instL_instAll` needs no closedness, so this one is *cheaper* than `weak'`/`instN`. -/
theorem TrProjG.instL {U' : Nat} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U')
    (H : TrProjG env U Γ s i e e') :
    TrProjG env U' (Γ.map (VExpr.instL ls)) s i (e.instL ls) (e'.instL ls) := by
  obtain @⟨_, D, T, C, us, ps, ιs, _, _, _, j, h1, hrec, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11⟩ := H
  rw [D.projTermG_instL T C us ls]
  refine .mk h1 hrec ?_ (by simp [h3]) (by simp [h4]) (by simp [h5]) h6 ?_ ?_ ?_ ?_ ?_
  · simpa [VExpr.instL, List.map_append] using h2.instL hls
  · exact fun l hl => by
      obtain ⟨l', _, rfl⟩ := List.mem_map.1 hl; exact VLevel.WF.inst hls
  · simpa [List.map_map, Function.comp_def, VExpr.instL_instL] using h8.instL hls
  · simpa [List.map_map, Function.comp_def, VExpr.instL_instL] using h9.instL hls
  · refine h10.imp id fun h k hk hg => ?_
    rw [← VLevel.inst_inst]
    exact VLevel.inst_congr_l (h k hk hg)
  · have hty := h11.instL hls
    rw [D.projTermG_instL T C us ls] at hty
    simpa [VExpr.instL_instAll, VExpr.instL_instL, List.map_append, List.map_map,
      Function.comp_def, D.projTermG_instL T C us ls] using hty

/-! ## `defeqDFC` — transports, but NOT for free: it re-derives the eleventh field

This is the one place in the structural cluster where option (d) costs something, and the
measurement is worth stating precisely.

`weak'`, `instN` and `instL` all move the *same* target term: the eleventh field's statement is
carried across a syntactic operation applied uniformly to subject, spine and type, so the
transported `HasType` **is** the one wanted, and no typing has to be re-derived (hence they are
hole-free at `Ordered`/nothing).

`defeqDFC` is different: its conclusion changes the **major premise**, from `e₁` to `e₂`.  The
eleventh field's *type* mentions the earlier projections of the major premise
(`(List.range i).map fun m => D.projTermG T C us ps ιs m j e`), so `HasType.defeqDFC` delivers
the field at `e₁` and the target the constructor demands is at `e₂`.  There are exactly two
routes:

1. **re-derive** the field at `e₂` from `mk'` — done below.  It needs `VEnv.WF env` and
   `OnCtx Γ₂ (env.IsType U)`, *both of which `TrProj.defeqDFC` already has* (the first
   verbatim, the second as `hΓ.symm.isType`, which is a line of the narrow proof already).  So
   **the signature is unchanged from the narrow lemma** — nothing is strengthened — but the
   proof now runs through wall 2, and therefore inherits `VEnv.IsDefEqU.weakN_iff` and
   `VEnv.IsDefEqU.forallE_inv_stratified`.
2. congruence of `projTermG` in its major premise, plus congruence of its **type**.  **I twice
   wrote that this route was blocked by an absent lemma, and was wrong both times** — recorded
   here because an unproved negative is the ledger's kind-4 overstatement, and I produced two in
   one afternoon.  Both halves exist:
   * `VInductDecl'.projTerm_congr_subject` (`Verify/Typing/ProjSpineInv.lean:184`) is
     `e₁ ≡ e₂ → projTerm … e₁ ≡ projTerm … e₂` at fixed data (narrow; the `projTermG` analogue
     looks routine).  Cone 3497, holes `{forallE_inv_stratified}` — **measured**.
   * `VEnv.IsDefEqU.instAllCongr` (`Verify/Typing/ProjSpineCongr.lean:26`) is the general
     `instAll b as ≡ instAll b as'` from `HasArgsDF`.  Cone 3519, holes
     `{forallE_inv_stratified}` — **measured**.  (Found by a structural query over the compiled
     environment — every declaration whose conclusion head is `IsDefEq`/`IsDefEqU` and whose
     conclusion mentions `VExpr.instAll` — after two greps had missed it.)

   So route 2 is **live and unpriced**, and it is interesting precisely because *neither*
   ingredient carries `weakN_iff`: it could plausibly give `defeqDFC` back its narrow hole set.
   What it cannot do is save a hypothesis — both ingredients take `VEnv.WF env` — and what is
   unmeasured is its real cost: `instAllCongr` wants `OnCtx (As.reverse ++ Γ)` and
   `HasType (As.reverse ++ Γ) b B` for the **field telescope** `As`, plus a `HasArgsDF` between
   the two projection spines; assembling those without re-entering `projTermG_hasType` is an
   unbuilt module, not a rewrite of this proof.

So the honest headline is: **`instN`/`instL` are free, `defeqDFC` is not.**  It transports at the
narrow signature and its cone grows to wall 2's. -/
theorem TrProjG.defeqDFC {Γ₁ Γ₂ : List VExpr} {e₁ e₂ : VExpr} (henv : VEnv.WF env)
    (hΓ : env.IsDefEqCtx U [] Γ₁ Γ₂) (he : env.IsDefEqU U Γ₁ e₁ e₂)
    (H : TrProjG env U Γ₁ s i e₁ e') : ∃ e'', TrProjG env U Γ₂ s i e₂ e'' := by
  have hΓ₂ : OnCtx Γ₂ (env.IsType U) := (hΓ.symm henv.ordered).isType
  obtain @⟨_, D, T, C, us, ps, ιs, _, _, _, j, h1, hrec, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, _⟩ := H
  refine ⟨_, .mk' henv hΓ₂ h1 hrec ?_ h3 h4 h5 h6 h7 (h8.defeqDFC henv.ordered hΓ)
    (h9.defeqDFC henv.ordered hΓ) h10⟩
  exact ((he.defeqDFC henv.ordered hΓ).of_l henv hΓ₂ (h2.defeqDFC henv.ordered hΓ)).hasType.2

/-! ## Localising the cost: the ten-field part of `defeqDFC`, and what the eleventh adds

**Correction to my own first draft, which said this version is hole-free.  It is not.**
Measured: `TrProjG.defeqDFC_ten` has cone **3490** and holes `{forallE_inv_stratified}` —
the same hole set and (to 7 nodes) the same cone as the *narrow* `TrProj.defeqDFC`
(**3497**, `{forallE_inv_stratified}`).  That hole comes from `IsDefEqU.of_l`, i.e. from moving
the **subject** from `e₁` to `e₂`; it is `defeqDFC`'s own pre-existing cost and has nothing to do
with option (d).

The eleventh field's **marginal** cost is therefore exactly the difference between this lemma and
`TrProjG.defeqDFC`: cone 3490 -> **5289**, holes `{forallE_inv_stratified}` →
`{weakN_iff, forallE_inv_stratified}`.  So option (d) makes `defeqDFC` gain **`weakN_iff`**, a
hole the narrow `defeqDFC` did not carry.  Nothing new *to the tree* (it is `TrProj.wf`'s and
wall 2's own hole, and `TrProj.wf` is in the same file), and nothing traded — but it is a real
widening of *this lemma's* cone, and it is the only such widening in the structural cluster:
`weak'`, `instN` and `instL` all stay hole-free.

Stated as a conjunction rather than as a `TrProjG` so that the eleventh field is genuinely
absent from the conclusion; an assembled `TrProjG` would have to contain it. -/
theorem TrProjG.defeqDFC_ten {Γ₁ Γ₂ : List VExpr} {e₁ e₂ : VExpr} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps ιs : List VExpr}
    {j : Nat} (henv : VEnv.WF env) (hΓ : env.IsDefEqCtx U [] Γ₁ Γ₂)
    (he : env.IsDefEqU U Γ₁ e₁ e₂)
    (hS : env.IsStructureG S D j T C) (hrec : C.recFields = [])
    (h2 : env.HasType U Γ₁ e₁ ((VExpr.const S us).mkApp (ps ++ ιs)))
    (h3 : us.length = D.uvars) (h4 : ps.length = D.np) (h5 : ιs.length = T.indices.length)
    (h6 : i < C.fields.length) (h7 : ∀ l ∈ us, l.WF U)
    (h8 : env.HasArgs U Γ₁ (D.params.map (VExpr.instL us)) ps)
    (h9 : env.HasArgs U Γ₁ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs)
    (h10 : D.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
      (C.fields.getD k default).lvl.inst us ≈ .zero) :
    env.IsStructureG S D j T C ∧ C.recFields = [] ∧
    env.HasType U Γ₂ e₂ ((VExpr.const S us).mkApp (ps ++ ιs)) ∧
    us.length = D.uvars ∧ ps.length = D.np ∧ ιs.length = T.indices.length ∧
    i < C.fields.length ∧ (∀ l ∈ us, l.WF U) ∧
    env.HasArgs U Γ₂ (D.params.map (VExpr.instL us)) ps ∧
    env.HasArgs U Γ₂ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs ∧
    (D.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
      (C.fields.getD k default).lvl.inst us ≈ .zero) := by
  have hΓ₂ : OnCtx Γ₂ (env.IsType U) := (hΓ.symm henv.ordered).isType
  exact ⟨hS, hrec,
    ((he.defeqDFC henv.ordered hΓ).of_l henv hΓ₂ (h2.defeqDFC henv.ordered hΓ)).hasType.2,
    h3, h4, h5, h6, h7, h8.defeqDFC henv.ordered hΓ, h9.defeqDFC henv.ordered hΓ, h10⟩

/-! ## `weak'_inv`: the widening is **not** better positioned, and the reason is measurable

`TrProj.weak'_inv` (`Verify/Typing/Lemmas.lean:902`) is one of the tree's 13 standing holes, so a
widened version was never expected to be hole-free.  The question the brief asks is the useful
one: is `TrProjG.weak'_inv` *better* positioned?  **It is not, and it is worse by exactly one
hole.**  Both halves of that verdict are stated as theorems below rather than as prose.

**Input side — no gain.**  The widened hypothesis is strictly stronger: it hands you the
target's typing in `Γ'` for free (`TrProjG.wf`, hole-free, 737 nodes), where a narrow proof
wanting the same thing must call `TrProj.wf` (cone 5095, holes
`{weakN_iff, forallE_inv_stratified}`).  But the *live* narrow route does not want it:
`TrProj.weak'_inv_of_typing_head` has cone **3716** and holes
`{forallE_inv_stratified, rigidShapeUniqNS}` — **no `weakN_iff`**, i.e. it never calls
`TrProj.wf`.  So the free eleventh field pays for nothing that route was buying.

**Output side — a strict loss.**  The widened conclusion is an eleventh field *in the smaller
context* `Γ`, and its only producer in the tree is `TrProjG.mk'`, i.e. wall 2.  That drags
`weakN_iff` back in — precisely the hole `weak'_inv_of_typing_head` was engineered to avoid —
and it needs `OnCtx Γ (env.IsType U)`, the **smaller** context's well-formedness, which the
headline `TrProj.weak'_inv` does not have (it takes `OnCtx Γ'`; recovering `OnCtx Γ` from it is
`OnCtx.weak'_inv`, and Update 7 of that docstring records that this single step is where
`weakN_iff` enters the strengthening route).

So option (d) reproduces at `weak'_inv` exactly the pattern it produces at `defeqDFC`: the
lemma's signature can be kept, and its hole set grows by `weakN_iff`.  Two of the six structural
lemmas pay it; four (`mono`, `weak'`, `weakN`, `instN`, `instL` — five, counting `weakN`
separately) do not. -/

/-- **The widened inversion, from the narrow one.**  This is the positive half of the verdict:
`TrProjG.weak'_inv` is *reachable* the moment `TrProj.weak'_inv` is, at the cost of `VEnv.WF env`
and `OnCtx Γ (env.IsType U)` — the smaller context.

Deliberately stated with the narrow inversion as an explicit hypothesis rather than by calling
`TrProj.weak'_inv`, so that the hole set measured on this theorem is the cost of the *widening*
alone and not of the standing hole. -/
theorem TrProjG.weak'_inv_of_narrow (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hnarrow : ∃ e'', TrProj env U Γ s i e e'') : ∃ e'', TrProjG env U Γ s i e e'' :=
  let ⟨_, h⟩ := hnarrow; ⟨_, h.toG henv hΓ⟩

/-- **The negative half, as a statement rather than as prose**: the widened inversion's extra
content is exactly an eleventh field in the smaller context, and *given* that field the widened
conclusion follows from `TrProj.mk`'s own ten (with `IsStructure` widened and `noRec` added)
with **no** `VEnv.WF` and **no** `OnCtx` at all.

Read against `weak'_inv_of_narrow`: the two together say the whole cost of widening
`TrProj.weak'_inv` is producing this one `HasType` in `Γ`, and that `VEnv.WF`/`OnCtx Γ` are
being spent solely on producing it (through `mk'`, hence through `weakN_iff`).  Anything that
produced the field another way would pay neither. -/
theorem TrProjG.weak'_inv_of_narrow_and_field {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps ιs : List VExpr}
    {j : Nat} (hS : env.IsStructureG S D j T C) (hrec : C.recFields = [])
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ ιs)))
    (h3 : us.length = D.uvars) (h4 : ps.length = D.np) (h5 : ιs.length = T.indices.length)
    (hi : i < C.fields.length) (h7 : ∀ l ∈ us, l.WF U)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hιsA : env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs)
    (hF : D.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
      (C.fields.getD k default).lvl.inst us ≈ .zero)
    (hfield : env.HasType U Γ (D.projTermG T C us ps ιs i j e)
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e))) :
    ∃ e'', TrProjG env U Γ S i e e'' :=
  ⟨_, .mk hS hrec he h3 h4 h5 hi h7 hpsA hιsA hF hfield⟩

end Lean4Lean
