import Lean4Lean.Theory.Typing.ConstSubstNested

/-!
# The nested route's three bridges, and the defect two of them just lost

`VEnv.addInductR_ordered'` (`Theory/Inductive/NestedOrdered.lean`) reduces "a nested
declaration step preserves `VEnv.Ordered`" to three obligations, and
`VEnv.ctorConstsCR_wf_of_substC` / `recConstsR_wf_of_substC` / `iotaRulesR_wf_of_substC`
(`Theory/Typing/ConstSubstNested.lean`) reduce each of those to one **syntactic bridge**.
Since 2026-08-31 the first two read

    (C.type D j).substC σ  = (C.typeR D R j).substC σ          -- (A) declared constructors
    (D.recType j).substC σ = (D.recTypeR R j).substC σ'        -- (B) renamed recursors

with `σ = VIndRestore.csubstTy D K`, `σ' = csubst D K`, because `VInductDecl'.ctorConstsCR`
and `recConstsR` now declare the *substituted* restored type; (C) is unchanged,

    D.iotaRules.map (·.substC σ') = D.iotaRulesR R             -- (C) ι-rules

because `VEnv.addIndRulesR` still folds `iotaRulesR` unsubstituted.  The history of that
asymmetry, and what it costs to remove, is Part 5's closing note.

## 1. Where the bridges stood, and what changed

Two independent obstructions were measured here.

* **β.** `R.tyVal D j = mkLams D.params …`, and `VInductDecl'.tyApp` supplies the block's
  parameter run as `bvars k D.np`, so a *companion* head becomes a saturated `D.np`-fold
  β-redex under `substC`, while `tyAppR` is the contractum
  (`InductiveDeclExamples.ntreeNode_substC_ne_typeR`, a `decide`).  Part 3 measures it exactly:
  `substC_tyApp_comp` computes the redex, `instAll_tyBody` proves its contractum is the
  restored head, so the gap is `D.np` β-steps per companion occurrence and nothing else.
  **This obstruction is still open** above `D.np = 0`, and it is not an artefact: Lean's own
  kernel stores the *contractum* (`ntreeNode_typeR`, `ntreeNode_declared_typeR`,
  `Theory/Inductive/NestedHead.lean`, `rfl` against `type_of% @NTree.node`), so `typeR` cannot
  be *defined* as `substC` — `TrConstant` relates the two through `TrExprS`, which has no defeq
  slack.  Closing it needs the telescope-defeq route
  (`VEnv.ctorConstsCR_wf_of_substC'`), not a syntactic equation.

* **Positions restoration never visits — CLOSED.**  `VIndCtor.typeR` restores the *result*
  head and the *recursive* fields' heads, and copies `C.params`, every **non**-recursive
  field's stored type and `C.args` verbatim.  `VIndCtor.WF.params_eq` and `VIndField.WF.pos`'s
  `none` branch make those only *definitionally* block-free — deliberately, with
  `(fun _ : T => Nat) r` as the accepted shape — so a companion constant could sit under a
  redex in one of them and be *declared*.  That was not a β-gap and not repairable by defeq
  slack: the step declared a constant whose type names a constant the environment does not
  hold.

  The repair is in `VInductDecl'.ctorConstsCR` and `recConstsR`: the declared type is
  `(C.typeR D R j).substC σ`, the abstract counterpart of `restoreNested` being a
  whole-expression `replaceNoCache`.  It is the **identity** on every position `typeR` already
  restored (checked at the real parameterised witness, `ntreeNode_declared_typeR`), so nothing
  the implementation declares moves; and it removes the dirt everywhere else.

## 2. Obligation (A) is a theorem for `D.params = []`, with no side condition on the block

`VEnv.ctorConstsCR_wf_of_np_zero'` (Part 4b) needs `Canonical`, `OwnId`, `Nodup`, and three
`decide`-able side conditions on the restoration *data* — and **no cleanliness hypothesis**.
`VIndCtor.RestoreClean` is no longer a hypothesis of anything; Part 4 keeps it, and
`VIndRestore.ctorType_substC_eq_typeR`, as the statement of what the new `substC` does *not*
change on a clean block.

## 3. What Part 5 is now

`nfnAuxDirty` — `nfnAux` with one extra non-recursive field whose stored type mentions
`_nested.PFn_1` under a redex — still satisfies **every** conjunct of `VEnv.AddNestedB`
(`nfnAuxDirty_AddNestedB`), and it is still not `RestoreClean`
(`nfnNodeDirty_not_restoreClean`).  What has changed is the conclusion:
`nfnAuxDirty_obligationA` now *proves* obligation (A) there, through the general theorem.
`nfnAuxDirty_step_not_ordered` and `nfnAuxDirty_obligationA_false` are **gone**; they were
theorems about the old `ctorConstsCR`.

The counterexample has not evaporated, it has **moved**: `VEnv.addIndRulesR` does not
substitute, `iotaCtxR` splices `C.fieldTypesR`, and the dirty entry is still there
(`nfnNodeDirty_fieldTypesR_dirty`, `nfnAuxDirty_iotaCtxR_eq`).  So `nfnAuxDirty` refutes
`hrules` where it used to refute `hctors`.

## 4. Obligations (B) and (C) carry a *third* obstruction

They run on `csubst`, not `csubstTy`, and `csubst`'s domain contains the companion's
**constructor** and **recursor** names as well — names that are *not* in `D.blockNames`
(`nfn_csubst_dom_escapes_blockNames`).  For (A) that is harmless and provably so: `D.WF env`
types a constructor in the environment carrying the block's *type* constants only, so no
constructor or recursor name of the block can occur in `C.type D j` at all.  For (B)/(C) it is
not: the recursor's type and the ι-rules are checked where those constants exist.  Part 6
records it.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars instAll)

/-! ## Part 1: the syntactic toolkit

`substC` is a structural homomorphism, so it commutes with every telescope former.
`VExpr.substC_mkPi` is in `ConstSubstNested.lean`; `substC_mkApp`, `substC_mkLams` and
`map_substC_bvars` **moved down to `Theory/Inductive/Restore.lean`** when
`VEnv.addIndRulesR` started substituting — `Theory/Inductive/NestedKeys.lean` needs them and
does not import this file. -/

namespace VExpr
variable {σ : CSubst}

/-- A term free of every constant in a name list is `substC`-invariant for any `σ` whose
domain sits inside that list. -/
theorem NoConsts.noCSubst {S : List Name} (hdom : ∀ n, σ n ≠ none → n ∈ S) :
    ∀ {e : VExpr}, e.NoConsts S → e.NoCSubst σ
  | .bvar _, _ | .sort _, _ => trivial
  | .const c _, h => by
    cases hc : σ c with
    | none => exact hc
    | some _ => exact absurd (hdom c (by rw [hc]; exact nofun)) h
  | .app .., h | .lam .., h | .forallE .., h =>
    ⟨NoConsts.noCSubst hdom h.1, NoConsts.noCSubst hdom h.2⟩

end VExpr

/-! ## Part 2: what is in `VIndRestore.csubstTy`'s domain

Exactly the **companion** members' type constants, and nothing else.  Both directions are
load-bearing: "nothing else" is what makes the positions the step declares under their own
names `substC`-invariant, and "these" is what rewrites a companion position. -/

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Lean.Name}

/-- **Every name in `csubstTy`'s domain is a companion member's**, and its value is that
member's presented spine. -/
theorem csubstTy_dom {n : Lean.Name} {v : VExpr} (h : R.csubstTy D K n = some v) :
    ∃ (j : Nat) (T : VIndType), D.types[j]? = some T ∧ T.name = n ∧ T.name ∈ K ∧
      v = R.tyVal D j := by
  have h := Lean4Lean.List.lookup_mem h
  rw [csubstTyList, List.mem_map] at h
  obtain ⟨⟨T, j⟩, hmem, hp⟩ := h
  rw [List.mem_filter] at hmem
  obtain ⟨hz, hd⟩ := hmem
  cases hp
  exact ⟨j, T, List.mk_mem_zipIdx_iff_getElem?.1 hz, rfl, of_decide_eq_true hd, rfl⟩

/-- Off `K` the substitution is the identity — which is what `VIndRestore.OwnId` is for. -/
theorem csubstTy_eq_none {n : Lean.Name} (hK : n ∉ K) : R.csubstTy D K n = none := by
  cases h : R.csubstTy D K n with
  | none => rfl
  | some v => obtain ⟨_, _, _, rfl, hK', _⟩ := csubstTy_dom h; exact absurd hK' hK

/-- …and its whole domain is inside the block's own member names. -/
theorem csubstTy_dom_blockNames {n : Lean.Name} (h : R.csubstTy D K n ≠ none) :
    n ∈ D.blockNames := by
  cases hc : R.csubstTy D K n with
  | none => exact absurd hc h
  | some v =>
    obtain ⟨j, T, hT, rfl, -, -⟩ := csubstTy_dom hc
    rw [VInductDecl'.blockNames, List.mem_map]
    exact ⟨T, List.mem_of_getElem? hT, rfl⟩

/-- **A block-free term is `csubstTy`-invariant.**  This is what turns `VIndCtor.WF`'s
`NoBlock` clauses — a recursive field's `ξ` and `π`, a constructor's result indices — into
`substC`-invariance for free. -/
theorem noBlock_noCSubst {e : VExpr} (h : D.NoBlock e) : e.NoCSubst (R.csubstTy D K) :=
  VExpr.NoConsts.noCSubst (fun _ => csubstTy_dom_blockNames) h

private theorem lookup_csubstTyList_aux (R : VIndRestore) (D : VInductDecl')
    (K : List Lean.Name) :
    ∀ (L : List (VIndType × Nat)), (L.map (·.1.name)).Nodup →
      ∀ {T : VIndType} {j : Nat}, (T, j) ∈ L → T.name ∈ K →
        ((L.filter fun p => decide (p.1.name ∈ K)).map
            (fun p => (p.1.name, R.tyVal D p.2))).lookup T.name = some (R.tyVal D j)
  | [], _, _, _, hm, _ => absurd hm nofun
  | (T₀, j₀) :: L, hnd, T, j, hm, hK => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.filter_cons]
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      rw [if_pos (by simpa using hK), List.map_cons, List.lookup_cons]
      simp
    · have hne : T.name ≠ T₀.name := by
        intro hq
        exact hnd.1 (hq ▸ List.mem_map.2 ⟨(T, j), hm, rfl⟩)
      by_cases h0 : T₀.name ∈ K
      · rw [if_pos (decide_eq_true h0), List.map_cons, List.lookup_cons,
          show (T.name == T₀.name) = false from beq_eq_false_iff_ne.2 hne]
        exact lookup_csubstTyList_aux R D K L hnd.2 hm hK
      · rw [if_neg (by simpa using h0)]
        exact lookup_csubstTyList_aux R D K L hnd.2 hm hK

/-- **…and at a companion member the value is the presented spine.**  The `Nodup` hypothesis
is what `addIndTypes`' success already gives: `addConstList` fails on a repeated name. -/
theorem csubstTy_eq_some (hnd : D.blockNames.Nodup) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    R.csubstTy D K T.name = some (R.tyVal D j) := by
  refine lookup_csubstTyList_aux R D K D.types.zipIdx ?_
    (List.mk_mem_zipIdx_iff_getElem?.2 hT) hK
  have he : D.types.zipIdx.map (fun x : VIndType × Nat => x.fst.name) = D.blockNames := by
    rw [VInductDecl'.blockNames,
      show (fun x : VIndType × Nat => x.fst.name)
          = ((fun T : VIndType => T.name) ∘ Prod.fst) from rfl,
      ← List.map_map, List.zipIdx_map_fst]
  rw [he]; exact hnd

end VIndRestore

/-! ## Part 3: the β-gap, located and measured

The three bridges are equations between `X.substC σ` and `X`'s restored form, and `substC`
is structural, so they reduce to one equation per **head position**.  There are exactly two
kinds of head position, and they behave completely differently.

* A head the step declares under its own name (`T.name ∉ K`) is **not in σ's domain**, and
  `VIndRestore.OwnId` says the restored head is that same head — so the bridge holds there
  on the nose (`substC_tyApp_own`).
* A **companion** head is in σ's domain, and its value is `R.tyVal D j = mkLams D.params …`.
  `tyApp` supplies the parameter run as `bvars k D.np`, so the substituted form is a
  saturated `D.np`-fold **β-redex** (`substC_tyApp_comp`) whose contractum is the restored
  head (`instAll_tyBody`) — and nothing else differs.

So the residual on the (A) bridge is exactly `D.np` β-steps per companion occurrence: zero
when the block has no parameters, in which case the bridge is a theorem
(`substC_tyApp_eq_tyAppR`), and non-zero otherwise, in which case the bridge is **false**
(`InductiveDeclExamples.ntreeNode_substC_ne_typeR`, already in the tree). -/

namespace VExpr

theorem map_substC_eq_self {σ : CSubst} : ∀ {l : List VExpr},
    (∀ a ∈ l, a.NoCSubst σ) → l.map (VExpr.substC · σ) = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, (h a List.mem_cons_self).substC_eq,
      map_substC_eq_self (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- Indices above a saturated instantiation window just come down by its width — whatever
the arguments are. -/
theorem instAll_bvar_high_gen : ∀ {as : List VExpr} {m t : Nat},
    instAll (.bvar (m + as.length + t)) as m = .bvar (m + t)
  | [], _, _ => rfl
  | a :: as, m, t => by
    rw [instAll_cons]
    show instAll ((VExpr.bvar (m + (as.length + 1) + t)).inst a (m + as.length)) as m = _
    rw [show (VExpr.bvar (m + (as.length + 1) + t)).inst a (m + as.length)
        = .bvar (m + as.length + t) from by
      simp only [inst, instVar, if_neg (show ¬ (m + (as.length+1) + t < m + as.length) by omega),
        if_neg (show ¬ (m + (as.length+1) + t = m + as.length) by omega)]
      congr 1; omega]
    exact instAll_bvar_high_gen

theorem instAll_bvar_lift : ∀ {n j m i : Nat}, i < m + n →
    instAll (.bvar i) (bvars j n) m = .bvar (liftVar j i m)
  | 0, _, m, i, h => by
    rw [bvars, instAll_nil, liftVar, if_pos (by omega)]
  | n+1, j, m, i, h => by
    rw [bvars, instAll_cons, length_bvars]
    rcases Nat.lt_or_ge i (m + n) with h' | h'
    · rw [show (VExpr.bvar i).inst (.bvar (j + n)) (m + n) = .bvar i from by
        simp only [inst, instVar, if_pos h']]
      exact instAll_bvar_lift h'
    · have hi : i = m + n := by omega
      subst hi
      rw [show (VExpr.bvar (m + n)).inst (.bvar (j + n)) (m + n)
          = .bvar (m + n + (j + n)) from by
        simp only [inst, instVar, if_neg (Nat.lt_irrefl _), if_true, liftN, liftVar_base]]
      rw [show m + n + (j + n) = m + (bvars j n).length + (j + n) from by
          rw [length_bvars],
        instAll_bvar_high_gen, liftVar, if_neg (by omega)]
      congr 1; omega

/-- **Saturated β on a shifted identity spine.**  `instAll_bvars` is the `j = 0` case (which
gives `e` back); this is the general one, and it is the equation that says the contractum of
a substituted companion head is the *restored* head. -/
theorem instAll_bvars_lift : ∀ {e : VExpr} {n j m : Nat}, e.ClosedN (m + n) →
    instAll e (bvars j n) m = e.liftN j m
  | .bvar _, _, _, _, h => instAll_bvar_lift h
  | .sort _, _, _, _, _ => by simp [liftN]
  | .const .., _, _, _, _ => by simp [liftN]
  | .app .., _, _, _, h => by
    rw [instAll_app, instAll_bvars_lift h.1, instAll_bvars_lift h.2]; rfl
  | .lam .., _, _, m, h => by
    rw [instAll_lam, instAll_bvars_lift h.1,
      instAll_bvars_lift (m := m+1) (by rw [Nat.add_right_comm]; exact h.2)]
    rfl
  | .forallE .., _, _, m, h => by
    rw [instAll_forallE, instAll_bvars_lift h.1,
      instAll_bvars_lift (m := m+1) (by rw [Nat.add_right_comm]; exact h.2)]
    rfl

end VExpr

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Lean.Name}

/-- The body of `R.tyVal D j`: the presented head applied to the presented spine, over the
block's parameters. -/
def tyBody (R : VIndRestore) (D : VInductDecl') (j : Nat) : VExpr :=
  (VExpr.const (R.tyName j) (R.tyLvls j)).mkApp (R.tyArgs j)

theorem tyVal_eq (R : VIndRestore) (D : VInductDecl') (j : Nat) :
    R.tyVal D j = mkLams D.params (R.tyBody D j) := rfl

/-- **The contractum of a substituted companion head is the restored head, exactly.**  This
is the whole content of "the two sides differ by β and by nothing else". -/
theorem instAll_tyBody (hcl : ∀ a ∈ R.tyArgs j, a.ClosedN D.np) (k : Nat)
    (args : List VExpr) :
    (VExpr.instAll (R.tyBody D j) (bvars k D.np)).mkApp args = D.tyAppR R j k args := by
  rw [tyBody, VExpr.instAll_mkApp, VExpr.instAll_const, VInductDecl'.tyAppR,
    VInductDecl'.tyAppH, ← VExpr.mkApp_append]
  congr 2
  exact List.map_congr_left fun a ha => VExpr.instAll_bvars_lift (by simpa using hcl a ha)

/-- **A head off `K` does not move**, and `OwnId` says the restored head is the same head. -/
theorem substC_tyApp_own (hown : R.OwnId D K) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hK : T.name ∉ K) {k : Nat} {args : List VExpr}
    (hargs : ∀ a ∈ args, a.NoCSubst (R.csubstTy D K)) :
    (D.tyApp j k args).substC (R.csubstTy D K) = D.tyAppR R j k args := by
  have hg : (D.types.getD j default).name = T.name := by
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  rw [VInductDecl'.tyApp, VExpr.substC_mkApp,
    VExpr.substC_const_none (by rw [hg]; exact csubstTy_eq_none hK),
    List.map_append, VExpr.map_substC_bvars, VExpr.map_substC_eq_self hargs,
    ← VInductDecl'.tyApp, hown.tyAppR_eq hT hK]

/-- **A companion head becomes a saturated `D.np`-fold redex.** -/
theorem substC_tyApp_comp (hnd : D.blockNames.Nodup) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hlw : (R.tyVal D j).LevelWF D.uvars) {k : Nat} {args : List VExpr}
    (hargs : ∀ a ∈ args, a.NoCSubst (R.csubstTy D K)) :
    (D.tyApp j k args).substC (R.csubstTy D K)
      = (mkLams D.params (R.tyBody D j)).mkApp (bvars k D.np ++ args) := by
  have hg : (D.types.getD j default).name = T.name := by
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  rw [VInductDecl'.tyApp, VExpr.substC_mkApp,
    VExpr.substC_const_some (by rw [hg]; exact csubstTy_eq_some hnd hT hK),
    List.map_append, VExpr.map_substC_bvars, VExpr.map_substC_eq_self hargs,
    show (R.tyVal D j).instL D.ownLvls = R.tyVal D j from
      VExpr.LevelWF.instL_id (U := D.uvars) hlw,
    tyVal_eq]

/-- **The (A)-bridge head equation, in general, for a block with no parameters.**  Both kinds
of head position are covered; the `D.params = []` hypothesis is exactly the absence of the
β-gap. -/
theorem substC_tyApp_eq_tyAppR (hp : D.params = []) (hnd : D.blockNames.Nodup)
    (hown : R.OwnId D K)
    (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T)
    {k : Nat} {args : List VExpr}
    (hargs : ∀ a ∈ args, a.NoCSubst (R.csubstTy D K)) :
    (D.tyApp j k args).substC (R.csubstTy D K) = D.tyAppR R j k args := by
  by_cases hK : T.name ∈ K
  · have hnp : D.np = 0 := by rw [show D.np = D.params.length from rfl, hp]; rfl
    have h2 := instAll_tyBody (R := R) (D := D) (j := j) (hcl j) k args
    rw [hnp, VExpr.bvars_zero, VExpr.instAll_nil] at h2
    rw [substC_tyApp_comp hnd hT hK (hlw j) hargs, hnp, VExpr.bvars_zero, List.nil_append,
      hp, VExpr.mkLams_nil]
    exact h2
  · exact substC_tyApp_own hown hT hK hargs

end VIndRestore

/-! ## Part 4: the (A) bridge for a parameterless block, and the side condition it needs

`VIndCtor.typeR` restores the constructor's **result** head and its **recursive** fields'
heads, and copies `C.params` and every **non-recursive** field's stored type verbatim.  So
the bridge asks for two things: that the restored positions agree (Part 3), and that the
copied ones carry no companion constant at all.  The second is `VIndCtor.RestoreClean`, and
it is a genuinely new side condition — see the refutation at the end of this file. -/

namespace VIndCtor

/-- **The positions `VIndCtor.typeR` does not rewrite must already be companion-free.**

`VIndField.WF.pos`'s `none` branch requires a non-recursive field's stored type to be only
*definitionally* block-free, and `VIndCtor.WF.params_eq` requires `C.params` to be only
*definitionally* `D.params`.  So a companion constant may sit under a redex in either place,
and `typeR` leaves it there.

**Not implied by `VEnv.AddNested`, nor by `VEnv.AddNestedB`.**
`InductiveDeclExamples.nfnAuxDirty_refutation` is the counterexample. -/
def RestoreClean (C : VIndCtor) (σ : CSubst) : Prop :=
  (∀ A ∈ C.params, A.NoCSubst σ) ∧ ∀ F ∈ C.fields, F.recArg = none → F.type.NoCSubst σ

end VIndCtor

/-- The two `NoBlock` clauses of a recursive field's `pos`, plus its index bound, read off
`VIndField.WF`. -/
theorem VIndField.WF.recArg_noBlock {env : VEnv} {D : VInductDecl'} {pre : List VIndField}
    {Γ : List VExpr} {i : Nat} {F : VIndField} (h : F.WF env D pre Γ i) {r : VIndRecArg}
    (hr : F.recArg = some r) :
    r.idx < D.nm ∧ (∀ B ∈ r.binders, D.NoBlock B) ∧ (∀ a ∈ r.args, D.NoBlock a) := by
  have hp := h.pos
  rw [hr] at hp
  exact ⟨hp.1, hp.2.2.1, hp.2.2.2.1⟩

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Lean.Name}
variable (hp : D.params = []) (hnd : D.blockNames.Nodup) (hown : R.OwnId D K)
  (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
  (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np)

include hp hnd hown hlw hcl

/-- **One field's bridge.**  Either the field is non-recursive, in which case `typeR` copies
it and cleanliness is exactly what is needed; or it is recursive and canonical, in which case
Part 3's head equation does it. -/
theorem field_typeR_substC {F : VIndField} {i : Nat}
    (hnone : F.recArg = none → F.type.NoCSubst (R.csubstTy D K))
    (hsome : ∀ r, F.recArg = some r → F.type = r.canonType D i ∧ r.idx < D.nm ∧
      (∀ B ∈ r.binders, D.NoBlock B) ∧ (∀ a ∈ r.args, D.NoBlock a)) :
    F.type.substC (R.csubstTy D K) = F.typeR D R i := by
  cases hr : F.recArg with
  | none =>
    rw [show F.typeR D R i = F.type from by rw [VIndField.typeR, hr]]
    exact (hnone hr).substC_eq
  | some r =>
    obtain ⟨hct, hlt, hb, ha⟩ := hsome r hr
    obtain ⟨T', hT'⟩ : ∃ T', D.types[r.idx]? = some T' :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [R.typeR_canonical hnd hr hT' hb hct,
      hct, VIndRecArg.canonType, VExpr.substC_mkPi, VIndRecArg.canonTypeR,
      VExpr.map_substC_eq_self (fun B hB => noBlock_noCSubst (hb B hB)),
      VIndRecArg.canonResult, VIndRecArg.canonResultR,
      substC_tyApp_eq_tyAppR hp hnd hown hlw hcl hT'
        (fun a haa => noBlock_noCSubst (ha a haa))]

/-- The field telescope's bridge, entrywise. -/
theorem fieldTypes_substC :
    ∀ (Fs : List VIndField) (i : Nat),
      (∀ (k : Nat) (F : VIndField), Fs[k]? = some F → F.recArg = none →
        F.type.NoCSubst (R.csubstTy D K)) →
      (∀ (k : Nat) (F : VIndField) (r : VIndRecArg), Fs[k]? = some F → F.recArg = some r →
        F.type = r.canonType D (i + k) ∧ r.idx < D.nm ∧
        (∀ B ∈ r.binders, D.NoBlock B) ∧ (∀ a ∈ r.args, D.NoBlock a)) →
      Fs.map (fun F => F.type.substC (R.csubstTy D K))
        = (Fs.zipIdx i).map (fun p => p.1.typeR D R p.2)
  | [], _, _, _ => rfl
  | F :: Fs, i, hn, hs => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons,
      field_typeR_substC hp hnd hown hlw hcl (F := F) (i := i)
        (hn 0 F rfl) (fun r hr => by simpa using hs 0 F r rfl hr),
      fieldTypes_substC Fs (i+1)
        (fun k F' hF' => hn (k+1) F' (by simpa using hF'))
        (fun k F' r hF' hr => by
          rw [show i + 1 + k = i + (k+1) from by omega]
          exact hs (k+1) F' r (by simpa using hF') hr)]

/-- **Obligation (A)'s bridge, in general, for a block with no parameters.**  Every
hypothesis is either a `Nodup`/level/closedness side condition of the substitution (the same
ones `csubst_closed` takes), `OwnId`, `D.Canonical`, or the new cleanliness condition. -/
theorem ctorType_substC_eq_typeR {C : VIndCtor} {j : Nat}
    (hclean : C.RestoreClean (R.csubstTy D K)) (hcanon : C.Canonical D)
    (hpos : ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r →
      r.idx < D.nm ∧ (∀ B ∈ r.binders, D.NoBlock B) ∧ (∀ a ∈ r.args, D.NoBlock a))
    (hargs : ∀ a ∈ C.args, D.NoBlock a)
    {T : VIndType} (hT : D.types[j]? = some T) :
    (C.type D j).substC (R.csubstTy D K) = C.typeR D R j := by
  have hfl : C.fields.map (fun F => F.type.substC (R.csubstTy D K)) = C.fieldTypesR D R := by
    rw [VIndCtor.fieldTypesR]
    exact fieldTypes_substC hp hnd hown hlw hcl C.fields 0
      (fun k F hF => hclean.2 F (List.mem_of_getElem? hF))
      (fun k F r hF hr => ⟨by simpa using hcanon k F r hF hr, hpos k F r hF hr⟩)
  rw [VIndCtor.type, VExpr.substC_mkPi, VIndCtor.typeR, VIndCtor.canonResult,
    substC_tyApp_eq_tyAppR hp hnd hown hlw hcl hT
      (fun a ha => noBlock_noCSubst (hargs a ha)),
    List.map_append, VExpr.map_substC_eq_self hclean.1, List.map_map,
    show ((fun x : VExpr => x.substC (R.csubstTy D K)) ∘ fun F : VIndField => F.type)
        = (fun F : VIndField => F.type.substC (R.csubstTy D K)) from rfl, hfl]

end VIndRestore

/-! ## Part 4b: the (A) bridge **without** the cleanliness side condition

`VInductDecl'.ctorConstsCR` no longer declares `C.typeR D R j` but
`(C.typeR D R j).substC (R.csubstTy D K)` — the restoration substituted through the positions
`typeR` copies verbatim, which is what `restoreNested`'s whole-expression `replaceNoCache`
does and what `VIndCtor.RestoreClean` was standing in for.  The bridge that
`VEnv.ctorConstsCR_wf_of_substC` now asks for is therefore

    (C.type D j).substC σ = (C.typeR D R j).substC σ,      σ = R.csubstTy D K

and **that is a theorem with no cleanliness hypothesis at all**: every position `typeR`
copies appears under `substC σ` on *both* sides, so it cancels rather than having to be
assumed clean.  What is left is one equation per *head* position, and there the two sides
differ only by the β-gap of Part 3 — zero at `D.np = 0`.

Two side conditions on the restoration data appear that Part 4 did not need, both of the same
`decide`-able nature as `hlw`/`hcl`: the presented head `R.tyName i` and spine `R.tyArgs i`
must not themselves name a companion member.  A restoration violating either would present a
companion member *as another companion member*; nothing downstream would be true of it. -/

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Lean.Name}
variable (hp : D.params = []) (hnd : D.blockNames.Nodup) (hown : R.OwnId D K)
  (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
  (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np)
  (hnn : ∀ i, R.csubstTy D K (R.tyName i) = none)
  (hna : ∀ i, ∀ a ∈ R.tyArgs i, a.NoCSubst (R.csubstTy D K))

include hp hnd hown hlw hcl

/-- **The head equation with the arguments substituted on both sides.**  Compare
`substC_tyApp_eq_tyAppR`, which needs the arguments to be `σ`-invariant; here they are
rewritten by `σ` in the conclusion, so nothing is assumed about them. -/
theorem substC_tyApp_eq_tyAppR_map {j : Nat} (hna' : ∀ a ∈ R.tyArgs j, a.ClosedN 0)
    {T : VIndType} (hT : D.types[j]? = some T) {k : Nat} {args : List VExpr} :
    (D.tyApp j k args).substC (R.csubstTy D K)
      = D.tyAppR R j k (args.map (VExpr.substC · (R.csubstTy D K))) := by
  have hnp : D.np = 0 := by rw [show D.np = D.params.length from rfl, hp]; rfl
  have hg : (D.types.getD j default).name = T.name := by
    rw [List.getD_eq_getElem?_getD, hT]; rfl
  rw [VInductDecl'.tyApp, VExpr.substC_mkApp, List.map_append, VExpr.map_substC_bvars]
  by_cases hK : T.name ∈ K
  · have hid : ((R.tyArgs j).map fun x => x.liftN k) = R.tyArgs j := by
      rw [show ((R.tyArgs j).map fun x => x.liftN k) = (R.tyArgs j).map id from
        List.map_congr_left fun a ha => (hna' a ha).liftN_eq (Nat.zero_le _), List.map_id]
    rw [VExpr.substC_const_some (by rw [hg]; exact csubstTy_eq_some hnd hT hK),
      show (R.tyVal D j).instL D.ownLvls = R.tyVal D j from
        VExpr.LevelWF.instL_id (U := D.uvars) (hlw j),
      tyVal_eq, hp, VExpr.mkLams_nil, tyBody, VInductDecl'.tyAppR, VInductDecl'.tyAppH,
      ← VExpr.mkApp_append, hnp, VExpr.bvars_zero, List.nil_append, hid]
  · rw [VExpr.substC_const_none (by rw [hg]; exact csubstTy_eq_none hK),
      hnp, VExpr.bvars_zero, List.nil_append,
      show (VExpr.const (D.types.getD j default).name D.ownLvls).mkApp
            (args.map (VExpr.substC · (R.csubstTy D K)))
          = D.tyApp j k (args.map (VExpr.substC · (R.csubstTy D K))) from by
        rw [VInductDecl'.tyApp, hnp, VExpr.bvars_zero, List.nil_append],
      hown.tyAppR_eq hT hK]

include hnn hna

/-- **…and the restored head is `σ`-invariant**, which is what lets the right-hand side of the
bridge carry a `substC σ` that does nothing to the head. -/
theorem substC_tyAppR (j k : Nat) (args : List VExpr) :
    (D.tyAppR R j k args).substC (R.csubstTy D K)
      = D.tyAppR R j k (args.map (VExpr.substC · (R.csubstTy D K))) := by
  rw [VInductDecl'.tyAppR, VInductDecl'.tyAppH, VExpr.substC_mkApp,
    VExpr.substC_const_none (hnn j), List.map_append, List.map_map]
  congr 2
  exact List.map_congr_left fun a ha =>
    ((hna j a ha).liftN (n := k) (k := 0)).substC_eq

/-- **The (A) bridge, in general, for a parameterless block — no `RestoreClean`.** -/
theorem ctorType_substC_eq_typeR_substC {C : VIndCtor} {j : Nat}
    (hcanon : C.Canonical D)
    (hpos : ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → r.idx < D.nm ∧ ∀ B ∈ r.binders, D.NoBlock B)
    (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)
    {T : VIndType} (hT : D.types[j]? = some T) :
    (C.type D j).substC (R.csubstTy D K)
      = (C.typeR D R j).substC (R.csubstTy D K) := by
  have hfl : ∀ (Fs : List VIndField) (i : Nat),
      (∀ (k : Nat) (F : VIndField) (r : VIndRecArg), Fs[k]? = some F → F.recArg = some r →
        F.type = r.canonType D (i + k) ∧ r.idx < D.nm ∧ ∀ B ∈ r.binders, D.NoBlock B) →
      Fs.map (fun F => F.type.substC (R.csubstTy D K))
        = ((Fs.zipIdx i).map (fun p => p.1.typeR D R p.2)).map
            (VExpr.substC · (R.csubstTy D K)) := by
    intro Fs
    induction Fs with
    | nil => intro _ _; rfl
    | cons F Fs ih =>
      intro i hs
      rw [List.zipIdx_cons, List.map_cons, List.map_cons, List.map_cons,
        ih (i+1) (fun k F' r hF' hr => by
          rw [show i + 1 + k = i + (k+1) from by omega]
          exact hs (k+1) F' r (by simpa using hF') hr)]
      congr 1
      cases hr : F.recArg with
      | none => rw [show F.typeR D R i = F.type from by rw [VIndField.typeR, hr]]
      | some r =>
        obtain ⟨hct, hlt, hb⟩ := hs 0 F r rfl hr
        obtain ⟨T', hT'⟩ : ∃ T', D.types[r.idx]? = some T' := ⟨_, List.getElem?_eq_getElem hlt⟩
        rw [show i + 0 = i from rfl] at *
        rw [R.typeR_canonical hnd hr hT' hb hct]
        rw [hct, VIndRecArg.canonType, VIndRecArg.canonTypeR, VExpr.substC_mkPi,
          VExpr.substC_mkPi, VIndRecArg.canonResult, VIndRecArg.canonResultR,
          substC_tyApp_eq_tyAppR_map hp hnd hown hlw hcl (hcl0 r.idx) hT',
          substC_tyAppR hp hnd hown hlw hcl hnn hna]
  rw [VIndCtor.type, VIndCtor.typeR, VExpr.substC_mkPi, VExpr.substC_mkPi,
    List.map_append, List.map_append, VIndCtor.canonResult,
    substC_tyApp_eq_tyAppR_map hp hnd hown hlw hcl (hcl0 j) hT,
    substC_tyAppR hp hnd hown hlw hcl hnn hna, List.map_map,
    show ((fun x : VExpr => x.substC (R.csubstTy D K)) ∘ fun F : VIndField => F.type)
        = (fun F : VIndField => F.type.substC (R.csubstTy D K)) from rfl,
    VIndCtor.fieldTypesR,
    hfl C.fields 0 (fun k F r hF hr =>
      ⟨by simpa using hcanon k F r hF hr, hpos k F r hF hr⟩)]

end VIndRestore

/-- **Obligation (A), in general, for a parameterless nested block, with no cleanliness
condition.**

This is `VEnv.ctorConstsCR_wf_of_np_zero` with `hclean` **removed** — the hypothesis that
`nfnAuxDirty` refuted.  What replaced it is the `substC` in `VInductDecl'.ctorConstsCR`, i.e.
the abstract counterpart of `restoreNested` restoring the occurrence wherever it sits.  The
two new hypotheses are side conditions on the restoration *data*, not on the block. -/
theorem VEnv.ctorConstsCR_wf_of_np_zero' {env env₃ e₁ : VEnv} {D : VInductDecl'}
    {K : List Lean.Name} {R : VIndRestore}
    (hD : D.WF env) (h₃ : env.addIndTypes D = some env₃) (henv₃ : env₃.Ordered)
    (hσ : (R.csubstTy D K).WF env₃ e₁ D.uvars)
    (hp : D.params = []) (hnd : D.blockNames.Nodup) (hown : R.OwnId D K)
    (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np)
    (hnn : ∀ i, R.csubstTy D K (R.tyName i) = none)
    (hna : ∀ i, ∀ a ∈ R.tyArgs i, a.NoCSubst (R.csubstTy D K))
    (hcanon : D.Canonical) :
    ∀ c ∈ D.ctorConstsCR R K, VConstant.WF e₁ c.2 := by
  refine VEnv.ctorConstsCR_wf_of_substC hD h₃ henv₃ hσ ?_
  intro j T C hT hK hC
  have hnp : D.np = 0 := by rw [show D.np = D.params.length from rfl, hp]; rfl
  have hct := hD.ctors env₃ h₃ j T hT C hC
  exact VIndRestore.ctorType_substC_eq_typeR_substC hp hnd hown hlw hcl hnn hna
    (hcanon j C (VInductDecl'.mem_ctorsAll_of hT hC))
    (fun i F r hF hr =>
      let hn := (hct.fields i F hF).recArg_noBlock hr; ⟨hn.1, hn.2.1⟩)
    (fun i => hnp ▸ hcl i) hT

/-! ### The superseded form

`VEnv.ctorConstsCR_wf_of_np_zero` used to sit here: obligation (A) for a parameterless block
**given `VIndCtor.RestoreClean`**, which `nfnAuxDirty` refutes as a consequence of
`VEnv.AddNestedB`.  It is gone, replaced by `VEnv.ctorConstsCR_wf_of_np_zero'` above, which
needs no cleanliness at all.  `VIndRestore.ctorType_substC_eq_typeR` (Part 4) survives as the
statement that *under* `RestoreClean` the old, unsubstituted `typeR` was already the bridge's
right-hand side — i.e. that the `substC` in `ctorConstsCR` changes nothing on a clean block,
which is the faithfulness half. -/

namespace InductiveDeclExamples


/-! ### The general (A) bridge is not vacuous: it re-proves the `NFn`/`PFn` witness

`nfn_csubstTy` (`ConstSubstNested.lean`) already checks that the general `VIndRestore.csubstTy`
*is* the hand-written `nfnSubst`, so the general theorem applies verbatim where the bespoke
`rfl` bridge did. -/

theorem nfnAux_params_nil : nfnAux.params = [] := rfl
theorem nfnAux_blockNames_nodup : nfnAux.blockNames.Nodup := by decide

theorem nfnRestore_tyVal_levelWF (i : Nat) :
    (nfnRestore.tyVal nfnAux i).LevelWF nfnAux.uvars := by
  rw [VIndRestore.tyVal, nfnAux_params_nil, VExpr.mkLams_nil,
    show nfnRestore.tyArgs i = if i = 1 then [VExpr.const ``NFn []] else [] from rfl]
  split
  · exact ⟨nofun, nofun⟩
  · exact nofun

theorem nfnRestore_tyArgs_closed (i : Nat) :
    ∀ a ∈ nfnRestore.tyArgs i, a.ClosedN nfnAux.np := by
  rw [show nfnRestore.tyArgs i = if i = 1 then [VExpr.const ``NFn []] else [] from rfl]
  split
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; trivial
  · intro a ha; simp at ha

theorem nfnNode_restoreClean : nfnNode.RestoreClean nfnSubst :=
  ⟨nofun, by
    intro F hF hr
    simp only [nfnNode, List.mem_cons, List.not_mem_nil, or_false] at hF
    subst hF
    exact absurd hr nofun⟩

theorem pfnAuxMk_restoreClean : pfnAuxMk.RestoreClean nfnSubst :=
  ⟨nofun, by
    intro F hF hr
    simp only [pfnAuxMk, List.mem_cons, List.not_mem_nil, or_false] at hF
    obtain rfl | rfl := hF <;> exact absurd hr nofun⟩

section
variable {env₂ env₃ env₄ : VEnv}
variable (h : VEnv.empty.addInduct' pfnDecl = some env₂) (henv₂ : env₂.Ordered)
variable (h₃ : env₂.addIndTypes nfnAux = some env₃)
variable (h₄ : env₂.addConstList (nfnAux.typeConstsC nfnK) = some env₄)

include h henv₂ h₃ h₄ in
/-- **Obligation (A) at `NFn`/`PFn`, through the general bridge.**  Compare
`nfnAux_ctorConstsCR_wf`, which supplies `hbridge` by `rfl` at this one block. -/
theorem nfnAux_ctorConstsCR_wf_general :
    ∀ c ∈ nfnAux.ctorConstsCR nfnRestore nfnK, VConstant.WF env₄ c.2 :=
  VEnv.ctorConstsCR_wf_of_np_zero' nfnAux_WF h₃ (env₃_ordered henv₂ h₃)
    (by rw [nfn_csubstTy]; exact nfnSubst_WF h henv₂ h₃ h₄)
    nfnAux_params_nil nfnAux_blockNames_nodup nfnRestore_ownId
    nfnRestore_tyVal_levelWF nfnRestore_tyArgs_closed
    (by rw [nfn_csubstTy]; rintro (_ | _ | i) <;> rfl)
    (by
      rw [nfn_csubstTy]
      intro i a ha
      rw [show nfnRestore.tyArgs i = if i = 1 then [VExpr.const ``NFn []] else [] from rfl] at ha
      split at ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        subst ha; exact nfnSubst_of_ne (by decide)
      · simp at ha)
    ((nfnAux_built h).canonical nfnAux_canonicalOwn)

end

/-! ## Part 5: the refutation — the cleanliness condition is not optional

Everything above is conditional on `VIndCtor.RestoreClean`.  This section shows the condition
is load-bearing: a block that fails it satisfies **every** premise of `VEnv.AddNestedB` — the
constructive form of the nested step, which implies `VEnv.AddNestedStep`, which is what
`VDecl.WF.inductNested` takes — and the step it licenses produces an environment that is not
`Ordered`. -/

/-- A **non-recursive** field whose stored type mentions the companion constant
`_nested.PFn_1` — but only under a β-redex, so it is *definitionally* block-free, which is
all `VIndField.WF.pos`'s `none` branch asks for. -/
def nfnDirtyField : VIndField where
  type := .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.const `_nested.PFn_1 [])
  lvl := .succ .zero
  recArg := none

/-- `nfnNode` with that one extra field. -/
def nfnNodeDirty : VIndCtor where
  name := ``NFn.node
  params := []
  fields :=
    [{ type := .const `_nested.PFn_1 [], lvl := .succ .zero,
       recArg := some { binders := [], idx := 1, args := [] } },
     nfnDirtyField]
  args := []

/-- `nfnAux` with the dirty constructor.  The companion member is untouched. -/
def nfnAuxDirty : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := true
  types :=
    [{ name := ``NFn, type := .sort (.succ .zero), indices := [], ctors := [nfnNodeDirty] },
     { name := `_nested.PFn_1, type := .sort (.succ .zero), indices := [],
       ctors := [pfnAuxMk] }]

theorem nfnAuxDirty_header : nfnAuxDirty.header = nfnAux.header := by
  rw [VInductDecl'.header, VInductDecl'.header]
  congr 1
  funext j
  match j with
  | 0 => rfl
  | 1 => rfl
  | (_+2) => rfl

theorem nfnAuxDirty_allNamesCR :
    nfnAuxDirty.allNamesCR nfnRestore nfnK = [``NFn, ``NFn.node, ``NFn.rec, ``NFn.rec_1] := rfl

theorem nfnAuxDirty_ctorConstsCR :
    nfnAuxDirty.ctorConstsCR nfnRestore nfnK
      = [(``NFn.node,
          ⟨0, (nfnNodeDirty.typeR nfnAuxDirty nfnRestore 0).substC
                (nfnRestore.csubstTy nfnAuxDirty nfnK)⟩)] := rfl

/-- **The dirt survives `VIndCtor.typeR`** — `VIndField.typeR` copies a non-recursive field's
stored type verbatim, so the companion constant is still there in the *canonical* restored
type.  What has changed is that this is no longer the type the step declares. -/
theorem nfnNodeDirty_typeR_eq :
    nfnNodeDirty.typeR nfnAuxDirty nfnRestore 0
      = .forallE (.app (.const ``PFn []) (.const ``NFn []))
          (.forallE (.app (.lam (.sort (.succ .zero)) (.sort .zero))
            (.const `_nested.PFn_1 [])) (.const ``NFn [])) := rfl

theorem nfnNodeDirty_typeR_dirty :
    ¬ (nfnNodeDirty.typeR nfnAuxDirty nfnRestore 0).NoCSubst nfnSubst := by
  rw [nfnNodeDirty_typeR_eq]
  intro h
  have h1 : nfnSubst `_nested.PFn_1 = none := h.2.1.2
  simp [nfnSubst_aux] at h1

/-- **…and the substitution removes it.**  The type `VInductDecl'.ctorConstsCR` declares is
the one above with `_nested.PFn_1` replaced by `PFn NFn` — the β-redex the field's `pos`
obligation was discharged through is still there (the implementation would leave it too;
`restoreNested` is a replacement, not a reduction), but it no longer names a constant the
environment does not hold. -/
theorem nfnNodeDirty_declared_eq :
    (nfnNodeDirty.typeR nfnAuxDirty nfnRestore 0).substC (nfnRestore.csubstTy nfnAuxDirty nfnK)
      = .forallE (.app (.const ``PFn []) (.const ``NFn []))
          (.forallE (.app (.lam (.sort (.succ .zero)) (.sort .zero))
            (.app (.const ``PFn []) (.const ``NFn []))) (.const ``NFn [])) := rfl

/-- **The declared type is clean.**  This is the refutation's premise, negated: what
`nfnAuxDirty_step_not_ordered` used to derive `¬ Ordered` from is now false. -/
theorem nfnNodeDirty_declared_clean :
    ((nfnNodeDirty.typeR nfnAuxDirty nfnRestore 0).substC
      (nfnRestore.csubstTy nfnAuxDirty nfnK)).NoCSubst nfnSubst := by
  rw [nfnNodeDirty_declared_eq]
  exact ⟨⟨nfnSubst_of_ne (by decide), nfnSubst_of_ne (by decide)⟩,
    ⟨⟨trivial, trivial⟩, nfnSubst_of_ne (by decide), nfnSubst_of_ne (by decide)⟩,
    nfnSubst_of_ne (by decide)⟩


theorem nfnAuxDirty_typeConsts : nfnAuxDirty.typeConsts = nfnAux.typeConsts := rfl

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)

theorem nfnDirty_const_staged {env₃ : VEnv} (hs : env₂.addIndTypes nfnAuxDirty = some env₃) :
    env₃.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants hs (``NFn, ⟨0, .sort (.succ .zero)⟩) (by exact List.Mem.head _)

theorem pfnauxDirty_const_staged {env₃ : VEnv}
    (hs : env₂.addIndTypes nfnAuxDirty = some env₃) :
    env₃.constants `_nested.PFn_1 = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants hs (`_nested.PFn_1, ⟨0, .sort (.succ .zero)⟩)
    (by exact List.Mem.tail _ (List.Mem.head _))

/-- **The dirty block is well formed.**  Only the `j = 0`, `i = 1` case differs from
`nfnAux_WF`: the new field's `pos` obligation is discharged by `IsDefEq.beta`, which is
exactly what `VIndField.WF.pos`'s `none` branch is *designed* to allow (`Decl.lean`'s
`(fun _ : T => Nat) r` comment). -/
theorem nfnAuxDirty_WF : nfnAuxDirty.WF env₂ where
  types_ne := by simp [nfnAuxDirty]
  params := trivial
  types := by
    intro T hT
    simp only [nfnAuxDirty, List.mem_cons, List.not_mem_nil, or_false] at hT
    obtain rfl | rfl := hT <;>
      exact { indices := trivial, isType := ⟨_, by type_tac⟩, canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₃ hs j T hT C hC
    have hn := nfnDirty_const_staged hs
    have hp := pfnauxDirty_const_staged hs
    match j, hT with
    | 0, hT =>
      simp only [nfnAuxDirty] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .zero, fields := ?_, args_len := rfl,
               args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [nfnNodeDirty, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, nfnAuxDirty, Lean.Nat.imax]
                binders_indep := fun r hr => by
                  cases hr; intro _ _ _ _ _ _ k B hB; simp at hB
                pos := ⟨by decide, rfl, nofun, nofun, trivial, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
      | 1, hF =>
        simp only [nfnNodeDirty, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hF
        subst hF
        refine { hasType := ?_
                 level := fun ls => by
                   simp [VLevel.eval, nfnAuxDirty, nfnDirtyField, Lean.Nat.imax]
                 binders_indep := nofun
                 pos := ?_ }
        · show env₃.HasType 0 [VExpr.const `_nested.PFn_1 []]
            (.app (.lam (.sort (.succ .zero)) (.sort .zero)) (.const `_nested.PFn_1 []))
            (.sort (.succ .zero))
          exact VEnv.IsDefEq.appDF (B := .sort (.succ .zero))
            (VEnv.IsDefEq.lamDF (u := .succ (.succ .zero)) (by type_tac) (by type_tac))
            (by type_tac)
        · exact ⟨.sort .zero, trivial, _,
            VEnv.IsDefEq.beta (A := .sort (.succ .zero)) (B := .sort (.succ .zero))
              (by type_tac) (by type_tac)⟩
      | (_ + 2), hF => simp [nfnNodeDirty] at hF
    | 1, hT =>
      simp only [nfnAuxDirty] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .zero, fields := ?_, args_len := rfl,
               args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [pfnAuxMk, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, nfnAuxDirty, Lean.Nat.imax]
                binders_indep := fun r hr => by
                  cases hr; intro _ _ _ _ _ _ k B hB; simp at hB
                pos := ⟨by decide, rfl, nofun, nofun, trivial, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
      | 1, hF =>
        simp only [pfnAuxMk, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hF
        subst hF
        exact { hasType := by
                  refine VEnv.HasType.forallE (u := .succ .zero) (v := .succ .zero) ?_ ?_ <;>
                    type_tac
                level := fun ls => by simp [VLevel.eval, nfnAuxDirty, Lean.Nat.imax]
                binders_indep := fun r hr => by
                  cases hr; exact pfnAuxMk_bindersIndep 1 _ _ rfl rfl
                pos := ⟨by decide, rfl,
                        by rintro B hB; simp at hB; subst hB; trivial, nofun,
                        ⟨⟨trivial, _, by type_tac⟩, _, by type_tac⟩, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
      | (_ + 2), hF => simp [pfnAuxMk] at hF
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, nfnAuxDirty])


/-! ### …and the step goes through, `Built` and all -/

theorem nfnAuxDirty_canonicalOwn : nfnAuxDirty.CanonicalOwn nfnK := by
  intro j C hjC _
  rw [show nfnAuxDirty.ctorsAll = [((0 : Nat), nfnNodeDirty), (1, pfnAuxMk)] from rfl] at hjC
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hjC
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hjC
  · intro i F r hF hr
    match i, hF with
    | 0, hF => simp only [nfnNodeDirty] at hF; cases hF; cases hr; rfl
    | 1, hF => simp only [nfnNodeDirty] at hF; cases hF; exact absurd hr nofun
    | (_ + 2), hF => simp [nfnNodeDirty] at hF
  · exact (pfnOcc.member_Canonical nfnRestore nfnAuxDirty _
      (by rw [show (pfnOcc.member nfnAuxDirty.header nfnRestore).ctors = [pfnAuxMk] from by
                rw [nfnAuxDirty_header]; rfl]
          exact List.Mem.head _))

theorem nfnRestore_ownId_dirty : nfnRestore.OwnId nfnAuxDirty nfnK where
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [nfnAuxDirty] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [nfnAuxDirty] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [nfnAuxDirty] at hT
  recName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [nfnAuxDirty] at hT
  ctorName := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [nfnAuxDirty] at hT

include h in
theorem nfnAuxDirty_built :
    nfnAuxDirty.Built nfnRestore nfnK env₂ (fun _ => pfnOcc) where
  member := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; rw [nfnAuxDirty_header]; rfl
    · simp [nfnAuxDirty] at hT
  occurs := fun _ _ _ _ => pfnOcc_occurs h
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [nfnAuxDirty] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [nfnAuxDirty] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [nfnAuxDirty] at hT
  ctorName_inv := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT; exact absurd hK (by decide)
    · simp only [show pfnOcc.src.ctors = [pfnMk] from rfl, List.mem_cons,
        List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · simp [nfnAuxDirty] at hT
  own := nfnRestore_ownId_dirty
  nodup := by decide
  fields_noK := by
    rintro (_ | _ | j) T hT hK C₀ hC₀ k F₀ hF₀
    · cases hT; exact absurd hK (by decide)
    · simp only [show pfnOcc.src.ctors = [pfnMk] from rfl, List.mem_cons,
        List.not_mem_nil, or_false] at hC₀
      subst hC₀
      rcases k with _ | _ | k
      · cases hF₀
        exact VExpr.noConsts_instAll _ _ (by simp [VExpr.NoConsts, VExpr.instL, nfnK])
          (by simp [pfnOcc, VExpr.NoConsts, nfnK])
      · cases hF₀
        exact VExpr.noConsts_instAll _ _ (by simp [VExpr.NoConsts, VExpr.instL, nfnK])
          (by simp [pfnOcc, VExpr.NoConsts, nfnK])
      · exact absurd hF₀ nofun
    · simp [nfnAuxDirty] at hT

include h in
theorem nfnAuxDirty_admitted :
    ∃ env₃, env₂.addInductR nfnAuxDirty nfnK nfnRestore = some env₃ := by
  refine VEnv.addInductR_eq_some_iff.2 ⟨?_, ?_⟩ <;> rw [nfnAuxDirty_allNamesCR]
  · intro n hn; exact nfn_fresh h n hn
  · decide

include h in
/-- **The dirty block satisfies the constructive premise of the nested rule.**  Every
conjunct of `VEnv.AddNestedB` — hence of `VEnv.AddNested`, hence of `VEnv.AddNestedStep`,
which is what `VDecl.WF.inductNested` takes — holds. -/
theorem nfnAuxDirty_AddNestedB :
    ∃ env₃, VEnv.AddNestedB env₂ nfnAuxDirty nfnK nfnRestore (fun _ => pfnOcc) env₃ :=
  ⟨(nfnAuxDirty_admitted h).choose, nfnAuxDirty_WF,
    nfnAuxDirty_built h, (nfnAuxDirty_admitted h).choose_spec⟩

/-! ### …and the step it takes now **does** preserve `Ordered` at the constructor stage

This subsection used to end in `nfnAuxDirty_step_not_ordered` and
`nfnAuxDirty_obligationA_false`.  Both are gone, and what replaced them is below: with the
restoration substituted through the declared type (`VInductDecl'.ctorConstsCR`), obligation
**(A)** *holds* at the dirty block — through the general theorem
`VEnv.ctorConstsCR_wf_of_np_zero'`, which has no cleanliness hypothesis left to violate.

What survives of the counterexample is stated at the end: the dirt is still in
`VIndCtor.typeR`, hence still in `iotaCtxR`, hence still in the **ι-rules** the step emits,
and `VEnv.addIndRulesR` does *not* substitute.  So `nfnAuxDirty` has moved from refuting
`hctors` to refuting `hrules`. -/

theorem nfnAuxDirty_typeConstsC : nfnAuxDirty.typeConstsC nfnK = nfnAux.typeConstsC nfnK := rfl

/-- The staging environment of the dirty block is the staging environment of `nfnAux`: the two
blocks differ only inside a constructor, and `addIndTypes` reads `typeConsts`. -/
theorem nfnAuxDirty_addIndTypes {env₃ : VEnv} :
    env₂.addIndTypes nfnAuxDirty = some env₃ ↔ env₂.addIndTypes nfnAux = some env₃ := by
  rw [VEnv.addIndTypes, VEnv.addIndTypes, nfnAuxDirty_typeConsts]

/-- **The general type-entry substitution at the dirty block is still `nfnSubst`.**  It reads
only the member *names* and the (empty) parameter telescope, neither of which the extra field
touches. -/
theorem nfn_csubstTy_dirty : nfnRestore.csubstTy nfnAuxDirty nfnK = nfnSubst := by
  funext n
  show List.lookup n [(`_nested.PFn_1, nfnVal)] = _
  rw [List.lookup_cons]
  by_cases hq : n = `_nested.PFn_1
  · subst hq; rfl
  · rw [show (n == `_nested.PFn_1) = false from beq_eq_false_iff_ne.2 hq]
    exact (CSubst.one_of_ne hq).symm

theorem nfnAuxDirty_params_nil' : nfnAuxDirty.params = [] := rfl
theorem nfnAuxDirty_blockNames_nodup' : nfnAuxDirty.blockNames.Nodup := by decide

theorem nfnRestore_tyVal_levelWF_dirty (i : Nat) :
    (nfnRestore.tyVal nfnAuxDirty i).LevelWF nfnAuxDirty.uvars := by
  rw [VIndRestore.tyVal, nfnAuxDirty_params_nil', VExpr.mkLams_nil,
    show nfnRestore.tyArgs i = if i = 1 then [VExpr.const ``NFn []] else [] from rfl]
  split
  · exact ⟨nofun, nofun⟩
  · exact nofun

theorem nfnRestore_tyArgs_closed_dirty (i : Nat) :
    ∀ a ∈ nfnRestore.tyArgs i, a.ClosedN nfnAuxDirty.np := by
  rw [show nfnRestore.tyArgs i = if i = 1 then [VExpr.const ``NFn []] else [] from rfl]
  split
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha; trivial
  · intro a ha; simp at ha

include h in
/-- **Obligation (A) holds at the dirty block.**  The theorem the previous revision of this
file proved is `nfnAuxDirty_obligationA_false`; this is its negation's negation, and nothing
about the block changed — only `ctorConstsCR`. -/
theorem nfnAuxDirty_obligationA {env₃ env₄ : VEnv} (henv₂ : env₂.Ordered)
    (h₃ : env₂.addIndTypes nfnAuxDirty = some env₃)
    (h₄ : env₂.addConstList (nfnAuxDirty.typeConstsC nfnK) = some env₄) :
    ∀ c ∈ nfnAuxDirty.ctorConstsCR nfnRestore nfnK, VConstant.WF env₄ c.2 := by
  have h₃' : env₂.addIndTypes nfnAux = some env₃ := nfnAuxDirty_addIndTypes.1 h₃
  have h₄' : env₂.addConstList (nfnAux.typeConstsC nfnK) = some env₄ := by
    rwa [← nfnAuxDirty_typeConstsC]
  refine VEnv.ctorConstsCR_wf_of_np_zero' nfnAuxDirty_WF h₃
    (VInductDecl'.addIndTypes_ordered henv₂ nfnAuxDirty_WF h₃)
    (by rw [nfn_csubstTy_dirty]; exact nfnSubst_WF h henv₂ h₃' h₄')
    nfnAuxDirty_params_nil' nfnAuxDirty_blockNames_nodup' nfnRestore_ownId_dirty
    nfnRestore_tyVal_levelWF_dirty nfnRestore_tyArgs_closed_dirty
    (by rw [nfn_csubstTy_dirty]; rintro (_ | _ | i) <;> rfl)
    (by
      rw [nfn_csubstTy_dirty]
      intro i a ha
      rw [show nfnRestore.tyArgs i = if i = 1 then [VExpr.const ``NFn []] else [] from rfl] at ha
      split at ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        subst ha; exact nfnSubst_of_ne (by decide)
      · simp at ha)
    ((nfnAuxDirty_built h).canonical nfnAuxDirty_canonicalOwn)

end

/-- **The hypothesis the old counterexample violated.**  `VIndCtor.RestoreClean` is no longer a
hypothesis of anything: `VEnv.ctorConstsCR_wf_of_np_zero'` does without it.  The predicate and
this refutation of it stay, because they are what pins *which* positions the `substC` in
`ctorConstsCR` is there for. -/
theorem nfnNodeDirty_not_restoreClean : ¬ nfnNodeDirty.RestoreClean nfnSubst := by
  intro hc
  have h1 := hc.2 nfnDirtyField (by
    show nfnDirtyField ∈ [_, nfnDirtyField]
    exact List.mem_cons_of_mem _ List.mem_cons_self) rfl
  have h2 : nfnSubst `_nested.PFn_1 = none := h1.2
  simp [nfnSubst_aux] at h2

theorem nfnAuxDirty_params_nil : nfnAuxDirty.params = [] := rfl
theorem nfnAuxDirty_blockNames_nodup : nfnAuxDirty.blockNames.Nodup := by decide

/-! ### …and the refutation of `hrules` is gone too — the repair landed

The previous revision of this section ended: "`VEnv.addIndRulesR` folds `D.iotaRulesR R`
*unsubstituted*, and `iotaCtxR` splices `C.fieldTypesR` — the same telescope whose
non-recursive entry carries `_nested.PFn_1`.  So the first ι-rule the dirty step emits still has
a type mentioning a constant the environment does not hold, and obligation **(C)** of
`VEnv.addInductR_ordered'` is false at this block for exactly the reason (A) used to be."

That is no longer true.  `VEnv.addIndRulesR` now folds `VInductDecl'.iotaRulesRS D R K` — the
restored rules with `R.csubst D K` substituted through them — and at this block the substituted
rules are exactly the *ordinary* block's ι-rules substituted, `rfl`
(`nfnAuxDirty_iotaRulesRS_bridge`).  So the (C) bridge that
`VEnv.iotaRulesRS_wf_of_substC` asks for holds here, and what is left of the obligation is
`hsrc`/`hσ` — `VInductDecl'.iotaRules_WF` and a `CSubst.WF`, neither of which mentions the
restoration.

Two things about the cost, because the previous note mis-priced it.

* The note said the cost was that `VEnv.keysR_induct` is stated about the keys of
  `D.iotaRulesR R` and re-establishing the key "needs `Faithful` plus the freshness of the
  auxiliary names, not `rfl`".  **Both halves are wrong.**  What re-establishes the key is
  `VInductDecl'.key_iotaRuleR_substC` (`Theory/Inductive/NestedHead.lean`), and it needs
  neither `Faithful` nor freshness: it needs exactly `σ (R.recName …) = none` and
  `σ (R.ctorName C.name) = none`, isolated as `VIndRestore.KeysFree`.
* And `KeysFree` is **not** derivable from `Faithful` + `OwnId` + the two `addConstList`
  successes, so freshness could not have been the route: a companion member's own name is
  declared by *no* step (`typeConstsC` removes it), so nothing among those hypotheses forbids
  `R.recName (mkRecName I_j)` from being that name.  It is a syntactic side condition of
  `keysR_induct` alongside `KeysDistinct`, `decide`-able at a concrete block, and it is exactly
  what excludes G4's configuration at the substitution level:
  `InductiveDeclExamples.idRestore_not_keysFree` (`Theory/Inductive/NestedKeys.lean`) is the
  un-renamed recursor failing it.

What survives unchanged is that the dirt is still in `VIndCtor.typeR`, hence still in
`iotaCtxR`: `typeR` is the *canonical* restored form and `Faithful.ctor_agree` is stated against
it, so it was never the thing to change. -/

/-- **The general substitution at the dirty block is still `nfnSubstAll`** — the full one, with
the companion's constructor and recursor entries.  Compare `nfn_csubstTy_dirty`, the type-only
one that obligation (A) uses. -/
theorem nfn_csubst_dirty : nfnRestore.csubst nfnAuxDirty nfnK = nfnSubstAll := by
  funext n
  show List.lookup n [(`_nested.PFn_1, nfnVal), (`_nested.PFn_1.rec, nfnValRec),
    (`_nested.PFn_1.mk, nfnValMk)] = _
  by_cases h1 : n = `_nested.PFn_1
  · subst h1; rfl
  by_cases h2 : n = `_nested.PFn_1.mk
  · subst h2; rfl
  by_cases h3 : n = `_nested.PFn_1.rec
  · subst h3; rfl
  rw [List.lookup_cons, show (n == `_nested.PFn_1) = false from beq_eq_false_iff_ne.2 h1,
    List.lookup_cons, show (n == `_nested.PFn_1.rec) = false from beq_eq_false_iff_ne.2 h3,
    List.lookup_cons, show (n == `_nested.PFn_1.mk) = false from beq_eq_false_iff_ne.2 h2]
  show none = _
  rw [nfnSubstAll, if_neg h1, if_neg h2, if_neg h3]

/-- **Obligation (C)'s bridge, at the block that used to refute it.**  This is
`nfn_iotaRules_substC` (the clean witness's (C) bridge) at the *dirty* block, and it is `rfl`
for the same reason: `iotaCtx` and `iotaCtxR` differ only in positions the substitution
identifies. -/
theorem nfnAuxDirty_iotaRulesRS_bridge :
    nfnAuxDirty.iotaRules.map (·.substC nfnSubstAll)
      = nfnAuxDirty.iotaRulesRS nfnRestore nfnK := by
  rw [VInductDecl'.iotaRulesRS, nfn_csubst_dirty]; rfl

/-- `KeysFree` holds at the dirty block too — the extra field is in a constructor's telescope
and `KeysFree` reads only the restoration's names. -/
theorem nfnRestore_keysFree_dirty : nfnRestore.KeysFree nfnAuxDirty nfnK := by
  unfold VIndRestore.KeysFree; decide

/-! ### The change is bounded both ways

`docs/vacuity-ledger.md` §5: a repair that could not have changed anything is not a repair, and
one that changes what the implementation declares breaks faithfulness.  The substitution in
`VEnv.addIndRulesR` is measured on both sides.

* **It does nothing on a clean block.**  At *both* end-to-end witnesses the substituted rule
  list is the restored one on the nose, `rfl` — so `AddInductStagesR`
  (`Verify/Environment/InductR.lean`) and every `Faithful` equation are untouched, and
  `nfnAux_addInductR_ordered` (`Theory/Typing/ConstSubstNested.lean`) still discharges all
  three obligations with the *same* proofs.
* **It does something on the block that refuted (C).**  The first rule's `type` moves. -/

theorem nfnAux_iotaRulesRS_noop :
    nfnAux.iotaRulesRS nfnRestore nfnK = nfnAux.iotaRulesR nfnRestore := rfl

theorem ntreeAux_iotaRulesRS_noop :
    ntreeAux.iotaRulesRS ntreeRestore ntreeK = ntreeAux.iotaRulesR ntreeRestore := rfl

theorem nfnAuxDirty_iotaRulesRS_moves :
    (nfnAuxDirty.iotaRulesRS nfnRestore nfnK).head?.map (·.type)
      ≠ (nfnAuxDirty.iotaRulesR nfnRestore).head?.map (·.type) := by
  rw [VInductDecl'.iotaRulesRS, nfn_csubst_dirty]; decide

/-- **The dirt is still in the canonical restored telescope.**  `VIndField.typeR` copies a
non-recursive field's stored type verbatim, so `fieldTypesR` — and therefore `iotaCtxR` — still
names `_nested.PFn_1`.  What changed is that this is no longer what the step *registers*:
`iotaRulesRS` substitutes.  Kept because it pins which positions the substitution is for. -/
theorem nfnNodeDirty_fieldTypesR_dirty :
    ∃ A ∈ nfnNodeDirty.fieldTypesR nfnAuxDirty nfnRestore, ¬ A.NoCSubst nfnSubst := by
  refine ⟨nfnDirtyField.type, ?_, ?_⟩
  · rw [show nfnNodeDirty.fieldTypesR nfnAuxDirty nfnRestore
          = [nfnNodeDirty.fields[0]!.typeR nfnAuxDirty nfnRestore 0, nfnDirtyField.type] from rfl]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · intro hcl
    have h1 : nfnSubst `_nested.PFn_1 = none := hcl.2
    simp [nfnSubst_aux] at h1

/-- …and `VInductDecl'.iotaCtxR` splices exactly that telescope (through `atRecTele` and
`liftTele`, neither of which touches a constant), so the ι-rule's `type` still names
`_nested.PFn_1`.  The membership plumbing through the two telescope maps is not written out
here; the entry above is the whole content. -/
theorem nfnAuxDirty_iotaCtxR_eq (C : VIndCtor) :
    nfnAuxDirty.iotaCtxR nfnRestore C
      = nfnAuxDirty.atRecTele nfnAuxDirty.params ++ nfnAuxDirty.motivesR nfnRestore ++
          nfnAuxDirty.minorsR nfnRestore ++
          VExpr.liftTele (nfnAuxDirty.nm + nfnAuxDirty.nmin)
            (nfnAuxDirty.atRecTele (C.fieldTypesR nfnAuxDirty nfnRestore)) := rfl

/-! ## Part 6: obligations (B) and (C) need strictly more

`csubstTy`'s domain is inside `D.blockNames` (`VIndRestore.csubstTy_dom_blockNames`), and that
is what makes `VIndCtor.WF`'s `NoBlock` clauses do all the work in Part 4.  `csubst`'s domain
is **not**: it also holds the companion's constructor and recursor names.  So for (B) and (C)
the cleanliness condition has to be stated against `csubst` rather than against `NoBlock`, and
no clause of `VIndCtor.WF` supplies it. -/

theorem nfn_csubst_ctorName_some :
    nfnRestore.csubst nfnAux nfnK `_nested.PFn_1.mk = some nfnValMk := rfl

theorem nfn_csubst_recName_some :
    nfnRestore.csubst nfnAux nfnK `_nested.PFn_1.rec = some nfnValRec := rfl

/-- **`csubst`'s domain escapes `D.blockNames`.**  Compare
`VIndRestore.csubstTy_dom_blockNames`. -/
theorem nfn_csubst_dom_escapes_blockNames :
    `_nested.PFn_1.mk ∉ nfnAux.blockNames ∧ `_nested.PFn_1.rec ∉ nfnAux.blockNames := by
  constructor <;> decide

end InductiveDeclExamples
end Lean4Lean
