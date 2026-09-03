/-
# `RecTyped`: obligation (B) at `D.np > 0`, reduced to bundled typed data

`docs/handoff-flipprice.md` §6 lists three items still blocking the nested `AddInduct` flip, all
of one shape.  This file is item **(B)**: the *typed data* that
`VEnv.recConstsR_wf_of_blocksD` / `_of_entriesD` (`Theory/Inductive/NestedTele.lean` §T15.3a)
take as their `hmot` / `hmin` / `hbody`.

(C) already has this shape: `VIndRestore.IotaHargs` bundles the per-rule residual and
`VEnv.iotaRulesRS_wf_of_hargsD` reduces (C) to it.  **(B) had no counterpart** — measured, not
grepped: `RecTypedScan.lean` enumerates every declaration in the compiled environment whose type
mentions `VInductDecl'.recConstsR` together with `VConstant.WF`, and among the nineteen the only
general ones take either the entry defeqs themselves (`_of_blocks(D)`, `_of_entries(D)`), a
syntactic bridge (`_of_substC*`), or `hp : D.params = []` (`_of_np_zero*`).  Both parameterful
witnesses of (B) — `InductiveDeclExamples.ntreeAux_obligationB` and
`MRedex.MPWit.mpAuxB_obligationB`, arity 0 each — were built by hand at their block, entry by
entry, and neither goes through §T15's closures.

What is below is the missing composition, in three layers:

* §1 the `CSubst.WFD` variants of §T3's telescope inversion — needed because `σ.WF` is *refuted*
  between both staging pairs of a parameterised block (`ntree_csubst_WF₂_false`,
  `mp_csubst_WF₂_false`), so §T3/§T9/§T10 as stated are vacuous exactly where (B) is blocked;
* §2 the free items, at the ambient contexts `recConstsR_wf_of_entriesD` actually binds:
  the entry `OnCtx`s, `hOnp`, `hbv`, and the parameter-block σ-identity;
* §3 the bundles `MotiveHargs` / `MinorHargs` / `RecBodyHargs` and the reduction
  `VEnv.recConstsR_wf_of_recHargsD`;
* §4b/§4c `MinorCtorHargs`'s `hAs` conjunct **derived** (§T12.1's chain, composed) and therefore
  the bundle suppliable from `hcbody`/`hfun` alone — moved here from
  `Theory/Inductive/TeleCongr.lean`, which imported this file and so could not be consumed by it
  (`docs/handoff-telemove2.md`).

**This is a reduction, not a discharge.**  Its `hargs`-shaped hypotheses *are* the open
obligation; `VIndRestore.instAt_indep_of_tyArgs` (`NestedRules.lean:1509`) says no
restoration-independent argument produces them.  Graded the way `docs/handoff-flipprice.md` §5b
grades (C)'s `iotaRulesRS_wf_of_hargsD_of_barrier`.  §4 is the anti-vacuity record.
-/
import Lean4Lean.Theory.Inductive.NestedTele

namespace Lean4Lean

/-! ## §1 The `WFD` variants of §T3's inversion

§T1a's note applies verbatim: `Theory/Typing/ConstSubstNested.lean` §B refutes `σ.WF E₂ F₂ U`
at a parameterised nested block, so `VConstant.WF.substC_mkPi_inv` and
`VEnv.recTypeTele_substC_onCtx` are vacuous in `hσ` exactly where (B) is open.  These are the
same statements over `CSubst.WFD`, whose proofs are the originals with `IsType.substCD` in place
of `IsType.substC`.  `CSubst.WF.wfd` carries every `D.np = 0` instance over unchanged. -/

theorem VConstant.WF.substCD_mkPi_inv {E e : VEnv} {U : Nat} {σ : CSubst}
    {As : List VExpr} {B : VExpr} (he : e.Ordered) (hσ : σ.WFD E e U)
    (hs : VConstant.WF E ⟨U, VExpr.mkPi As B⟩) :
    OnCtx ((As.map (VExpr.substC · σ)).reverse) (e.IsType U) ∧
      e.IsType U ((As.map (VExpr.substC · σ)).reverse) (B.substC σ) := by
  have h : e.IsType U [] ((VExpr.mkPi As B).substC σ) := hs.substCD hσ
  rw [VExpr.substC_mkPi] at h
  simpa using VEnv.IsType.mkPi_inv he (Γ := []) trivial h

/-- §T3's `recTypeTele_substC_onCtx` over `WFD`. -/
theorem VEnv.recTypeTele_substCD_onCtx {E₂ e₂ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {j : Nat} {T : VIndType} (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars)
    (hg : D.types.getD j default = T)
    (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩) :
    OnCtx (((D.atRecTele D.params ++ D.motives ++ D.minors ++
        VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
        (VExpr.substC · σ)).reverse) (e₂.IsType D.recUvars) ∧
      e₂.IsType D.recUvars
        (((D.atRecTele D.params ++ D.motives ++ D.minors ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
          (VExpr.substC · σ)).reverse)
        ((VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
            (VExpr.bvars 0 T.indices.length))
          ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
            (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC σ) :=
  VConstant.WF.substCD_mkPi_inv he₂ hσ (by rw [← hg] at *; exact hs)

/-- §T9 item 1's entry `OnCtx` over `WFD`. -/
theorem VEnv.recTypeEntry_substCD_onCtx {E₂ e₂ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {As Bs : List VExpr} {B Cd : VExpr} {i : Nat}
    (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars)
    (hs : VConstant.WF E₂ ⟨D.recUvars, VExpr.mkPi As B⟩)
    (hi : (As.map (VExpr.substC · σ))[i]? = some (VExpr.mkPi Bs Cd)) :
    OnCtx (Bs.reverse ++ (((As.map (VExpr.substC · σ)).take i).reverse ++ ([] : List VExpr)))
        (e₂.IsType D.recUvars) ∧
      e₂.IsType D.recUvars
        (Bs.reverse ++ (((As.map (VExpr.substC · σ)).take i).reverse ++ ([] : List VExpr))) Cd :=
  OnCtx.mkPi_entry_inv he₂ (by simpa using (VConstant.WF.substCD_mkPi_inv he₂ hσ hs).1) hi

/-- §T10's `hpar` over `WFD` — the parameter telescope well-formed in the substituted
environment, from `D.WF env` and a fresh `σ`, with no `σ.WF`. -/
theorem VInductDecl'.onCtxParamsAtRec_substCD {env e : VEnv} {D : VInductDecl'} {σ : CSubst}
    (henv : env.Ordered) (hD : D.WF env) (hfresh : σ.FreshIn env)
    (hσ : σ.WFD env e D.recUvars) :
    OnCtx ((D.atRecTele D.params).reverse) (e.IsType D.recUvars) := by
  have hsrc := hD.onCtxParamsAtRec
  have h := VEnv.OnCtx.substCD hσ hsrc
  rwa [VEnv.OnCtx.substC_eq henv hfresh hsrc] at h

/-! ## §2 The free items, at the ambient contexts (B)'s closure actually binds

`VEnv.recConstsR_wf_of_entriesD` binds `hmot` over

    ((D.motives.map (substC · σ)).take t).reverse ++ ((D.atRecTele D.params).map (substC · σ)).reverse

and `hmin` over the analogous prefix one block further in.  §T5's `substC_motiveType_defeq'` and
§T6's `substC_minorType_defeq` are stated at a *general* ambient context, so they fit — but the
items §T9/§T10/§T16.2 call free (`hOn`, `hOnp`, `hbv`, the two σ-identities) are stated at shapes
that have to be *transported* to these ones.  That transport is this section, and it is the part
a prose composition hides. -/

section ListAux
variable {α : Type _}

/-- `++` for `List` is **left**-associative, so the four-block recursor telescope is
`((P ++ M) ++ Q) ++ I`.  Stating the two arithmetic facts against a *split hypothesis* rather
than a syntactic pattern makes them usable at all three of the splits below without fighting
associativity. -/
private theorem getElem?_map_of_split {f : α → α} {L P M R : List α} {i : Nat}
    (hL : L = P ++ M ++ R) (hi : i < M.length) :
    (L.map f)[P.length + i]? = (M.map f)[i]? := by
  subst hL
  simp only [List.map_append, List.append_assoc]
  rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simpa using hi)]
  simp

private theorem take_map_of_split {f : α → α} {L P M R : List α} {i : Nat}
    (hL : L = P ++ M ++ R) (hi : i ≤ M.length) :
    (L.map f).take (P.length + i) = P.map f ++ (M.map f).take i := by
  subst hL
  simp only [List.map_append, List.append_assoc]
  rw [show P.length = (List.map f P).length from by simp, List.take_append,
    List.take_of_length_le (by simp), List.take_append_of_le_length (by simpa using hi)]
  simp

private theorem take_map_prefix_of_split {f : α → α} {L P R : List α} (hL : L = P ++ R) :
    (L.map f).take P.length = P.map f := by
  subst hL
  rw [List.map_append, show P.length = (List.map f P).length from by simp,
    List.take_left]

end ListAux


/-- `hpcl`: the parameter telescope is closed.  `ClosedTele.of_onCtx` at `WF.onCtxParamsAtRec`,
recorded so that it is not counted as content. -/
theorem VInductDecl'.atRecTele_params_closedTele {env : VEnv} {D : VInductDecl'}
    (henv : env.Ordered) (hD : D.WF env) :
    VExpr.ClosedTele (D.atRecTele D.params) 0 :=
  VExpr.ClosedTele.of_onCtx (Γ := []) henv (by simpa using hD.onCtxParamsAtRec)

/-- **The entry itself, as a type at the prefix below it.**  `OnCtx.mkPi_entry_inv`'s first half
without the `mkPi` decomposition — what the *off-`K`* branches of §5 need, where the two sides of
an entry defeq are syntactically equal and the defeq is therefore a typing. -/
theorem OnCtx.entry_inv {e : VEnv} {U : Nat} {As Γ : List VExpr} {A : VExpr} {i : Nat}
    (hOn : OnCtx (As.reverse ++ Γ) (e.IsType U)) (hi : As[i]? = some A) :
    e.IsType U ((As.take i).reverse ++ Γ) A := by
  have hlt : i < As.length := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨L, Rr, hAs, hL⟩ : ∃ L Rr, As = L ++ A :: Rr ∧ L.length = i := by
    refine ⟨As.take i, As.drop (i+1), ?_, by simp [Nat.min_eq_left (Nat.le_of_lt hlt)]⟩
    have h1 : As.take (i+1) ++ As.drop (i+1) = As := List.take_append_drop _ _
    have h2 : As.take (i+1) = As.take i ++ [A] := by rw [List.take_add_one, hi]; rfl
    rw [h2] at h1
    simpa using h1.symm
  subst hAs
  rw [show (L ++ A :: Rr).take i = L from by rw [← hL]; simp]
  rw [List.reverse_append, List.reverse_cons] at hOn
  simp only [List.append_assoc, List.singleton_append] at hOn
  exact OnCtx.head_of_append (Δ := Rr.reverse) hOn

namespace VEnv

/-- The four-block recursor telescope, re-split for the motive entry (`++` is left-associative,
so the natural form is `((P ++ M) ++ Q) ++ I`). -/
private theorem recTele_split_mot (D : VInductDecl') (T : VIndType) :
    D.atRecTele D.params ++ D.motives ++ D.minors ++
        VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)
      = D.atRecTele D.params ++ D.motives ++
        (D.minors ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)) := by
  simp [List.append_assoc]

private theorem recTele_split_par (D : VInductDecl') (T : VIndType) :
    D.atRecTele D.params ++ D.motives ++ D.minors ++
        VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)
      = D.atRecTele D.params ++ (D.motives ++ D.minors ++
        VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)) := by
  simp [List.append_assoc]

/-- The motive entry's index data, substitution-free.  Extracted because the off-`K` branch (§5)
needs it without the `mkPi` decomposition. -/
private theorem motiveEntry_index (D : VInductDecl') (σ : CSubst) (T : VIndType) {t : Nat}
    (ht : t < D.nm) :
    ((D.atRecTele D.params ++ D.motives ++ D.minors ++
        VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
        (VExpr.substC · σ))[(D.atRecTele D.params).length + t]?
        = some ((D.motiveType t).substC σ)
      ∧ ((D.atRecTele D.params ++ D.motives ++ D.minors ++
        VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
        (VExpr.substC · σ)).take ((D.atRecTele D.params).length + t)
        = (D.atRecTele D.params).map (VExpr.substC · σ)
          ++ (D.motives.map (VExpr.substC · σ)).take t := by
  have hmot : t < D.motives.length := by simpa using ht
  refine ⟨?_, take_map_of_split (f := (VExpr.substC · σ))
    (P := D.atRecTele D.params) (M := D.motives)
    (R := D.minors ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
    (recTele_split_mot D T) (Nat.le_of_lt hmot)⟩
  rw [getElem?_map_of_split (f := (VExpr.substC · σ))
      (P := D.atRecTele D.params) (M := D.motives)
      (R := D.minors ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
      (recTele_split_mot D T) hmot,
    List.getElem?_map, VInductDecl'.motives, List.getElem?_map, List.getElem?_range ht]
  rfl

/-- **The motive entry's `OnCtx`, at the ambient context (B)'s closure binds.**  §T9 item 1
transported, over `WFD`: `hsrc` + `hσ` and nothing else. -/
theorem motiveEntry_substCD_onCtx {E₂ e₂ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {j t : Nat} {T Tt : VIndType} (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars)
    (hg : D.types.getD j default = T)
    (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩)
    (hgt : D.types.getD t default = Tt) (ht : t < D.nm) :
    OnCtx ((VExpr.liftTele t ((D.atRecTele Tt.indices).map (VExpr.substC · σ)) 0).reverse
      ++ (((D.motives.map (VExpr.substC · σ)).take t).reverse
          ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
      (e₂.IsType D.recUvars) := by
  have hs' : VConstant.WF E₂ ⟨D.recUvars, VExpr.mkPi (D.atRecTele D.params ++ D.motives ++
      D.minors ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
      (VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
          (VExpr.bvars 0 T.indices.length))
        ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
          (VExpr.bvars 1 T.indices.length ++ [.bvar 0])))⟩ := by
    rw [← hg]; exact hs
  have hent : (D.motiveType t).substC σ
      = VExpr.mkPi (VExpr.liftTele t ((D.atRecTele Tt.indices).map (VExpr.substC · σ)) 0)
        ((VExpr.forallE (D.tyApp' t (Tt.indices.length + t) (VExpr.bvars 0 Tt.indices.length))
          (.sort D.elimLvl)).substC σ) := by
    rw [VInductDecl'.motiveType, hgt, VExpr.substC_mkPi,
      VExpr.map_substC_liftTele (σ := σ) hσ.closed]
  have hmot : t < D.motives.length := by simpa using ht
  have hi := getElem?_map_of_split (f := (VExpr.substC · σ))
    (P := D.atRecTele D.params) (M := D.motives)
    (R := D.minors ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
    (recTele_split_mot D T) hmot
  have htk := take_map_of_split (f := (VExpr.substC · σ))
    (P := D.atRecTele D.params) (M := D.motives)
    (R := D.minors ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
    (recTele_split_mot D T) (Nat.le_of_lt hmot)
  have hentry : ((D.atRecTele D.params ++ D.motives ++ D.minors ++
        VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
        (VExpr.substC · σ))[(D.atRecTele D.params).length + t]?
      = some (VExpr.mkPi (VExpr.liftTele t ((D.atRecTele Tt.indices).map (VExpr.substC · σ)) 0)
        ((VExpr.forallE (D.tyApp' t (Tt.indices.length + t) (VExpr.bvars 0 Tt.indices.length))
          (.sort D.elimLvl)).substC σ)) := by
    rw [hi, List.getElem?_map, VInductDecl'.motives, List.getElem?_map,
      List.getElem?_range ht, ← hent]
    rfl
  have h := recTypeEntry_substCD_onCtx (D := D)
    (i := (D.atRecTele D.params).length + t) he₂ hσ hs' hentry
  rw [htk] at h
  simpa [List.reverse_append] using h.1

/-- **The minor entry's `OnCtx`, at the ambient context (B)'s closure binds.** -/
theorem minorEntry_substCD_onCtx {E₂ e₂ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {j q t : Nat} {T : VIndType} {C : VIndCtor} (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars)
    (hg : D.types.getD j default = T)
    (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩)
    (hq : D.ctorsAll[q]? = some (t, C)) (hqlt : q < D.minors.length) :
    OnCtx ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)) 0
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
      ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
          ++ ((D.motives.map (VExpr.substC · σ)).reverse
              ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)))
      (e₂.IsType D.recUvars) := by
  have hs' : VConstant.WF E₂ ⟨D.recUvars, VExpr.mkPi (D.atRecTele D.params ++ D.motives ++
      D.minors ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
      (VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
          (VExpr.bvars 0 T.indices.length))
        ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
          (VExpr.bvars 1 T.indices.length ++ [.bvar 0])))⟩ := by
    rw [← hg]; exact hs
  have hent : (D.minorType q t C).substC σ
      = VExpr.mkPi (VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)) 0
          ++ (D.ihTypes q C).map (VExpr.substC · σ))
        (((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
          ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
              C.fields.length (D.atRec a))
            ++ [D.ctorApp' C ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
                  (VExpr.bvars (D.ihTypes q C).length C.fields.length)])).substC σ) := by
    rw [VInductDecl'.minorType, VExpr.substC_mkPi, List.map_append,
      VExpr.map_substC_liftTele (σ := σ) hσ.closed]
  have hi := getElem?_map_of_split (f := (VExpr.substC · σ))
    (P := D.atRecTele D.params ++ D.motives) (M := D.minors)
    (R := VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)) rfl hqlt
  have htk := take_map_of_split (f := (VExpr.substC · σ))
    (P := D.atRecTele D.params ++ D.motives) (M := D.minors)
    (R := VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)) rfl (Nat.le_of_lt hqlt)
  have hentry : ((D.atRecTele D.params ++ D.motives ++ D.minors ++
        VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
        (VExpr.substC · σ))[(D.atRecTele D.params ++ D.motives).length + q]?
      = some (VExpr.mkPi (VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)) 0
          ++ (D.ihTypes q C).map (VExpr.substC · σ))
        (((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
          ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
              C.fields.length (D.atRec a))
            ++ [D.ctorApp' C ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
                  (VExpr.bvars (D.ihTypes q C).length C.fields.length)])).substC σ)) := by
    rw [hi, List.getElem?_map, VInductDecl'.minors_getElem?, hq, ← hent]
    rfl
  have h := recTypeEntry_substCD_onCtx (D := D)
    (i := (D.atRecTele D.params ++ D.motives).length + q) he₂ hσ hs' hentry
  rw [htk] at h
  simpa [List.reverse_append, List.append_assoc] using h.1

/-- **The minor entry's *body* typing**, same derivation, `.2` instead of `.1`.  Off `K` the two
sides of the minor conclusion are syntactically equal (`OwnId.ctorAppR_eq`), so this typing *is*
the body defeq there. -/
theorem minorEntry_substCD_body {E₂ e₂ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {j q t : Nat} {T : VIndType} {C : VIndCtor} (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars)
    (hg : D.types.getD j default = T)
    (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩)
    (hq : D.ctorsAll[q]? = some (t, C)) (hqlt : q < D.minors.length) :
    e₂.IsType D.recUvars ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)) 0
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
      ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
          ++ ((D.motives.map (VExpr.substC · σ)).reverse
              ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)))
      (((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a))
          ++ [D.ctorApp' C ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
                (VExpr.bvars (D.ihTypes q C).length C.fields.length)])).substC σ) := by
  have hs' : VConstant.WF E₂ ⟨D.recUvars, VExpr.mkPi (D.atRecTele D.params ++ D.motives ++
      D.minors ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
      (VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
          (VExpr.bvars 0 T.indices.length))
        ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
          (VExpr.bvars 1 T.indices.length ++ [.bvar 0])))⟩ := by
    rw [← hg]; exact hs
  have hent : (D.minorType q t C).substC σ
      = VExpr.mkPi (VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)) 0
          ++ (D.ihTypes q C).map (VExpr.substC · σ))
        (((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
          ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
              C.fields.length (D.atRec a))
            ++ [D.ctorApp' C ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
                  (VExpr.bvars (D.ihTypes q C).length C.fields.length)])).substC σ) := by
    rw [VInductDecl'.minorType, VExpr.substC_mkPi, List.map_append,
      VExpr.map_substC_liftTele (σ := σ) hσ.closed]
  have hi := getElem?_map_of_split (f := (VExpr.substC · σ))
    (P := D.atRecTele D.params ++ D.motives) (M := D.minors)
    (R := VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)) rfl hqlt
  have htk := take_map_of_split (f := (VExpr.substC · σ))
    (P := D.atRecTele D.params ++ D.motives) (M := D.minors)
    (R := VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)) rfl (Nat.le_of_lt hqlt)
  have hentry : ((D.atRecTele D.params ++ D.motives ++ D.minors ++
        VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
        (VExpr.substC · σ))[(D.atRecTele D.params ++ D.motives).length + q]?
      = some (VExpr.mkPi (VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)) 0
          ++ (D.ihTypes q C).map (VExpr.substC · σ))
        (((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
          ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
              C.fields.length (D.atRec a))
            ++ [D.ctorApp' C ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
                  (VExpr.bvars (D.ihTypes q C).length C.fields.length)])).substC σ)) := by
    rw [hi, List.getElem?_map, VInductDecl'.minors_getElem?, hq, ← hent]
    rfl
  have h := recTypeEntry_substCD_onCtx (D := D)
    (i := (D.atRecTele D.params ++ D.motives).length + q) he₂ hσ hs' hentry
  rw [htk] at h
  simpa [List.reverse_append, List.append_assoc] using h.2

/-- **`hpar` from `hsrc` and `hσ` alone** — the parameter block is the outermost segment of the
substituted recursor telescope, and §T16.2's σ-identity identifies it with the unsubstituted one.
This is what removes the *second* `CSubst.WFD` that `onCtxParamsAtRec_substCD` would need (one at
`(env, e₂)` on top of the closure's own at `(E₂, e₂)`). -/
theorem recPar_substCD_onCtx {env E₂ e₂ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {j : Nat} {T : VIndType} (henv : env.Ordered) (hD : D.WF env) (hfresh : σ.FreshIn env)
    (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars)
    (hg : D.types.getD j default = T)
    (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩) :
    OnCtx ((D.atRecTele D.params).reverse) (e₂.IsType D.recUvars) := by
  have h := (recTypeTele_substCD_onCtx he₂ hσ hg hs).1
  have h2 := OnCtx.take_of_reverse (P := e₂.IsType D.recUvars) (Γ := [])
    (D.atRecTele D.params).length (by rw [List.append_nil]; exact h)
  rw [take_map_prefix_of_split (f := (VExpr.substC · σ)) (P := D.atRecTele D.params)
      (R := D.motives ++ D.minors ++ VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
      (recTele_split_par D T),
    VInductDecl'.atRecTele_params_substC_eq henv hD hfresh] at h2
  simpa using h2

end VEnv

/-! ### The off-`K` branch: at a type the restoration does **not** touch, the entry is reflexive

`VIndRestore.OwnId.tyAppR'_eq` / `.ctorAppR_eq` say the restored heads collapse to the source
ones off `K`.  So for a `T.name ∉ K` entry the two sides of the defeq are *syntactically equal*
and the entry defeq is a **typing**, which `OnCtx.entry_inv` / `OnCtx.mkPi_entry_inv` already
supply from `hsrc` + `hσ`.

**This is the repair of a vacuity in the first version of §4's closure.**  That version demanded
`hK : ∀ t T, D.types[t]? = some T → T.name ∈ K` — and at the canonical parameterised nested block
that is **false**: `ntreeK = [`_nested.List_1]` while `ntreeAux.types` also contains the block's
own head `NTree`.  With that hypothesis the closure's premises were jointly unsatisfiable at every
real nested block, and the axiom line said nothing about it. -/

/-- **The motive entry off `K`**: reflexive, hence free. -/
theorem motiveEntry_defeq_off_K {E₂ e₂ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Lean.Name} {σ : CSubst} {j t : Nat} {T Tt : VIndType}
    (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars) (hown : R.OwnId D K)
    (hg : D.types.getD j default = T)
    (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩)
    (hTt : D.types[t]? = some Tt) (hKt : Tt.name ∉ K) (ht : t < D.nm) :
    ∃ u, e₂.IsDefEq D.recUvars
      (((D.motives.map (VExpr.substC · σ)).take t).reverse
        ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)
      ((D.motiveType t).substC σ) ((D.motiveTypeR R t).substC σ) (.sort u) := by
  have hgt : D.types.getD t default = Tt := VInductDecl'.getD_types hTt
  have heq : D.motiveTypeR R t = D.motiveType t := by
    rw [VInductDecl'.motiveTypeR, VInductDecl'.motiveType, hgt,
      hown.tyAppR'_eq hTt hKt]
  rw [heq]
  obtain ⟨hidx, htk⟩ := VEnv.motiveEntry_index D σ T ht
  have h := OnCtx.entry_inv (Γ := []) (e := e₂) (U := D.recUvars)
    (by rw [List.append_nil]; exact (VEnv.recTypeTele_substCD_onCtx he₂ hσ hg hs).1) hidx
  rw [htk] at h
  obtain ⟨u, hu⟩ : e₂.IsType D.recUvars
      (((D.motives.map (VExpr.substC · σ)).take t).reverse
        ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)
      ((D.motiveType t).substC σ) := by
    simpa [List.reverse_append] using h
  exact ⟨u, hu⟩

/-- **The recursor body off `K`**: reflexive, hence free. -/
theorem recBody_defeq_off_K {E₂ e₂ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Lean.Name} {σ : CSubst} {j : Nat} {T : VIndType}
    (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars) (hown : R.OwnId D K)
    (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩)
    (hT : D.types[j]? = some T) (hK : T.name ∉ K) :
    ∃ v : VLevel, e₂.IsDefEq D.recUvars
      (((D.atRecTele D.params ++ D.motives ++ D.minors ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
          (VExpr.substC · σ)).reverse)
      ((VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
            (VExpr.bvars 0 T.indices.length))
          ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
            (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC σ)
      ((VExpr.forallE (D.tyAppR' R j (T.indices.length + D.nmin + D.nm)
            (VExpr.bvars 0 T.indices.length))
          ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
            (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC σ) (.sort v) := by
  rw [hown.tyAppR'_eq hT hK]
  obtain ⟨v, hv⟩ := (VEnv.recTypeTele_substCD_onCtx he₂ hσ (VInductDecl'.getD_types hT) hs).2
  exact ⟨v, hv⟩


/-! ## §3 The producers: each entry family of (B)'s closure, from `hargs`-shaped data

`VEnv.recConstsR_wf_of_entriesD` takes three families — `hmot`, `hmin`, `hbody`.  Each is
produced below from the §8.9 data for **one** head (the type head for `hmot`/`hbody`, the
constructor head for `hmin`) plus, for the minor block, `hfld`.  Every other input is discharged
from §2 or from §T9/§T10/§T16.2.

`hbody`/`hcbody` are taken at the **params-only** context and weakened by
`VIndRestore.hbody_weak` (§T11's factorisation: the subject is closed at `D.np`, so one typing
serves every entry's context).  That is why the data enters *once per `Faithful` clause* rather
than once per entry. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst}
variable {env E₂ e₂ : VEnv}

/-- **`hmot` for one motive entry, from the type head's `hargs`.**  The ambient context is
literally the one `VEnv.recConstsR_wf_of_entriesD` binds. -/
theorem motiveEntry_defeq_of_hargs
    (henv : env.Ordered) (hD : D.WF env) (hfresh : σ.FreshIn env)
    (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars) (hσc : σ.Closed)
    (hfr : R.SubstFree D σ) (hat : R.SubstAt D K σ) (helim : D.elimLvl.WF D.recUvars)
    {j t : Nat} {T Tt : VIndType}
    (hg : D.types.getD j default = T) (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩)
    (hTt : D.types[t]? = some Tt) (hKt : Tt.name ∈ K) (ht : t < D.nm)
    (hcl : ∀ a ∈ R.tyArgs t, a.ClosedN D.np)
    {As : List VExpr} {B B' : VExpr} {w : VLevel}
    (hbody : e₂.HasType D.recUvars ((D.atRecTele D.params).reverse)
      (D.atRec (R.tyBody D t)) B)
    (hpi : VExpr.instAll B (VExpr.bvars (Tt.indices.length + t) D.np) = VExpr.mkPi As B')
    (hAs : e₂.HasArgs D.recUvars
      ((VExpr.liftTele t ((D.atRecTele Tt.indices).map (VExpr.substC · σ)) 0).reverse
        ++ (((D.motives.map (VExpr.substC · σ)).take t).reverse
            ++ (D.atRecTele D.params).reverse))
      As (VExpr.bvars 0 Tt.indices.length))
    (hsort : VExpr.instAll B' (VExpr.bvars 0 Tt.indices.length) = .sort w) :
    ∃ u, e₂.IsDefEq D.recUvars
      (((D.motives.map (VExpr.substC · σ)).take t).reverse
        ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse)
      ((D.motiveType t).substC σ) ((D.motiveTypeR R t).substC σ) (.sort u) := by
  have hgt : D.types.getD t default = Tt := VInductDecl'.getD_types hTt
  have hpcl : VExpr.ClosedTele (D.atRecTele D.params) 0 :=
    VInductDecl'.atRecTele_params_closedTele henv hD
  have hpar : OnCtx ((D.atRecTele D.params).reverse) (e₂.IsType D.recUvars) :=
    VEnv.recPar_substCD_onCtx henv hD hfresh he₂ hσ hg hs
  have hσp := VInductDecl'.atRecTele_params_substC_eq (D := D) (σ := σ) henv hD hfresh
  have hOn := VEnv.motiveEntry_substCD_onCtx he₂ hσ hg hs hgt ht
  rw [hσp] at hOn ⊢
  have hOnp := VEnv.onCtx_params_append he₂ hpcl hpar hOn
  have hbv := hasArgs_params_bvars_motiveCtx' (e := e₂) (U := D.recUvars) (D := D) (T := Tt)
    (M := (D.motives.map (VExpr.substC · σ)).take t) (Γ₀ := []) (σ := σ) hpcl
    (by rw [List.length_take, Nat.min_eq_left (by simpa using Nat.le_of_lt ht)])
  rw [List.append_nil] at hbv
  exact substC_motiveType_defeq' hσc hfr hat hcl he₂ helim hTt hKt hgt hOn hOnp hbv
    (hbody_weak he₂ hpcl hbody) hpi hAs hsort

/-- **`hbody` for one recursor, from the type head's `hargs`.**  `substC_recBody_defeq` at the
whole substituted telescope; the conclusion is reflexive (§T8), so the only datum is the major
premise's head defeq. -/
theorem recBody_defeq_of_hargs (hfr : R.SubstFree D σ) {j : Nat} {T : VIndType} {w : VLevel}
    (hhead : e₂.IsDefEq D.recUvars
      (((D.atRecTele D.params ++ D.motives ++ D.minors ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
          (VExpr.substC · σ)).reverse)
      ((D.tyApp' j (T.indices.length + D.nmin + D.nm)
        (VExpr.bvars 0 T.indices.length)).substC σ)
      (D.tyAppR' R j (T.indices.length + D.nmin + D.nm) (VExpr.bvars 0 T.indices.length))
      (.sort w))
    (hconcl : e₂.HasType D.recUvars
      (((D.tyApp' j (T.indices.length + D.nmin + D.nm)
          (VExpr.bvars 0 T.indices.length)).substC σ)
        :: ((D.atRecTele D.params ++ D.motives ++ D.minors ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
          (VExpr.substC · σ)).reverse)
      ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
        (VExpr.bvars 1 T.indices.length ++ [.bvar 0])) (.sort D.elimLvl)) :
    ∃ v : VLevel, e₂.IsDefEq D.recUvars
      (((D.atRecTele D.params ++ D.motives ++ D.minors ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
          (VExpr.substC · σ)).reverse)
      ((VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
            (VExpr.bvars 0 T.indices.length))
          ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
            (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC σ)
      ((VExpr.forallE (D.tyAppR' R j (T.indices.length + D.nmin + D.nm)
            (VExpr.bvars 0 T.indices.length))
          ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
            (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC σ) (.sort v) :=
  ⟨_, substC_recBody_defeq hfr hhead hconcl⟩

/-- **`hmin` for one minor entry, from the constructor head's `hargs` plus `hfld`.**

The ambient context is the one `VEnv.recConstsR_wf_of_entriesD` binds; `hOn`/`hOnp`/`hbv` are
discharged from §2, `hpi`'s `B'` is a `tyAppR'` by §T10's `instAt_ctor_hpi` at the call site, and
`hfld` is §T15.7's residual (which §T16.1 turns into the *same* head datum, so it is not a fourth
kind of obligation). -/
theorem minorEntry_defeq_of_hargs
    (henv : env.Ordered) (hD : D.WF env) (hfresh : σ.FreshIn env)
    (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars) (hσc : σ.Closed)
    (hfr : R.SubstFree D σ) (hat : R.SubstAt D K σ)
    {j q t : Nat} {T Tt : VIndType} {C : VIndCtor}
    (hg : D.types.getD j default = T) (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩)
    (hTt : D.types[t]? = some Tt) (hKt : Tt.name ∈ K) (hC : C ∈ Tt.ctors)
    (hq : D.ctorsAll[q]? = some (t, C)) (hqlt : q < D.minors.length)
    (hcl : ∀ a ∈ R.tyArgs t, a.ClosedN D.np)
    {As : List VExpr} {B B' : VExpr}
    (hfld : e₂.TeleDefEq D.recUvars
      (((D.minors.map (VExpr.substC · σ)).take q).reverse
        ++ ((D.motives.map (VExpr.substC · σ)).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
      (VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)))
      (VExpr.liftTele (D.nm + q) ((D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ))))
    (hcbody : e₂.HasType D.recUvars ((D.atRecTele D.params).reverse)
      (D.atRec (R.ctorBody D t C)) B)
    (hpi : VExpr.instAll B
      (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)
        = VExpr.mkPi As B')
    (hAs : e₂.HasArgs D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      As (VExpr.bvars (D.ihTypes q C).length C.fields.length))
    (hfun : e₂.HasType D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      ((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a)).map (VExpr.substC · σ)))
      (.forallE (VExpr.instAll B' (VExpr.bvars (D.ihTypes q C).length C.fields.length))
        (.sort D.elimLvl))) :
    ∃ u, e₂.IsDefEq D.recUvars
      (((D.minors.map (VExpr.substC · σ)).take q).reverse
        ++ ((D.motives.map (VExpr.substC · σ)).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
      ((D.minorType q t C).substC σ) ((D.minorTypeR R q t C).substC σ) (.sort u) := by
  have hpcl : VExpr.ClosedTele (D.atRecTele D.params) 0 :=
    VInductDecl'.atRecTele_params_closedTele henv hD
  have hpar : OnCtx ((D.atRecTele D.params).reverse) (e₂.IsType D.recUvars) :=
    VEnv.recPar_substCD_onCtx henv hD hfresh he₂ hσ hg hs
  have hσp := VInductDecl'.atRecTele_params_substC_eq (D := D) (σ := σ) henv hD hfresh
  have hOn0 := VEnv.minorEntry_substCD_onCtx he₂ hσ hg hs hq hqlt
  rw [hσp] at hOn0 hfld ⊢
  have hM : (((D.minors.map (VExpr.substC · σ)).take q).reverse
      ++ (D.motives.map (VExpr.substC · σ)).reverse).length = D.nm + q := by
    rw [List.length_append, List.length_reverse, List.length_reverse, List.length_take,
      List.length_map, List.length_map, Nat.min_eq_left (Nat.le_of_lt hqlt)]
    simp [Nat.add_comm]
  have hOn : OnCtx ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
      ++ ((((D.minors.map (VExpr.substC · σ)).take q).reverse
          ++ (D.motives.map (VExpr.substC · σ)).reverse)
        ++ ((D.atRecTele D.params).reverse ++ ([] : List VExpr))))
      (e₂.IsType D.recUvars) := by
    simpa [List.append_assoc] using hOn0
  have key := substC_minorType_defeq (R := R) (D := D) (K := K) (σ := σ) (e := e₂)
    (U := D.recUvars) (t := t) (q := q) (T := Tt) (C := C)
    (M := ((D.minors.map (VExpr.substC · σ)).take q).reverse
      ++ (D.motives.map (VExpr.substC · σ)).reverse) (Γ₀ := [])
    hσc hat hfr hcl he₂ hTt hKt hC hpcl hM
    (by simpa [List.append_assoc] using hfld)
    hOn
    (VEnv.onCtx_params_append he₂ hpcl hpar hOn)
    (hbody_weak he₂ hpcl hcbody) hpi
    (by simpa [List.append_assoc] using hAs)
    (by simpa [List.append_assoc] using hfun)
  simpa [List.append_assoc] using key

/-- **The minor entry off `K`, from `hfld` alone.**  `OwnId.ctorAppR_eq` makes the minor
conclusion reflexive, so the body defeq is the entry's own typing (`minorEntry_substCD_body`) and
the *only* residual is the field-telescope defeq.  Note this is **not** vacuous work: the field
telescope moves even off `K` — `C.fieldTypesR` rewrites a companion occurrence inside a
constructor of the block's **own** head, which is exactly the `NTree.node` case. -/
theorem minorEntry_defeq_off_K
    (he₂ : e₂.Ordered) (hσ : σ.WFD E₂ e₂ D.recUvars) (hσc : σ.Closed) (hown : R.OwnId D K)
    {j q t : Nat} {T Tt : VIndType} {C : VIndCtor}
    (hg : D.types.getD j default = T) (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩)
    (hTt : D.types[t]? = some Tt) (hKt : Tt.name ∉ K) (hC : C ∈ Tt.ctors)
    (hq : D.ctorsAll[q]? = some (t, C)) (hqlt : q < D.minors.length)
    (hfld : e₂.TeleDefEq D.recUvars
      (((D.minors.map (VExpr.substC · σ)).take q).reverse
        ++ ((D.motives.map (VExpr.substC · σ)).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
      (VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)))
      (VExpr.liftTele (D.nm + q) ((D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ)))) :
    ∃ u, e₂.IsDefEq D.recUvars
      (((D.minors.map (VExpr.substC · σ)).take q).reverse
        ++ ((D.motives.map (VExpr.substC · σ)).reverse
            ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
      ((D.minorType q t C).substC σ) ((D.minorTypeR R q t C).substC σ) (.sort u) := by
  obtain ⟨w, hw⟩ := VEnv.minorEntry_substCD_body he₂ hσ hg hs hq hqlt
  refine substC_minorType_defeq' hσc hfld
    (VEnv.minorEntry_substCD_onCtx he₂ hσ hg hs hq hqlt) (w := w) ?_
  rw [hown.ctorAppR_eq hTt hKt hC]
  exact hw

end
end VIndRestore

/-! ## §4 The bundles, and obligation (B) at `D.np > 0` from them alone

The (B) counterpart of `VIndRestore.IotaHargs` / `VEnv.iotaRulesRS_wf_of_hargsD`.  Four bundles:
`MotiveHargs` and `RecBodyHargs` carry the **type** head's data, `MinorCtorHargs` the
**constructor** head's, and `MinorFldDefEq` is §T15.7's `hfld`.  That is §T11's count — the data
enters once per `Faithful` clause — made checkable.

The `Hargs` bundles are demanded only at a type **in `K`** (§5's off-`K` branch makes the others
reflexive); `MinorFldDefEq` is demanded everywhere, because the restored field telescope moves at
a constructor of the block's own head too. -/

namespace VIndRestore
section
variable (R : VIndRestore) (D : VInductDecl') (σ : CSubst) (e : VEnv)

/-- Motive entry `t`'s residual: §8.9's `hbody`/`hpi`/`hAs`/`hsort` for the type head, with
`hbody` at the params-only context (`hbody_weak` moves it to every entry's). -/
def MotiveHargs (t : Nat) (T : VIndType) : Prop :=
  ∃ (As : List VExpr) (B B' : VExpr) (w : VLevel),
    e.HasType D.recUvars ((D.atRecTele D.params).reverse) (D.atRec (R.tyBody D t)) B ∧
    VExpr.instAll B (VExpr.bvars (T.indices.length + t) D.np) = VExpr.mkPi As B' ∧
    e.HasArgs D.recUvars
      ((VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
        ++ (((D.motives.map (VExpr.substC · σ)).take t).reverse
            ++ (D.atRecTele D.params).reverse))
      As (VExpr.bvars 0 T.indices.length) ∧
    VExpr.instAll B' (VExpr.bvars 0 T.indices.length) = .sort w

/-- §T15.7's `hfld` at minor entry `q`, at the ambient context (B)'s closure binds. -/
def MinorFldDefEq (q : Nat) (C : VIndCtor) : Prop :=
  e.TeleDefEq D.recUvars
    (((D.minors.map (VExpr.substC · σ)).take q).reverse
      ++ ((D.motives.map (VExpr.substC · σ)).reverse
          ++ ((D.atRecTele D.params).map (VExpr.substC · σ)).reverse))
    (VExpr.liftTele (D.nm + q)
      ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)))
    (VExpr.liftTele (D.nm + q) ((D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ)))

/-- Minor entry `q`'s *constructor-head* residual: `hcbody`/`hpi`/`hAs`/`hfun`. -/
def MinorCtorHargs (q t : Nat) (C : VIndCtor) : Prop :=
  ∃ (As : List VExpr) (B B' : VExpr),
    e.HasType D.recUvars ((D.atRecTele D.params).reverse)
      (D.atRec (R.ctorBody D t C)) B ∧
    VExpr.instAll B
      (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)
        = VExpr.mkPi As B' ∧
    e.HasArgs D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      As (VExpr.bvars (D.ihTypes q C).length C.fields.length) ∧
    e.HasType D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      ((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a)).map (VExpr.substC · σ)))
      (.forallE (VExpr.instAll B' (VExpr.bvars (D.ihTypes q C).length C.fields.length))
        (.sort D.elimLvl))

/-- Recursor `j`'s body residual: the major premise's head defeq over §T8's reflexive
conclusion. -/
def RecBodyHargs (j : Nat) (T : VIndType) : Prop :=
  ∃ w : VLevel,
    e.IsDefEq D.recUvars
      (((D.atRecTele D.params ++ D.motives ++ D.minors ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
          (VExpr.substC · σ)).reverse)
      ((D.tyApp' j (T.indices.length + D.nmin + D.nm)
        (VExpr.bvars 0 T.indices.length)).substC σ)
      (D.tyAppR' R j (T.indices.length + D.nmin + D.nm) (VExpr.bvars 0 T.indices.length))
      (.sort w) ∧
    e.HasType D.recUvars
      (((D.tyApp' j (T.indices.length + D.nmin + D.nm)
          (VExpr.bvars 0 T.indices.length)).substC σ)
        :: ((D.atRecTele D.params ++ D.motives ++ D.minors ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
          (VExpr.substC · σ)).reverse)
      ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
        (VExpr.bvars 1 T.indices.length ++ [.bvar 0])) (.sort D.elimLvl)

end
end VIndRestore

/-! ## §4b `MinorCtorHargs`'s `hAs` is a THEOREM — §T12.1's chain, composed

`NestedTele.lean` §T12.1 sets out the de Bruijn arithmetic and §T13 closes its two side
conditions, and both sections say in as many words that the composition is not performed there.
This is it.  It was proved in `Theory/Inductive/TeleCongr.lean`, **downstream** of this file, which
is why nothing here could consume it; the move is `docs/handoff-telemove2.md` §2.

Reading the chain off §T12.1, with `nf := C.fields.length`, `nr := (D.ihTypes q C).length`,
`off := D.nm + q` and `k := nr + nf + off`:

1. `instAt_ctor_hpi` (§T10) fixes `As = instAllTele (D.atRecTele (C.fieldTypesR D R)) (bvars k D.np) 0`;
2. `instAllTele_bvars_lift` + `atRecTele_fieldTypesR_closedTele` turn that into `liftTele k … 0`;
3. `HasArgs.bvars` types the spine against `liftTele (nr+nf) (liftTele off srcF 0) 0`, which
   `liftTele_collapse₂` collapses to `liftTele (off+(nr+nf)) srcF 0` — **the same offset**, as
   §T12.1 predicted;
4. `TeleDefEq.weakN` lifts `MinorFldDefEq` over the field/ih block and
   `atRecTele_fieldTypesR_substC_eq` identifies its right endpoint with the *unsubstituted*
   restored telescope;
5. `congr_tele` closes it.

The σ-identity on `D.atRecTele D.params` is needed because `MinorFldDefEq` states its context
with the parameter block **substituted** and `MinorCtorHargs` states it **raw**. -/

namespace VIndRestore
variable {e : VEnv} {R : VIndRestore} {D : VInductDecl'} {C : VIndCtor} {σ : CSubst} {q : Nat}

/-- **`MinorCtorHargs`'s `hAs` conjunct, at the `As` `instAt_ctor_hpi` delivers.**

`hfld` is `MinorFldDefEq`, which obligation (B)'s closure already demands at *every* entry — so
this consumes nothing new from the caller.  The other three inputs are §T13's two side conditions
plus the parameter-block σ-identity. -/
theorem minorCtor_hAs (he : e.Ordered) (hfld : R.MinorFldDefEq D σ e q C)
    (hσp : (D.atRecTele D.params).map (VExpr.substC · σ) = D.atRecTele D.params)
    (hσf : (D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ)
      = D.atRecTele (C.fieldTypesR D R))
    (hclF : VExpr.ClosedTele (D.atRecTele (C.fieldTypesR D R)) D.np) :
    e.HasArgs D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      (VExpr.instAllTele (D.atRecTele (C.fieldTypesR D R))
        (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np) 0)
      (VExpr.bvars (D.ihTypes q C).length C.fields.length) := by
  -- lengths: the substituted source field telescope has `C.fields.length` entries
  have hlensrc : ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)).length
      = C.fields.length := by
    simp [VInductDecl'.length_atRecTele]
  -- step 2: the existential `As` is a `liftTele`
  rw [VExpr.instAllTele_bvars_lift
    (n := D.np) (j := (D.ihTypes q C).length + C.fields.length + (D.nm + q)) (m := 0)
    (by simpa using hclF)]
  -- step 3: the spine, typed against the source field telescope
  have hbv := VEnv.HasArgs.bvars (env := e) (U := D.recUvars)
    (Δ := ((D.ihTypes q C).map (VExpr.substC · σ)).reverse)
    (As := VExpr.liftTele (D.nm + q)
      ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)) 0)
    (Γ₀ := ((D.minors.map (VExpr.substC · σ)).take q).reverse
      ++ ((D.motives.map (VExpr.substC · σ)).reverse ++ (D.atRecTele D.params).reverse))
  rw [List.length_reverse, List.length_map, VExpr.length_liftTele, hlensrc,
    VExpr.liftTele_collapse₂] at hbv
  -- step 4: `MinorFldDefEq`, lifted over the field/ih block, right endpoint desubstituted
  rw [VIndRestore.MinorFldDefEq, hσp, hσf] at hfld
  have hw := VEnv.TeleDefEq.weakN (n := (D.ihTypes q C).length + C.fields.length) (k := 0) he
    (Ctx.LiftN.zero (((D.ihTypes q C).map (VExpr.substC · σ)).reverse
      ++ (VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)) 0).reverse) (by
        simp [VExpr.length_liftTele, hlensrc])) hfld
  rw [VExpr.liftTele_collapse₂, VExpr.liftTele_collapse₂] at hw
  -- step 5
  have hcong := hbv.congr_tele he hw
  rw [show D.nm + q + ((D.ihTypes q C).length + C.fields.length)
      = (D.ihTypes q C).length + C.fields.length + (D.nm + q) from by omega] at hcong
  simpa [List.reverse_append, List.append_assoc] using hcong

/-! ### §4c …and `MinorCtorHargs` from **two** components, not four

`instAt_ctor_hpi` (§T10) fixes `B`, `As` and `B'` outright, so `hpi` is not data; §4b then closes
`hAs`.  What is left of `MinorCtorHargs` is `hcbody` and `hfun` — the two `hargs`-shaped data
§5 below already names as the open obligation.

The `Faithful` cost is real and is **available here**, unlike at (A): §5's `hminD` is demanded only at
`T.name ∈ K`, which is exactly `Faithful.ctor_agree`'s guard. -/

/-- **`MinorCtorHargs` with `hpi` and `hAs` both derived.**

`hlen`/`hagree` are `Faithful.ctor_agree` read through `VIndCtor.WF.params_len`; `hfld` is the
`MinorFldDefEq` obligation (B)'s closure already demands at every entry; `hσp`/`hσf`/`hclF` are
§T16.2's parameter σ-identity and §T13's two side conditions.  `hcbody` and `hfun` are the only
data left. -/
theorem minorCtorHargs_of_hargs (he : e.Ordered) {t npJ : Nat} {ci : VConstant}
    (hlen : D.params.length = C.params.length)
    (hagree : R.instAt D npJ t ci.type = C.typeR D R t)
    (hfld : R.MinorFldDefEq D σ e q C)
    (hσp : (D.atRecTele D.params).map (VExpr.substC · σ) = D.atRecTele D.params)
    (hσf : (D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ)
      = D.atRecTele (C.fieldTypesR D R))
    (hclF : VExpr.ClosedTele (D.atRecTele (C.fieldTypesR D R)) D.np)
    (hcbody : e.HasType D.recUvars ((D.atRecTele D.params).reverse)
      (D.atRec (R.ctorBody D t C))
      (D.atRec (VExpr.instAll (VExpr.splitPis npJ (ci.type.instL (R.tyLvls t))).2
        (R.tyArgs t))))
    (hfun : e.HasType D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      ((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a)).map (VExpr.substC · σ)))
      (.forallE (VExpr.instAll
          (VExpr.instAll (D.tyAppR' R t C.fields.length (D.atRecTele C.args))
            (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)
            (C.fieldTypesR D R).length)
          (VExpr.bvars (D.ihTypes q C).length C.fields.length))
        (.sort D.elimLvl))) :
    R.MinorCtorHargs D σ e q t C :=
  ⟨_, _, _, hcbody, VIndRestore.instAt_ctor_hpi hlen hagree,
    minorCtor_hAs he hfld hσp hσf hclF, hfun⟩

/-- **…and with §T13's two side conditions CALLED rather than hypothesised.**

`minorCtorHargs_of_hargs` takes `hσf` and `hclF` as facts; this takes their producers' inputs
instead, so the chain `§T13 → §T12.1 → §4b → MinorCtorHargs` is composed end to end and nothing is
asserted.  `atRecTele_fieldTypesR_closedTele` and `atRecTele_fieldTypesR_substC_eq` were the two
declarations in the relayed zero-user list that stayed zero-user after §4c; they are consumed here.

Every hypothesis is either one §5's `recConstsR_wf_of_recHargsD` already carries (`henv`, `hD`, `hcl`),
a `Faithful` clause (available at `T.name ∈ K`, which is where `hminD` is demanded), or a side
condition on the restoration data that is `decide`-able at a witness (`hargsF`). -/
theorem minorCtorHargs_of_hargs' {env : VEnv} {env₃ : VEnv} {t npJ : Nat} {T : VIndType}
    {ci : VConstant} (he : e.Ordered) (henv : env.Ordered) (henv₃ : env₃.Ordered)
    (hD : D.WF env) (hfresh : σ.FreshIn env)
    (hCwf : VIndCtor.WF env₃ D t T C)
    (hci : env.constants (R.ctorName C.name) = some ci)
    (hagree : R.instAt D npJ t ci.type = C.typeR D R t)
    (hcl : ∀ j, ∀ a ∈ R.tyArgs j, a.ClosedN D.np)
    (hargsF : ∀ a ∈ R.tyArgs t, a.NoCSubst σ)
    (hfld : R.MinorFldDefEq D σ e q C)
    (hcbody : e.HasType D.recUvars ((D.atRecTele D.params).reverse)
      (D.atRec (R.ctorBody D t C))
      (D.atRec (VExpr.instAll (VExpr.splitPis npJ (ci.type.instL (R.tyLvls t))).2
        (R.tyArgs t))))
    (hfun : e.HasType D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      ((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a)).map (VExpr.substC · σ)))
      (.forallE (VExpr.instAll
          (VExpr.instAll (D.tyAppR' R t C.fields.length (D.atRecTele C.args))
            (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)
            (C.fieldTypesR D R).length)
          (VExpr.bvars (D.ihTypes q C).length C.fields.length))
        (.sort D.elimLvl))) :
    R.MinorCtorHargs D σ e q t C := by
  have hlen : D.params.length = C.params.length := by rw [hCwf.params_len]
  refine minorCtorHargs_of_hargs he hlen hagree hfld
    (VInductDecl'.atRecTele_params_substC_eq henv hD hfresh)
    (VIndRestore.atRecTele_fieldTypesR_substC_eq henv hfresh hci hargsF hlen hagree)
    (VIndCtor.atRecTele_fieldTypesR_closedTele hcl ?_) hcbody hfun
  have hsrc := VExpr.closedTele_append.1 (hCwf.tele_closed henv₃)
  rw [Nat.zero_add, hCwf.params_len] at hsrc
  exact hsrc.2

end VIndRestore

/-! ## §5 Obligation (B) at `D.np > 0` from the bundles, with the off-`K` entries free -/

/-- **OBLIGATION (B) OF `VEnv.addInductR_ordered'` AT `D.np > 0`, FROM THE BUNDLED TYPED DATA.**

No bound on `D.np`, no `hp : D.params = []`, no `hcl0`, and no `σ.WF` (which is *refuted* between
the staging pair at a parameterised block).  Every telescope-typing input is discharged: the entry
`OnCtx`s from `hsrc`/`hσ` (§2), `hOnp` from those plus §T16.2's σ-identity, `hbv` from
`HasArgs.bvars`, `hpcl` and the σ-identity from `D.WF env` and `σ.FreshIn env`.  The `Hargs`
bundles are asked for **only at a companion type** (`T.name ∈ K`); off `K` the entry defeqs are
reflexive and free (`OwnId.tyAppR'_eq` / `.ctorAppR_eq`), which is what keeps the premise set
inhabitable at a real nested block — see the `hK`-vacuity note in §5's preamble above.

**This is a reduction, not a discharge.**  `hmotD`/`hminD`/`hbodyD` *are* the open obligation:
they are `hargs` — the presented spine typed against the declared constant's binders — and
`VIndRestore.instAt_indep_of_tyArgs` says no restoration-independent argument supplies it.
`hfldD` is §T15.7's residual, which §T16.1 turns into the *same* head datum at the recursive
fields.  See `docs/handoff-rectyped.md` for what is and is not claimed. -/
theorem VEnv.recConstsR_wf_of_recHargsD {env E₂ e₂ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Name}
    (henv : env.Ordered) (hD : D.WF env) (hfresh : (R.csubst D K).FreshIn env)
    (hsrc : ∀ c ∈ D.recConsts, VConstant.WF E₂ c.2)
    (hσ : (R.csubst D K).WFD E₂ e₂ D.recUvars) (hσc : (R.csubst D K).Closed)
    (he₂ : e₂.Ordered)
    (hfr : R.SubstFree D (R.csubst D K)) (hat : R.SubstAt D K (R.csubst D K))
    (hown : R.OwnId D K) (helim : D.elimLvl.WF D.recUvars)
    (hcl : ∀ t : Nat, ∀ a ∈ R.tyArgs t, a.ClosedN D.np)
    (hmotD : ∀ (t : Nat) (T : VIndType), D.types[t]? = some T → T.name ∈ K →
      R.MotiveHargs D (R.csubst D K) e₂ t T)
    (hfldD : ∀ (q t : Nat) (C : VIndCtor), D.ctorsAll[q]? = some (t, C) →
      R.MinorFldDefEq D (R.csubst D K) e₂ q C)
    (hminD : ∀ (q t : Nat) (C : VIndCtor) (T : VIndType), D.ctorsAll[q]? = some (t, C) →
      D.types[t]? = some T → T.name ∈ K →
      R.MinorCtorHargs D (R.csubst D K) e₂ q t C)
    (hbodyD : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      R.RecBodyHargs D (R.csubst D K) e₂ j T) :
    ∀ c ∈ D.recConstsR R K, VConstant.WF e₂ c.2 := by
  have hrec : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T →
      VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩ := by
    intro j T hT
    exact hsrc (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩) (by
      simp only [VInductDecl'.recConsts, List.mem_map]
      exact ⟨(T, j), List.mk_mem_zipIdx_iff_getElem?.2 hT, rfl⟩)
  refine VEnv.recConstsR_wf_of_entriesD hsrc hσ he₂ ?_ ?_ ?_
  · -- the motive block
    intro t ht
    obtain ⟨Tt, hTt⟩ : ∃ Tt, D.types[t]? = some Tt := by
      rcases hlt : D.types[t]? with _ | Tt
      · exact absurd (by simpa using List.getElem?_eq_none_iff.1 hlt) (by simpa using ht)
      · exact ⟨Tt, rfl⟩
    by_cases hKt : Tt.name ∈ K
    · obtain ⟨As, B, B', w, hbody, hpi, hAs, hsort⟩ := hmotD t Tt hTt hKt
      exact VIndRestore.motiveEntry_defeq_of_hargs henv hD hfresh he₂ hσ hσc hfr hat helim
        (VInductDecl'.getD_types hTt) (hrec t Tt hTt) hTt hKt ht (hcl t) hbody hpi hAs hsort
    · exact motiveEntry_defeq_off_K he₂ hσ hown
        (VInductDecl'.getD_types hTt) (hrec t Tt hTt) hTt hKt ht
  · -- the minor block
    intro q t C hq
    obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hq)
    have hqlt : q < D.minors.length := by
      simpa using (List.getElem?_eq_some_iff.1 hq).1
    by_cases hKt : T.name ∈ K
    · obtain ⟨As, B, B', hcbody, hpi, hAs, hfun⟩ := hminD q t C T hq hT hKt
      exact VIndRestore.minorEntry_defeq_of_hargs henv hD hfresh he₂ hσ hσc hfr hat
        (VInductDecl'.getD_types hT) (hrec t T hT) hT hKt hC hq hqlt (hcl t)
        (hfldD q t C hq) hcbody hpi hAs hfun
    · exact VIndRestore.minorEntry_defeq_off_K he₂ hσ hσc hown
        (VInductDecl'.getD_types hT) (hrec t T hT) hT hKt hC hq hqlt (hfldD q t C hq)
  · -- the recursor body
    intro j T hT
    by_cases hK : T.name ∈ K
    · obtain ⟨w, hhead, hconcl⟩ := hbodyD j T hT hK
      exact VIndRestore.recBody_defeq_of_hargs hfr hhead hconcl
    · exact recBody_defeq_off_K he₂ hσ hown (hrec j T hT) hT hK

/-! ## §6 Anti-vacuity

Three separate facts, kept separate because a clean axiom line is not evidence of content
(`docs/vacuity-ledger.md` §0).

### 6a The `hK`-for-all-types version of §5 was VACUOUS, and here is the refutation

The first version of §5 demanded `hK : ∀ t T, D.types[t]? = some T → T.name ∈ K` — the hypothesis
`substC_motiveType_defeq'` and `substC_minorType_defeq` each carry per entry, lifted to the whole
block.  `ntree_recTyped_hK_false` refutes that conjunction at the canonical parameterised nested
block: `K` lists the **companions**, and an auxiliary block always also contains the *outer*
head, which is not one.  So that version's premises were jointly unsatisfiable at every real
nested block while printing a perfectly clean axiom line.

That is what §5's `T.name ∈ K` guards and the off-`K` branch replaces.

### 6b The non-bundle premises of §5 hold JOINTLY at a parameterised nested block

`ntreeAux_obligationB_of_bundles` is §5 with every hypothesis except the four data families
discharged at `ntreeAux` (`np = 1`), from the staging equations alone.  This is the (B)
counterpart of `InductiveDeclExamples.ntreeAux_obligationC_of_hdata`, and it is the *joint*
inhabitation check, not a per-hypothesis one.

### 6c What is NOT established

The four data families are **not** inhabited here, at `ntreeAux` or anywhere with `D.np > 0`.
`hargs` is the open obligation and `VIndRestore.instAt_indep_of_tyArgs` says no
restoration-independent argument produces it.  §5 is a **reduction**, and is graded as one. -/

namespace InductiveDeclExamples

/-- **§6a's refutation.**  `ntreeK = [`_nested.List_1]`, and `ntreeAux.types` also contains the
block's own head `NTree`, whose name is not in `K`. -/
theorem ntree_recTyped_hK_false :
    ¬ (∀ (t : Nat) (T : VIndType), ntreeAux.types[t]? = some T → T.name ∈ ntreeK) := by
  intro h
  have h0 : ntreeAux.types[0]? = some (ntreeAux.types.getD 0 default) := rfl
  exact absurd (h 0 _ h0) (by decide)

section
variable {env₁ E₁ E₂ E₃ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hE₁ : env₁.addIndTypes ntreeAux = some E₁)
variable (hE₂ : E₁.addIndCtors ntreeAux = some E₂)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)

include h hE₁ hE₂ hF₁ hF₂ in
/-- **§6b: obligation (B) at the canonical parameterised nested block, from the four data
families and the staging equations alone.**  Every other hypothesis of §5 is discharged. -/
theorem ntreeAux_obligationB_of_bundles
    (hmotD : ∀ (t : Nat) (T : VIndType), ntreeAux.types[t]? = some T → T.name ∈ ntreeK →
      ntreeRestore.MotiveHargs ntreeAux (ntreeRestore.csubst ntreeAux ntreeK) F₂ t T)
    (hfldD : ∀ (q t : Nat) (C : VIndCtor), ntreeAux.ctorsAll[q]? = some (t, C) →
      ntreeRestore.MinorFldDefEq ntreeAux (ntreeRestore.csubst ntreeAux ntreeK) F₂ q C)
    (hminD : ∀ (q t : Nat) (C : VIndCtor) (T : VIndType),
      ntreeAux.ctorsAll[q]? = some (t, C) → ntreeAux.types[t]? = some T → T.name ∈ ntreeK →
      ntreeRestore.MinorCtorHargs ntreeAux (ntreeRestore.csubst ntreeAux ntreeK) F₂ q t C)
    (hbodyD : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → T.name ∈ ntreeK →
      ntreeRestore.RecBodyHargs ntreeAux (ntreeRestore.csubst ntreeAux ntreeK) F₂ j T) :
    ∀ c ∈ ntreeAux.recConstsR ntreeRestore ntreeK, VConstant.WF F₂ c.2 :=
  VEnv.recConstsR_wf_of_recHargsD (listEnv_ordered h) (ntreeAux_WF h) (ntree_csubst_fresh h)
    (ntree_recConsts_wf h hE₁ hE₂) (ntree_csubst_WFD₂ h hE₁ hE₂ hF₁ hF₂) ntree_csubst_closed
    (ntreeF₂_ordered h hE₁ hF₁ hF₂) ntreeRestore_substFree ntreeRestore_domSep.substAt
    ntreeRestore_ownId (by decide) ntree_tyArgs_closedN_np hmotD hfldD hminD hbodyD

end

/-- **§6b with nothing assumed.**  `ntree_stage₂_exists` supplies the five staging equations, so
the twelve non-bundle premises of §5 are jointly satisfiable *outright* at a parameterised nested
block — not merely relative to hypotheses.  This is the arity-0 form of the inhabitation check;
the four data families are still open (§6c). -/
theorem ntreeAux_recHargs_premises_inhabited :
    ∃ (env₁ E₁ E₂ F₁ F₂ : VEnv), VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some E₁ ∧ E₁.addIndCtors ntreeAux = some E₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁ ∧
      F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂ ∧
      env₁.Ordered ∧ ntreeAux.WF env₁ ∧
      (ntreeRestore.csubst ntreeAux ntreeK).FreshIn env₁ ∧
      (∀ c ∈ ntreeAux.recConsts, VConstant.WF E₂ c.2) ∧
      (ntreeRestore.csubst ntreeAux ntreeK).WFD E₂ F₂ ntreeAux.recUvars ∧
      (ntreeRestore.csubst ntreeAux ntreeK).Closed ∧ F₂.Ordered ∧
      ntreeRestore.SubstFree ntreeAux (ntreeRestore.csubst ntreeAux ntreeK) ∧
      ntreeRestore.SubstAt ntreeAux ntreeK (ntreeRestore.csubst ntreeAux ntreeK) ∧
      ntreeRestore.OwnId ntreeAux ntreeK ∧ ntreeAux.elimLvl.WF ntreeAux.recUvars ∧
      (∀ t : Nat, ∀ a ∈ ntreeRestore.tyArgs t, a.ClosedN ntreeAux.np) := by
  obtain ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂⟩ := ntree_stage₂_exists
  exact ⟨env₁, E₁, E₂, F₁, F₂, h, hE₁, hE₂, hF₁, hF₂, listEnv_ordered h, ntreeAux_WF h,
    ntree_csubst_fresh h, ntree_recConsts_wf h hE₁ hE₂, ntree_csubst_WFD₂ h hE₁ hE₂ hF₁ hF₂,
    ntree_csubst_closed, ntreeF₂_ordered h hE₁ hF₁ hF₂, ntreeRestore_substFree,
    ntreeRestore_domSep.substAt, ntreeRestore_ownId, by decide, ntree_tyArgs_closedN_np⟩

/-- **A partial inhabitation datum for `MinorFldDefEq`, disclosed as degenerate.**  At a
constructor with **no** fields the telescope defeq is `TeleDefEq.nil`, so the bundle is not
uniformly false.  This is a *degenerate* witness in exactly the sense
`docs/vacuity-ledger.md` §5a asks to be disclosed: it says nothing about the entries where the
field telescope moves, which are the ones that carry the content. -/
theorem ntree_minorFld_nil (F : VEnv) :
    ntreeRestore.MinorFldDefEq ntreeAux (ntreeRestore.csubst ntreeAux ntreeK) F 1 nlistNil :=
  .nil

/-- …and the entry it is about is a real entry of the block. -/
theorem ntree_ctorsAll_one : ntreeAux.ctorsAll[1]? = some (1, nlistNil) := rfl

/-- **The complement: at `NTree.node` the field telescope really does move**, so `MinorFldDefEq`
is *not* `TeleDefEq.refl` there — which is why §5 asks for it at every `q`, including the off-`K`
ones, and why the off-`K` branch is not a way of making the minor block free. -/
theorem ntree_node_fieldTypesR_ne :
    ntreeAux.atRecTele (ntreeNode.fields.map (·.type))
      ≠ ntreeAux.atRecTele (ntreeNode.fieldTypesR ntreeAux ntreeRestore) := by decide

end InductiveDeclExamples

/-! ## §7 Axiom audit

Hole-freeness only — `docs/handoff-rectyped.md` §0 states inhabitation separately. -/

#print axioms Lean4Lean.VEnv.recConstsR_wf_of_recHargsD
#print axioms Lean4Lean.VEnv.motiveEntry_substCD_onCtx
#print axioms Lean4Lean.VEnv.minorEntry_substCD_onCtx
#print axioms Lean4Lean.VEnv.minorEntry_substCD_body
#print axioms Lean4Lean.VEnv.recPar_substCD_onCtx
#print axioms Lean4Lean.VIndRestore.motiveEntry_defeq_of_hargs
#print axioms Lean4Lean.VIndRestore.minorEntry_defeq_of_hargs
#print axioms Lean4Lean.VIndRestore.recBody_defeq_of_hargs
#print axioms Lean4Lean.motiveEntry_defeq_off_K
#print axioms Lean4Lean.VIndRestore.minorEntry_defeq_off_K
#print axioms Lean4Lean.recBody_defeq_off_K
#print axioms Lean4Lean.InductiveDeclExamples.ntree_recTyped_hK_false
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_obligationB_of_bundles
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_recHargs_premises_inhabited
#print axioms Lean4Lean.InductiveDeclExamples.ntree_minorFld_nil
#print axioms Lean4Lean.VIndRestore.minorCtor_hAs
#print axioms Lean4Lean.VIndRestore.minorCtorHargs_of_hargs
#print axioms Lean4Lean.VIndRestore.minorCtorHargs_of_hargs'
#print axioms Lean4Lean.InductiveDeclExamples.ntree_node_fieldTypesR_ne

end Lean4Lean
