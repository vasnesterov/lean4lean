import Lean4Lean.Theory.Typing.PatternRules
import Lean4Lean.Theory.Inductive.NestedBuild
import Lean4Lean.Theory.Inductive.NestedOrdered

/-!
# Wall 2, restated truly: a nested step keeps `KeyUnique`, and refutes `KeyMajorUnique`

`docs/handoff-inductive-add.md` §5.3 recorded that `Theory/Typing/DeltaUnique.lean`'s
`keys_induct` argues from a **freshness** premise that a nested step cannot supply: the key of
a companion member's ι-rule is `[R.recName I_j.rec, R.ctorName C.name]`, and the second name is
the constructor of a block the environment already holds.  That was right, and it understated
the problem.  The defect is not in the *argument*; it is in the **invariant**.

`VEnv.KeyMajorUnique` — *a rule is determined by the head of its major premise* — is **false**
in an environment holding a nested block.  `nfn_keyMajorUnique_false` below exhibits the pair:
`PFn`'s own ι-rule, keyed `[PFn.rec, PFn.mk]`, and `NFn`'s companion ι-rule, keyed
`[NFn.rec_1, PFn.mk]`.  Two distinct rules, one major-premise head.  So no repair of
`keys_induct`'s proof could have worked; the statement it proves had to change.

The replacement is `VEnv.KeyUnique` (`Theory/Typing/DeltaUnique.lean` Part II): a rule is
determined by its **whole** key.  It is what a nested step can defend, because the *head* of
every rule the step emits is a constant the step itself declares, hence fresh — the freshness
§5.3 identified as the one that is available.  This file:

1. records the swap in the two files that carried the old invariant (§1), now landed;
2. **refutes** `KeyMajorUnique` at the `NFn`/`PFn` witness, and checks that the same pair does
   *not* refute `KeyUnique` (`nfn_keys_ne`) — so the replacement is not refuted by the very
   example that kills the original;
3. proves the **nested arm** — `addInductR` preserves `KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique`
   — from `VIndRestore.Faithful` plus one syntactic property of the restoration,
   `VIndRestore.KeysDistinct`, which is discharged at both nested witnesses by `decide`;
4. lists what is left for the nested `VDecl.WF` rule itself (§4).

**Status (2026-08-31).**  The swap has landed: `VEnv.WF'.keys` carries
`KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique`, `VEnv.WF.keyMajorUnique` no longer exists, and
`Pat.iota_rule_uniq` reads `KeyUnique`.  `VEnv.KeyMajorUnique` survives as a definition only,
as the subject of `nfn_keyMajorUnique_false` and of `VEnv.keyUnique_of_major` (the record that
the replacement is a *weakening*, hence lost nothing in the current tree).  Nothing derives it
from `VEnv.WF` any more.
-/

namespace Lean4Lean

open VInductDecl' (iotaRuleR iotaRulesR)

/-! ## 1. The consumer, re-proved from `KeyUnique` — **landed**

`Theory/Typing/PatternRules.lean`'s `Pat.iota_rule_uniq` was the **only** use of
`KeyMajorUnique` in the tree (`Pat.deltaHead_ne_recName`, `.deltaHead_ne_ctorName` and
`Pat.deltaHead_ne_quot` use `KeyHeadDelta`, which survives).  It read the constructor name off
the shared pattern and appealed to the last key entry.

`VInductDecl'.iotaPat_inj` already returned the recursor name equation too — it was discarded
there — so the whole key was available and the appeal could be to `KeyUnique` instead.  The
only cost was that the key's head is `mkRecName (D.types.getD j default).name` while the
pattern carries `mkRecName T.name`, so the two `types[j]? = some T` hypotheses had to be
threaded in.  They were already present at the sole call site (`Pat.iota_data_uniq`, which
passes exactly `hTj` and `hTj'` to `VInductDecl'.iotaRule_inj` on the very next line), so this
was a hypothesis reshuffle inside one file and not a new obligation — **verified, and done**.

The lemmas this section used to carry, `Pat.iota_rule_uniq_keyUnique` and its `env.WF`
wrapper, now live in `Theory/Typing/PatternRules.lean` itself as
`Pat.iota_rule_uniq_keyUnique` and `Pat.iota_rule_uniq`. -/

/-! ## 2. The refutation, at a real nested block

The witness is `Theory/Inductive/NestedBuild.lean` Part 9's:

```
inductive PFn (α : Type) | mk : α → (Prop → α) → PFn α
inductive NFn            | node : PFn NFn → NFn
```

`env₂` is the environment after `PFn`'s own declaration step; the nested step for `NFn` is
`env₂.addInductR nfnAux nfnK nfnRestore`, which `nfnAux_admitted` shows succeeds. -/

namespace InductiveDeclExamples

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)
include h

/-- `PFn`'s own ι-rule is registered in `env₂`. -/
theorem pfn_iotaRule_defeqs : env₂.defeqs (pfnDecl.iotaRule 0 0 pfnMk) :=
  VEnv.addInduct'_defeqs h _
    (show pfnDecl.iotaRule 0 0 pfnMk ∈ pfnDecl.iotaRules from List.mem_cons_self)

omit h in
theorem pfn_iotaRule_key : (pfnDecl.iotaRule 0 0 pfnMk).key = [``PFn.rec, ``PFn.mk] := by
  rw [VInductDecl'.key_iotaRule]; rfl

omit h in
theorem nfn_companion_iotaRule_key :
    (nfnAux.iotaRuleR nfnRestore 1 1 pfnAuxMk).key = [``NFn.rec_1, ``PFn.mk] := by
  rw [VInductDecl'.key_iotaRuleR]; rfl

omit h in
theorem nfn_companion_mem :
    nfnAux.iotaRuleR nfnRestore 1 1 pfnAuxMk ∈ nfnAux.iotaRulesR nfnRestore := by
  rw [VInductDecl'.iotaRulesR]
  exact List.mem_map.2 ⟨((1, pfnAuxMk), 1),
    show _ ∈ [((0, nfnNode), 0), ((1, pfnAuxMk), 1)] from
      List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩

/-- **`VEnv.KeyMajorUnique` is false after a nested step.**

`PFn.rec`'s ι-rule and `NFn.rec_1`'s companion ι-rule are two *different* rules of the same
environment whose keys end in the same name, `PFn.mk`.  So the `induct` arm of
`VEnv.WF'.keys` could never have been extended to a nested step *while it concluded
`KeyMajorUnique`*, by any argument whatever: its conclusion is false there.  This is the
statement `docs/handoff-inductive-add.md` §5.3 recorded as an argument gap; it is a refutation
of the invariant, and it is why `WF'.keys` concludes `KeyUnique` today. -/
theorem nfn_keyMajorUnique_false {env₃ : VEnv}
    (hR : env₂.addInductR nfnAux nfnK nfnRestore = some env₃) : ¬ env₃.KeyMajorUnique := by
  intro H
  have h1 : env₃.defeqs (pfnDecl.iotaRule 0 0 pfnMk) :=
    (VEnv.addInductR_le hR).defeqs (pfn_iotaRule_defeqs h)
  have h2 : env₃.defeqs (nfnAux.iotaRuleR nfnRestore 1 1 pfnAuxMk) :=
    VEnv.addInductR_defeqs hR _ nfn_companion_mem
  have he := H _ _ ``PFn.mk h1 h2
    (by rw [pfn_iotaRule_key]; rfl) (by rw [nfn_companion_iotaRule_key]; rfl)
  have hk := congrArg VDefEq.key he
  rw [pfn_iotaRule_key, nfn_companion_iotaRule_key] at hk
  exact absurd hk (by decide)

omit h in
/-- **…and the same pair does not refute `KeyUnique`.**  The two rules differ in the *head*
of their key — `PFn.rec` against `NFn.rec_1` — which is exactly the position a nested step
controls: `NFn.rec_1` is a constant the step declares itself. -/
theorem nfn_keys_ne :
    (pfnDecl.iotaRule 0 0 pfnMk).key ≠ (nfnAux.iotaRuleR nfnRestore 1 1 pfnAuxMk).key := by
  rw [pfn_iotaRule_key, nfn_companion_iotaRule_key]; decide

end

end InductiveDeclExamples

/-! ## 3. The nested arm: `addInductR` preserves the replacement

The three obligations `VEnv.keysU_addDefEqList_notDelta` asks for, at a nested step:

* **`hdecl`** — every key name is declared.  The *head* is `R.recName I_j.rec`, one of the
  step's own `recConstsR`; the *major* is `R.ctorName C.name`, which for a member the step
  declares is one of its own `ctorConstsCR`, and for a **companion** member is a constant the
  environment already holds — `VIndRestore.Faithful.ctor_agree`, verbatim.
* **`hδ`** — no registered δ-rule's head occurs in a new key.  For the head and for a declared
  member's major this is freshness.  For a **companion** member's major it cannot be, and the
  argument is instead: `Faithful.ctors_complete` names the block `D₀` the environment holds
  whose constructors the companion's are, `VInductDecl'.Declared` puts `D₀`'s own ι-rules into
  `env`, and `KeyHeadDelta` at `env` then identifies the δ-rule with one of them — which
  `not_isDeltaRule_iotaRule` forbids.  So the *old* invariant discharges the *new* step's
  obligation; no new invariant is introduced.
* **`hkey`** — a new key is not a registered key.  This is where `KeyUnique` earns its keep:
  the two keys share their last name, but the new key's **head** is fresh while every name in a
  registered key is declared (`KeysDeclared`).  Under `KeyMajorUnique` there is nothing to
  argue with, because the conclusion is false (§2).

The pairwise obligation *inside* the block is a syntactic property of the restoration,
isolated as `VIndRestore.KeysDistinct` and discharged at both witnesses in §3.3. -/

namespace VEnv

open VInductDecl' (iotaLhsR iotaRuleR iotaRulesR recConstsR ctorConstsCR)

/-- No restored ι-rule is a δ-rule: `iotaLhsR` always carries at least the major premise. -/
theorem not_isDeltaRule_iotaRuleR (D : VInductDecl') (R : VIndRestore) (j q : Nat)
    (C : VIndCtor) : ∀ c, ¬ IsDeltaRule (D.iotaRuleR R j q C) c := by
  refine not_isDeltaRule_mkLams (fun c ls => ?_)
  rw [VInductDecl'.iotaLhsR, VExpr.mkApp_concat]
  nofun

theorem not_isDeltaRule_iotaRulesR {D : VInductDecl'} {R : VIndRestore} :
    ∀ df ∈ D.iotaRulesR R, ∀ c, ¬ IsDeltaRule df c := by
  intro df hdf
  rw [VInductDecl'.iotaRulesR, List.mem_map] at hdf
  obtain ⟨⟨⟨j, C⟩, q⟩, _, rfl⟩ := hdf
  exact fun c => not_isDeltaRule_iotaRuleR D R j q C c

/-- …and neither is the *substituted* one, which is what the step registers. -/
theorem not_isDeltaRule_iotaRulesRS {D : VInductDecl'} {R : VIndRestore} {K : List Lean.Name}
    (hfree : R.KeysFree D K) : ∀ df ∈ D.iotaRulesRS R K, ∀ c, ¬ IsDeltaRule df c := by
  intro df hdf
  rw [VInductDecl'.iotaRulesRS, List.mem_map] at hdf
  obtain ⟨df₀, hdf₀, rfl⟩ := hdf
  rw [VInductDecl'.iotaRulesR, List.mem_map] at hdf₀
  obtain ⟨⟨⟨j, C⟩, q⟩, hm, rfl⟩ := hdf₀
  obtain ⟨h1, h2⟩ := hfree (j, C) (D.mem_ctorsAll_of_mem_zipIdx hm)
  exact D.not_isDeltaRule_iotaRuleR_substC R j q C h1 h2

end VEnv

/-- The renamed recursor of a member is one of the *recursor* constants the step declares —
`VInductDecl'.recName_mem_allNamesCR` refined to the stage that declares it. -/
theorem VInductDecl'.recName_mem_recConstsR (D : VInductDecl') (R : VIndRestore) {j : Nat}
    {T : VIndType} (hT : D.types[j]? = some T) :
    R.recName (Lean.mkRecName (D.types.getD j default).name)
      ∈ (D.recConstsR R K).map (·.1) := by
  rw [VInductDecl'.getD_types hT, VInductDecl'.recConstsR, List.map_map]
  exact List.mem_map.2 ⟨(T, j), List.mem_zipIdx_iff_getElem?.2 hT, rfl⟩

/-- A **non-companion** member's restored constructor name is one of the constructor
constants the step declares. -/
theorem VInductDecl'.ctorName_mem_ctorConstsCR (D : VInductDecl') (R : VIndRestore)
    (K : List Lean.Name) {j : Nat} {C : VIndCtor} (hm : (j, C) ∈ D.ctorsAll)
    (hK : (D.types.getD j default).name ∉ K) :
    R.ctorName C.name ∈ (D.ctorConstsCR R K).map (·.1) := by
  rw [VInductDecl'.ctorConstsCR]
  refine List.mem_map.2 ⟨(R.ctorName C.name,
      ⟨D.uvars, (C.typeR D R j).substC (R.csubstTy D K)⟩),
    List.mem_filterMap.2 ⟨(j, C), hm, ?_⟩, rfl⟩
  simp only [if_neg hK]

/-- **The restoration separates the block's own ι-rules.**

A purely syntactic property of `R` and `D`: no two entries of `ctorsAll` are given the same
(renamed recursor, restored constructor) pair.  It is what `KeyUnique` needs *within* the
block, and it is `decide`-able at a concrete block — §3.3 discharges it at both nested
witnesses.

It is also derivable rather than assumed, from the two `addConstList` successes plus
`Faithful.ctors_complete`: the renamed recursor names are `Nodup` because
`addConstList (D.recConstsR R K)` succeeded, which separates different members; within one
member, a declared member's restored constructor names are `Nodup` for the same reason, and a
companion member's are the constructor names of the block `ctors_complete` names, which are
`Nodup` because that block was declared.  That derivation is list combinatorics over a
`filterMap` and is not carried out here; the property is stated so that the arm below is a
theorem and not a sketch. -/
def VIndRestore.KeysDistinct (R : VIndRestore) (D : VInductDecl') : Prop :=
  D.ctorsAll.Pairwise fun a b =>
    R.recName (Lean.mkRecName (D.types.getD a.1 default).name)
        ≠ R.recName (Lean.mkRecName (D.types.getD b.1 default).name) ∨
      R.ctorName a.2.name ≠ R.ctorName b.2.name

theorem VInductDecl'.iotaRulesR_pairwise_key (D : VInductDecl') (R : VIndRestore)
    (hd : R.KeysDistinct D) :
    (D.iotaRulesR R).Pairwise fun a b => a.key ≠ b.key := by
  have h2 : D.ctorsAll.zipIdx.Pairwise fun a b =>
      R.recName (Lean.mkRecName (D.types.getD a.1.1 default).name)
          ≠ R.recName (Lean.mkRecName (D.types.getD b.1.1 default).name) ∨
        R.ctorName a.1.2.name ≠ R.ctorName b.1.2.name := by
    rw [VIndRestore.KeysDistinct, ← List.zipIdx_map_fst 0 D.ctorsAll] at hd
    exact (List.pairwise_map (f := Prod.fst)).1 hd
  rw [VInductDecl'.iotaRulesR]
  refine List.pairwise_map.2 (h2.imp ?_)
  rintro ⟨⟨j, C⟩, q⟩ ⟨⟨j', C'⟩, q'⟩ hh he
  rw [VInductDecl'.key_iotaRuleR, VInductDecl'.key_iotaRuleR] at he
  simp only [List.cons.injEq, and_true] at he
  exact hh.elim (fun h => h he.1) (fun h => h he.2)

/-- **The pairwise key separation, for the rules the step registers.**  `substC` leaves the
keys where they were (`VInductDecl'.key_iotaRuleR_substC`), so this is
`iotaRulesR_pairwise_key` transported along that equation. -/
theorem VInductDecl'.iotaRulesRS_pairwise_key (D : VInductDecl') (R : VIndRestore)
    {K : List Lean.Name} (hd : R.KeysDistinct D) (hfree : R.KeysFree D K) :
    (D.iotaRulesRS R K).Pairwise fun a b => a.key ≠ b.key := by
  have hkey : ∀ df₀ ∈ D.iotaRulesR R, (df₀.substC (R.csubst D K)).key = df₀.key := by
    intro df₀ hdf₀
    rw [VInductDecl'.iotaRulesR, List.mem_map] at hdf₀
    obtain ⟨⟨⟨j, C⟩, q⟩, hm, rfl⟩ := hdf₀
    obtain ⟨h1, h2⟩ := hfree (j, C) (D.mem_ctorsAll_of_mem_zipIdx hm)
    rw [D.key_iotaRuleR_substC R j q C h1 h2, D.key_iotaRuleR R j q C]
  rw [VInductDecl'.iotaRulesRS]
  refine List.pairwise_map.2 ((D.iotaRulesR_pairwise_key R hd).imp_of_mem ?_)
  intro a b ha hb hne
  rw [hkey a ha, hkey b hb]
  exact hne

namespace VEnv

/-- **The nested arm.**  `KeysDeclared`, `KeyHeadDelta` and `KeyUnique` all survive a nested
declaration step.  It is the exact analogue of `VEnv.keys_induct`, the non-nested `induct`
arm, and only becomes provable once that arm's third conclusion is `KeyUnique`: with
`KeyMajorUnique` there the statement below would be *false*
(`InductiveDeclExamples.nfn_keyMajorUnique_false`). -/
theorem keysR_induct {env env' : VEnv} {D : VInductDecl'} {K : List Lean.Name}
    {R : VIndRestore} {npJ : Nat → Nat}
    (hR : env.addInductR D K R = some env')
    (hf : R.Faithful D env K npJ) (hd : R.KeysDistinct D) (hfree : R.KeysFree D K)
    (ih : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyUnique) :
    env'.KeysDeclared ∧ env'.KeyHeadDelta ∧ env'.KeyUnique := by
  obtain ⟨e1, e2, e3, h1, h2, h3, rfl⟩ := VEnv.addInductR_stages hR
  have hdefeqs : e3.defeqs = env.defeqs := by
    rw [addConstList_defeqs h3, addConstList_defeqs h2, addConstList_defeqs h1]
  have hle : env ≤ e3 :=
    ((addConstList_le h1).trans (addConstList_le h2)).trans (addConstList_le h3)
  have hrecfresh : ∀ n ∈ (D.recConstsR R K).map (·.1), ¬ env.contains n := by
    rintro n hn ⟨x, hx⟩
    have := (addConstList_le h2).constants ((addConstList_le h1).constants hx)
    rw [(addConstList_fresh h3).1 n hn] at this; exact absurd this nofun
  have hctorfresh : ∀ n ∈ (D.ctorConstsCR R K).map (·.1), ¬ env.contains n := by
    rintro n hn ⟨x, hx⟩
    have := (addConstList_le h1).constants hx
    rw [(addConstList_fresh h2).1 n hn] at this; exact absurd this nofun
  have hrecdecl : ∀ n ∈ (D.recConstsR R K).map (·.1), e3.contains n := by
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hn
    exact ⟨_, addConstList_constants h3 c hc⟩
  have hctordecl : ∀ n ∈ (D.ctorConstsCR R K).map (·.1), e3.contains n := by
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hn
    exact ⟨_, (addConstList_le h3).constants (addConstList_constants h2 c hc)⟩
  -- the companion case of `hδ`, isolated: the already-declared constructor heads no δ-rule
  have hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ C ∈ T.ctors, ∀ df' c, env.defeqs df' → IsDeltaRule df' c →
        c ≠ R.ctorName C.name := by
    rintro j T hT hK C hC df' c hdf' hδ rfl
    obtain ⟨D₀, j₀, T₀, hDecl, hT₀, -, -, hmapc⟩ := hf.ctors_complete j T hT hK
    obtain ⟨C₀, hC₀, hname⟩ :=
      List.mem_map.1 (show R.ctorName C.name ∈ T₀.ctors.map (·.name) from
        hmapc ▸ List.mem_map.2 ⟨C, hC, rfl⟩)
    obtain ⟨e₀, e₁, hadd, hb⟩ := hDecl
    obtain ⟨q₀, hq₀⟩ := List.mem_iff_getElem?.1 (VInductDecl'.mem_ctorsAll_of hT₀ hC₀)
    have hrule : env.defeqs (D₀.iotaRule j₀ q₀ C₀) :=
      hb.defeqs (VEnv.addInduct'_defeqs hadd _ (List.mem_map.2
        ⟨((j₀, C₀), q₀), List.mk_mem_zipIdx_iff_getElem?.2 hq₀, rfl⟩))
    have heq := ih.2.1 df' (D₀.iotaRule j₀ q₀ C₀) _ hdf' hrule hδ
      (by rw [D₀.key_iotaRule, hname]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    exact not_isDeltaRule_iotaRule D₀ j₀ q₀ C₀ _ (heq ▸ hδ)
  refine keysU_addDefEqList_notDelta (D.iotaRulesRS R K) (keysU_mono hdefeqs hle ih)
    (not_isDeltaRule_iotaRulesRS hfree) ?_ ?_ ?_
    (D.iotaRulesRS_pairwise_key R hd hfree)
  · -- hdecl
    intro df hdf n hn
    obtain ⟨j, C, hm, hk⟩ := VInductDecl'.mem_iotaRulesRS hfree hdf
    obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hm
    rw [hk] at hn
    rcases List.mem_cons.1 hn with rfl | hn
    · exact hrecdecl _ (D.recName_mem_recConstsR R hT)
    · cases List.mem_singleton.1 hn
      by_cases hK : (D.types.getD j default).name ∈ K
      · obtain ⟨ci, hci, -, -⟩ :=
          hf.ctor_agree j T hT (by rwa [D.getD_types hT] at hK) C hC
        exact ⟨ci, hle.constants hci⟩
      · exact hctordecl _ (D.ctorName_mem_ctorConstsCR R K hm hK)
  · -- hδ
    intro df hdf df' c hdf' hδ hmem
    rw [hdefeqs] at hdf'
    have hcdecl : env.contains c :=
      ih.1 df' hdf' c (key_of_isDeltaRule hδ ▸ List.mem_singleton_self c)
    obtain ⟨j, C, hm, hk⟩ := VInductDecl'.mem_iotaRulesRS hfree hdf
    obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hm
    rw [hk] at hmem
    rcases List.mem_cons.1 hmem with rfl | hmem
    · exact hrecfresh _ (D.recName_mem_recConstsR R hT) hcdecl
    · cases List.mem_singleton.1 hmem
      by_cases hK : (D.types.getD j default).name ∈ K
      · exact hcomp j T hT (by rwa [D.getD_types hT] at hK) C hC df' _ hdf' hδ rfl
      · exact hctorfresh _ (D.ctorName_mem_ctorConstsCR R K hm hK) hcdecl
  · -- hkey
    intro df hdf df' hdf' hkeq
    rw [hdefeqs] at hdf'
    obtain ⟨j, C, hm, hk⟩ := VInductDecl'.mem_iotaRulesRS hfree hdf
    obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hm
    exact hrecfresh _ (D.recName_mem_recConstsR R hT)
      (ih.1 df' hdf' _ (by rw [← hkeq, hk]; exact List.mem_cons_self))

/-- The same for the packaged step `VEnv.AddNestedStep`, which is the premise the
`inductNested` rule of `Theory/Typing/Env.lean` would take. -/
theorem keys_addNestedStep {env env' : VEnv} {D : VInductDecl'} {K : List Lean.Name}
    {R : VIndRestore} (hs : VEnv.AddNestedStep env D K R env') (hd : R.KeysDistinct D)
    (hfree : R.KeysFree D K)
    (ih : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyUnique) :
    env'.KeysDeclared ∧ env'.KeyHeadDelta ∧ env'.KeyUnique :=
  let ⟨_, _, _, hf, hadd⟩ := hs
  keysR_induct hadd hf hd hfree ih

end VEnv

/-! ### 3.3 `KeysDistinct` at both nested witnesses

Non-vacuity: `keysR_induct`'s syntactic side condition holds at the two end-to-end nested
blocks this tree carries — `NTree`/`List` and `NFn`/`PFn` — by computation.  Both blocks have
a companion member whose restored constructor name is a name the environment already holds
(`List.cons`, `PFn.mk`), so this is the configuration `KeyMajorUnique` fails at. -/

namespace InductiveDeclExamples

theorem ntreeRestore_keysDistinct : ntreeRestore.KeysDistinct ntreeAux := by
  unfold VIndRestore.KeysDistinct; decide

theorem nfnRestore_keysDistinct : nfnRestore.KeysDistinct nfnAux := by
  unfold VIndRestore.KeysDistinct; decide

/-! `VIndRestore.KeysFree` — `keysR_induct`'s *second* syntactic side condition, the one the
substitution in `VEnv.addIndRulesR` introduced — at the same two witnesses.  Both are
`decide`, and both are non-trivial in the same way `KeysDistinct` is: `nfnRestore` really does
rename `_nested.PFn_1.rec ↦ NFn.rec_1` and `_nested.PFn_1.mk ↦ PFn.mk`, and what is being
checked is that neither *image* is back in `csubst`'s domain
`{_nested.PFn_1, _nested.PFn_1.rec, _nested.PFn_1.mk}`. -/

theorem ntreeRestore_keysFree : ntreeRestore.KeysFree ntreeAux ntreeK := by
  unfold VIndRestore.KeysFree; decide

theorem nfnRestore_keysFree : nfnRestore.KeysFree nfnAux nfnK := by
  unfold VIndRestore.KeysFree; decide

/-- **…and `KeysFree` is not vacuous: G4's own configuration fails it.**

`VInductDecl'.idRestore` leaves the recursor name alone, so at the *companion* member it
presents `_nested.PFn_1.rec` — which is precisely a name `R.csubst nfnAux nfnK` rewrites.  Under
that restoration the substitution in `VEnv.addIndRulesR` would rewrite the ι-rule's **head**,
i.e. change which constant the rule reduces, which is G4 reached by a new route.  So `KeysFree`
is the hypothesis that excludes the un-renamed recursor at the substitution level, exactly as
`VInductDecl'.key_iotaRule_ne_renamed` (`Theory/Inductive/NestedHead.lean`) excludes it at the
key level.

Note this does *not* contradict `VIndRestore.keysFree_nil`: there `K = []`, so σ is empty.  It
is having a companion member **and** not renaming its recursor that fails. -/
theorem idRestore_not_keysFree : ¬ (nfnAux.idRestore).KeysFree nfnAux nfnK := by
  unfold VIndRestore.KeysFree; decide

/-- …and the property is not trivially true of any restoration: a restoration that renamed
both members' recursors to the *same* name and both constructors to the same name would fail
it.  (`nfnAux` has two members and two constructors, so the two rules really are separated by
this property rather than by there being only one of them.) -/
theorem nfnAux_two_rules : (nfnAux.iotaRulesR nfnRestore).length = 2 := rfl

theorem nfnAux_keys :
    (nfnAux.iotaRulesR nfnRestore).map VDefEq.key
      = [[``NFn.rec, ``NFn.node], [``NFn.rec_1, ``PFn.mk]] := by
  show [(nfnAux.iotaRuleR nfnRestore 0 0 nfnNode).key,
        (nfnAux.iotaRuleR nfnRestore 1 1 pfnAuxMk).key] = _
  rw [VInductDecl'.key_iotaRuleR, VInductDecl'.key_iotaRuleR]; rfl

/-- **The whole of Wall 2 at one block, with no hypotheses.**

`env₂` is `PFn`'s environment (it exists, by `rfl`); `env₃` is the nested step's, and the step
is a real `VEnv.AddNestedStep`, not an assumption.  In `env₃`:

* `KeyMajorUnique` — the third invariant `VEnv.WF'.keys` used to prove — is **false**;
* `KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique` — the replacement — is **preserved**.

So the repair of §5.3 of `docs/handoff-inductive-add.md` is not a stronger proof of the same
statement; it is a different statement, and this is the block that separates them. -/
theorem nfn_keys_summary :
    ∃ (env₂ env₃ : VEnv),
      VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      VEnv.AddNestedStep env₂ nfnAux nfnK nfnRestore env₃ ∧
      ¬ env₃.KeyMajorUnique ∧
      ((env₂.KeysDeclared ∧ env₂.KeyHeadDelta ∧ env₂.KeyUnique) →
        env₃.KeysDeclared ∧ env₃.KeyHeadDelta ∧ env₃.KeyUnique) := by
  obtain ⟨env₂, h⟩ : ∃ e, VEnv.empty.addInduct' pfnDecl = some e := ⟨_, rfl⟩
  obtain ⟨env₃, hs⟩ := nfnAux_AddNestedStep h
  obtain ⟨npJ, hwf, hoi, hf, hadd⟩ := hs
  exact ⟨env₂, env₃, h, ⟨npJ, hwf, hoi, hf, hadd⟩, nfn_keyMajorUnique_false h hadd,
    fun ih => VEnv.keysR_induct hadd hf nfnRestore_keysDistinct nfnRestore_keysFree ih⟩

end InductiveDeclExamples

/-! ## 4. What is left when the nested `VDecl.WF` rule lands

The header of this file promised this list; here it is, measured against the tree as of
2026-08-31, when the `KeyMajorUnique` → `KeyUnique` swap landed in
`Theory/Typing/DeltaUnique.lean` and `Theory/Typing/PatternRules.lean`.

**Already done.**

* `VEnv.WF'.keys` proves `KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique`, by the same seven arms as
  before; the `keysU_*` step lemmas are the whole of the change on the `VEnv` side.
* `Pat.iota_rule_uniq` — the sole consumer — reads `WF.keyUnique`, via
  `Pat.iota_rule_uniq_keyUnique`.  `Pat.deltaHead_ne_recName`, `.deltaHead_ne_ctorName` and
  `.deltaHead_ne_quot` were untouched: they use `KeyHeadDelta`, which survives a nested step.
* The nested arm itself, `VEnv.keysR_induct` / `VEnv.keys_addNestedStep` (§3).

**Still open, in the order a nested `VDecl.WF` arm would hit them.**

1. **`VIndRestore.KeysDistinct` and `VIndRestore.KeysFree` have to stop being hypotheses.**
   `keysR_induct` takes both, and §3.3 discharges both by `decide` at the two concrete
   witnesses.  They are *not* the same debt:

   * `KeysDistinct` is derivable — from the two `addConstList` successes plus
     `Faithful.ctors_complete`, the argument sketched in its own docstring, which is list
     combinatorics over a `filterMap`.
   * `KeysFree` is **not** derivable from the premises the step carries, and that is a measured
     claim rather than a failure to find the proof: σ's domain is the companion members' own
     names, and `VInductDecl'.typeConstsC` declares none of them, so no freshness argument can
     separate a restored head from one.  Either it joins `VEnv.AddNestedStep`'s premises (where
     the checker discharges it — trivially, since `mkAuxRecNameMap` renames every auxiliary
     recursor to a name outside the `_nested` namespace), or `VIndRestore.Faithful` gains a
     clause asserting the restored names are declared in `env` while the auxiliary ones are not.
     `InductiveDeclExamples.idRestore_not_keysFree` is why it cannot simply be dropped.
2. **The other `VEnv.WF'` inductions need their own nested arms.**  `WF'.keys` is one of four
   in `Theory/Typing/DeltaUnique.lean` alone:
   * `WF'.keysNonempty` — trivial: `VInductDecl'.key_iotaRuleR` gives every restored ι-rule a
     two-element key.
   * `WF'.defEqHeads` (`DefEqHeadsDeclared`/`DefEqHeadsUnique`) — these are the bare-`const`
     case of `KeysDeclared`/`KeyHeadDelta`, so the cheapest route is to stop proving them by
     their own induction and derive them from `WF'.keys` instead, which removes the arm rather
     than writing it.  `VEnv.defEqHeads_of_keys` below checks that this really is a
     derivation and not a plan.
   * `WF'.iotaTypes` (Part III, `IotaTypeNotKey`) — a real arm: it must say that a nested
     step's block-type names head no rule key either.  For the step's *own* members that is
     the same freshness `keysR_induct` uses; for a **companion** member the type name is one
     the environment already holds, so it needs the `ctors_complete` route, exactly as `hδ`
     does in §3.
3. **`VEnv.WF'.ruleShape` (`Theory/Typing/PatternRules.lean`) needs a fourth rule shape.**
   `RuleShape` currently enumerates δ-rule, `quotDefEq`, and `D.iotaRule j q C`; a nested step
   registers `D.iotaRuleR R j q C`, which is none of them.  `Pat`'s `iota` constructor and
   `Params.extra_pat` then have to accept the restored form.  This is the largest remaining
   item, and it is *not* about keys.  `Pat.iota_rule_uniq` may well need no change at all: it
   is stated about `D.iotaRule` for an arbitrary `D`, so it applies as soon as a restored rule
   is exhibited as the `iotaRule` of *some* `VInductDecl'` — plausible, since `iotaRuleR`
   renames the constants and restores the types but keeps the shape, and **unverified**.
   Checking that is the first thing to do there.

**Not on the list.**  `VEnv.KeyMajorUnique` is retired and must stay retired: it is refuted
above, so no future arm can restore it.  It survives as a definition only, so that
`nfn_keyMajorUnique_false` and `VEnv.keyUnique_of_major` keep stating what they state. -/

namespace VEnv

/-- §4 item 2, machine-checked rather than asserted: the two `DefEqHeads*` invariants are
consequences of the key invariants, via `key_of_isDeltaRule`.  So a nested `VDecl.WF` arm owes
`WF'.defEqHeads` nothing — that induction can be deleted in favour of `WF'.keys`. -/
theorem defEqHeads_of_keys {env : VEnv} (h1 : env.KeysDeclared) (h2 : env.KeyHeadDelta) :
    env.DefEqHeadsDeclared ∧ env.DefEqHeadsUnique :=
  ⟨fun df c hdf hδ => h1 df hdf c (key_of_isDeltaRule hδ ▸ List.mem_singleton_self c),
   fun df df' c hdf hdf' hδ hδ' =>
     h2 df df' c hdf hdf' hδ (key_of_isDeltaRule hδ' ▸ List.mem_singleton_self c)⟩

end VEnv

end Lean4Lean
