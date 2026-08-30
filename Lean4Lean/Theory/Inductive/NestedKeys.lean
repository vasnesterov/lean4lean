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
`keys_induct`'s proof could have worked; the statement it proves has to change.

The replacement is `VEnv.KeyUnique` (`Theory/Typing/DeltaUnique.lean` Part IV): a rule is
determined by its **whole key**.  It is what a nested step can defend, because the *head* of
every rule the step emits is a constant the step itself declares, hence fresh — the freshness
§5.3 identified as the one that is available.  This file:

1. **refutes** `KeyMajorUnique` at the `NFn`/`PFn` witness, and checks that the same pair does
   *not* refute `KeyUnique` (`nfn_keys_ne`) — so the replacement is not refuted by the very
   example that kills the original;
2. re-proves the **only consumer**, `Pat.iota_rule_uniq`, from `KeyUnique`
   (`Pat.iota_rule_uniq_keyUnique`), and states the exact edit `Theory/Typing/PatternRules.lean`
   would need;
3. proves the **nested arm** — `addInductR` preserves `KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique`
   — from `VIndRestore.Faithful` plus one syntactic property of the restoration,
   `VIndRestore.KeysDistinct`, which is discharged at both nested witnesses by `decide`.

Nothing here edits a file this stream does not own, and `KeyMajorUnique` is left in place and
still proved: it is still *true* today, because `VDecl.WF` has no nested rule yet.  What
changes when that rule lands is listed in §4 below.
-/

namespace Lean4Lean

open VInductDecl' (iotaRuleR iotaRulesR)

/-! ## 1. The consumer, re-proved from `KeyUnique`

`Theory/Typing/PatternRules.lean`'s `Pat.iota_rule_uniq` is the **only** use of
`KeyMajorUnique` in the tree (`Pat.deltaHead_ne_recName`, `.deltaHead_ne_ctorName` and
`Pat.deltaHead_ne_quot` use `KeyHeadDelta`, which survives).  It reads the constructor name
off the shared pattern and appeals to the last key entry.

`VInductDecl'.iotaPat_inj` already returns the recursor name equation too — it is discarded
there — so the whole key is available and the appeal can be to `KeyUnique` instead.  The only
cost is that the key's head is `mkRecName (D.types.getD j default).name` while the pattern
carries `mkRecName T.name`, so the two `types[j]? = some T` hypotheses have to be threaded in.
**They are already present at the sole call site** (`Pat.iota_data_uniq`, `PatternRules.lean`
line 1005, which passes exactly `hTj` and `hTj'` to `VInductDecl'.iotaRule_inj` on the very
next line), so this is a hypothesis reshuffle inside one file and not a new obligation. -/

theorem Pat.iota_rule_uniq_keyUnique {env : VEnv} (hU : env.KeyUnique)
    {D D' : VInductDecl'} {j q j' q' : Nat} {T T' : VIndType} {C C' : VIndCtor}
    (hTj : D.types[j]? = some T) (hTj' : D'.types[j']? = some T')
    (hdf : env.defeqs (D.iotaRule j q C)) (hdf' : env.defeqs (D'.iotaRule j' q' C'))
    (hp : D.iotaPat T C = D'.iotaPat T' C') :
    D.iotaRule j q C = D'.iotaRule j' q' C' := by
  obtain ⟨hrec, -, hname, -⟩ := VInductDecl'.iotaPat_inj hp
  refine hU _ _ hdf hdf' ?_
  rw [VInductDecl'.key_iotaRule, VInductDecl'.key_iotaRule, D.getD_types hTj,
    D'.getD_types hTj', hrec, hname]

/-- Regression: the statement `PatternRules.lean` proves today is an instance of the one
above, so replacing `WF.keyMajorUnique` by `WF.keyUnique` there loses nothing. -/
theorem Pat.iota_rule_uniq_keyUnique' {env : VEnv} (henv : env.WF)
    {D D' : VInductDecl'} {j q j' q' : Nat} {T T' : VIndType} {C C' : VIndCtor}
    (hTj : D.types[j]? = some T) (hTj' : D'.types[j']? = some T')
    (hdf : env.defeqs (D.iotaRule j q C)) (hdf' : env.defeqs (D'.iotaRule j' q' C'))
    (hp : D.iotaPat T C = D'.iotaPat T' C') :
    D.iotaRule j q C = D'.iotaRule j' q' C' :=
  Pat.iota_rule_uniq_keyUnique henv.keyUnique hTj hTj' hdf hdf' hp

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
`VEnv.WF'.keys` cannot be extended to a nested step by any argument whatever: its conclusion
is false there.  This is the statement `docs/handoff-inductive-add.md` §5.3 recorded as an
argument gap; it is a refutation of the invariant. -/
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

end VEnv

/-- The renamed recursor of a member is one of the *recursor* constants the step declares —
`VInductDecl'.recName_mem_allNamesCR` refined to the stage that declares it. -/
theorem VInductDecl'.recName_mem_recConstsR (D : VInductDecl') (R : VIndRestore) {j : Nat}
    {T : VIndType} (hT : D.types[j]? = some T) :
    R.recName (Lean.mkRecName (D.types.getD j default).name)
      ∈ (D.recConstsR R).map (·.1) := by
  rw [VInductDecl'.getD_types hT, VInductDecl'.recConstsR, List.map_map]
  exact List.mem_map.2 ⟨(T, j), List.mem_zipIdx_iff_getElem?.2 hT, rfl⟩

/-- A **non-companion** member's restored constructor name is one of the constructor
constants the step declares. -/
theorem VInductDecl'.ctorName_mem_ctorConstsCR (D : VInductDecl') (R : VIndRestore)
    (K : List Lean.Name) {j : Nat} {C : VIndCtor} (hm : (j, C) ∈ D.ctorsAll)
    (hK : (D.types.getD j default).name ∉ K) :
    R.ctorName C.name ∈ (D.ctorConstsCR R K).map (·.1) := by
  rw [VInductDecl'.ctorConstsCR]
  refine List.mem_map.2 ⟨(R.ctorName C.name, ⟨D.uvars, C.typeR D R j⟩),
    List.mem_filterMap.2 ⟨(j, C), hm, ?_⟩, rfl⟩
  simp only [if_neg hK]

/-- **The restoration separates the block's own ι-rules.**

A purely syntactic property of `R` and `D`: no two entries of `ctorsAll` are given the same
(renamed recursor, restored constructor) pair.  It is what `KeyUnique` needs *within* the
block, and it is `decide`-able at a concrete block — §3.3 discharges it at both nested
witnesses.

It is also derivable rather than assumed, from the two `addConstList` successes plus
`Faithful.ctors_complete`: the renamed recursor names are `Nodup` because
`addConstList (D.recConstsR R)` succeeded, which separates different members; within one
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

namespace VEnv

/-- **The nested arm.**  `KeysDeclared`, `KeyHeadDelta` and `KeyUnique` all survive a nested
declaration step.  Compare `VEnv.keys_induct`, whose third conclusion — `KeyMajorUnique` —
is *false* here (`InductiveDeclExamples.nfn_keyMajorUnique_false`). -/
theorem keysR_induct {env env' : VEnv} {D : VInductDecl'} {K : List Lean.Name}
    {R : VIndRestore} {npJ : Nat → Nat}
    (hR : env.addInductR D K R = some env')
    (hf : R.Faithful D env K npJ) (hd : R.KeysDistinct D)
    (ih : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyUnique) :
    env'.KeysDeclared ∧ env'.KeyHeadDelta ∧ env'.KeyUnique := by
  obtain ⟨e1, e2, e3, h1, h2, h3, rfl⟩ := VEnv.addInductR_stages hR
  have hdefeqs : e3.defeqs = env.defeqs := by
    rw [addConstList_defeqs h3, addConstList_defeqs h2, addConstList_defeqs h1]
  have hle : env ≤ e3 :=
    ((addConstList_le h1).trans (addConstList_le h2)).trans (addConstList_le h3)
  have hrecfresh : ∀ n ∈ (D.recConstsR R).map (·.1), ¬ env.contains n := by
    rintro n hn ⟨x, hx⟩
    have := (addConstList_le h2).constants ((addConstList_le h1).constants hx)
    rw [(addConstList_fresh h3).1 n hn] at this; exact absurd this nofun
  have hctorfresh : ∀ n ∈ (D.ctorConstsCR R K).map (·.1), ¬ env.contains n := by
    rintro n hn ⟨x, hx⟩
    have := (addConstList_le h1).constants hx
    rw [(addConstList_fresh h2).1 n hn] at this; exact absurd this nofun
  have hrecdecl : ∀ n ∈ (D.recConstsR R).map (·.1), e3.contains n := by
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
  refine keysU_addDefEqList_notDelta (D.iotaRulesR R) (keysU_mono hdefeqs hle ih)
    not_isDeltaRule_iotaRulesR ?_ ?_ ?_ (D.iotaRulesR_pairwise_key R hd)
  · -- hdecl
    intro df hdf n hn
    obtain ⟨j, C, hm, hk⟩ := VInductDecl'.mem_iotaRulesR hdf
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
    obtain ⟨j, C, hm, hk⟩ := VInductDecl'.mem_iotaRulesR hdf
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
    obtain ⟨j, C, hm, hk⟩ := VInductDecl'.mem_iotaRulesR hdf
    obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hm
    exact hrecfresh _ (D.recName_mem_recConstsR R hT)
      (ih.1 df' hdf' _ (by rw [← hkeq, hk]; exact List.mem_cons_self))

/-- The same for the packaged step `VEnv.AddNestedStep`, which is the premise the
`inductNested` rule of `Theory/Typing/Env.lean` would take. -/
theorem keys_addNestedStep {env env' : VEnv} {D : VInductDecl'} {K : List Lean.Name}
    {R : VIndRestore} (hs : VEnv.AddNestedStep env D K R env') (hd : R.KeysDistinct D)
    (ih : env.KeysDeclared ∧ env.KeyHeadDelta ∧ env.KeyUnique) :
    env'.KeysDeclared ∧ env'.KeyHeadDelta ∧ env'.KeyUnique :=
  let ⟨_, _, _, _, hf, hadd⟩ := hs
  keysR_induct hadd hf hd ih

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

* `KeyMajorUnique` — Part II's third invariant, and the one `VEnv.WF'.keys` currently proves —
  is **false**;
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
  obtain ⟨npJ, hwf, hcan, hoi, hf, hadd⟩ := hs
  exact ⟨env₂, env₃, h, ⟨npJ, hwf, hcan, hoi, hf, hadd⟩, nfn_keyMajorUnique_false h hadd,
    fun ih => VEnv.keysR_induct hadd hf nfnRestore_keysDistinct ih⟩

end InductiveDeclExamples

end Lean4Lean
