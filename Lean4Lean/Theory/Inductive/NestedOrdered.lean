import Lean4Lean.Theory.Inductive.NestedHead

/-!
# `Ordered` for a nested step: the obligation, factored

`VEnv.Ordered` (`Theory/Typing/Lemmas.lean`) is what `VEnv.WF.ordered`
(`Theory/Typing/EnvLemmas.lean`) extracts from `VEnv.WF`, and it records that **every constant
the environment holds had a well-formed type at the moment it was declared** and every
definitional equation was well formed when it was added.  So the moment `VDecl.WF` gains the
nested rule (`Theory/Typing/Env.lean`), `VEnv.WF.ordered`'s new arm needs

    env.Ordered → env.addInductR D K R = some env' → env'.Ordered

and *that* — not the declaration history, and not the constant map — is what actually stands
between here and the rule.  It is a theorem about the **restored** types: `addInductR`
declares a user constructor at `C.typeR D R j`, in which a field that the auxiliary block
stored as `_nested.List_1 α` has been rewritten back to `List (Tree α)`, and it declares the
recursors at `D.recTypeR R j`.  Neither is a consequence of `D.WF env`, which is a statement
about the *auxiliary* block's own stored types.

This file does the part that is bookkeeping and names the part that is not.
`VEnv.addInductR_ordered` reduces the conclusion to four staged obligations, in the shape
`VInductDecl'.addInduct'_ordered` uses for the non-nested case, and `addInductR_ordered'`
discharges the first of the four outright.  What remains is three statements, listed at
`addInductR_ordered'`.
-/

namespace Lean4Lean
namespace VEnv

open VInductDecl' (typeConstsC ctorConstsCR recConstsR allConstsCR)

variable {env env' : VEnv} {D : VInductDecl'} {K : List Lean.Name} {R : VIndRestore}

/-- The three constant stages of `VEnv.addInductR`, then the rule fold.  This is
`VEnv.addInduct'_stages` for the restored constant lists; the proof is `addConstList_append`
twice, since `allConstsCR` is an append of three. -/
theorem addInductR_stages (h : env.addInductR D K R = some env') :
    ∃ e₁ e₂ e₃, env.addConstList (D.typeConstsC K) = some e₁ ∧
      e₁.addConstList (D.ctorConstsCR R K) = some e₂ ∧
      e₂.addConstList (D.recConstsR R) = some e₃ ∧ env' = e₃.addIndRulesR D R := by
  rw [VEnv.addInductR, Option.map_eq_some_iff] at h
  obtain ⟨e₃, h1, rfl⟩ := h
  rw [VInductDecl'.allConstsCR, VEnv.addConstList_append, Option.bind_eq_some_iff] at h1
  obtain ⟨e₂, h12, h3⟩ := h1
  rw [VEnv.addConstList_append, Option.bind_eq_some_iff] at h12
  obtain ⟨e₁, h1, h2⟩ := h12
  exact ⟨e₁, e₂, e₃, h1, h2, h3, rfl⟩


/-- …and conversely, the stages compose. -/
theorem addInductR_of_stages {e₁ e₂ e₃ : VEnv}
    (h1 : env.addConstList (D.typeConstsC K) = some e₁)
    (h2 : e₁.addConstList (D.ctorConstsCR R K) = some e₂)
    (h3 : e₂.addConstList (D.recConstsR R) = some e₃) :
    env.addInductR D K R = some (e₃.addIndRulesR D R) := by
  rw [VEnv.addInductR, VInductDecl'.allConstsCR, VEnv.addConstList_append,
    VEnv.addConstList_append, h1]
  simp only [Option.bind_some, h2, h3, Option.map_some]

/-- **`addInductR` preserves `Ordered`, modulo four staged obligations.**

The shape is `VInductDecl'.addInduct'_ordered`'s, and for the same reason: a constructor's
stored type mentions the block's own type constants, and an ι-rule mentions the recursors, so
neither obligation can be stated at `env`.  Each is stated at the environment the previous
stage produced. -/
theorem addInductR_ordered (henv : env.Ordered)
    (htys : ∀ c ∈ D.typeConstsC K, c.2.WF env)
    (hctors : ∀ {e₁ : VEnv}, env.addConstList (D.typeConstsC K) = some e₁ →
      ∀ c ∈ D.ctorConstsCR R K, c.2.WF e₁)
    (hrecs : ∀ {e₁ e₂ : VEnv}, env.addConstList (D.typeConstsC K) = some e₁ →
      e₁.addConstList (D.ctorConstsCR R K) = some e₂ → ∀ c ∈ D.recConstsR R, c.2.WF e₂)
    (hrules : ∀ {e₁ e₂ e₃ : VEnv}, env.addConstList (D.typeConstsC K) = some e₁ →
      e₁.addConstList (D.ctorConstsCR R K) = some e₂ →
      e₂.addConstList (D.recConstsR R) = some e₃ → ∀ df ∈ D.iotaRulesR R, df.WF e₃)
    (he : env.addInductR D K R = some env') : env'.Ordered := by
  obtain ⟨e₁, e₂, e₃, h1, h2, h3, rfl⟩ := addInductR_stages he
  have o1 := VEnv.addConstList_ordered henv htys h1
  have o2 := VEnv.addConstList_ordered o1 (hctors h1) h2
  have o3 := VEnv.addConstList_ordered o2 (hrecs h1 h2) h3
  exact VEnv.addDefEqList_ordered _ _ o3 (hrules h1 h2 h3)

/-- **The first obligation is free.**  The type constants a nested step declares are a
sublist of the ones `addInduct'` declares — `typeConstsC` only *removes* the companion
members — and their stored types are the auxiliary block's own, which `D.WF env` covers
verbatim.  So this half of `addIndTypes_ordered` transfers with no restoration content at
all. -/
theorem addInductR_typeConstsC_wf (h : D.WF env) : ∀ c ∈ D.typeConstsC K, c.2.WF env := by
  intro c hc
  rw [VInductDecl'.typeConstsC, List.mem_filterMap] at hc
  obtain ⟨c₀, hc₀, hce⟩ := hc
  split at hce
  · exact absurd hce nofun
  · cases hce
    simp only [VInductDecl'.typeConsts, List.mem_map] at hc₀
    obtain ⟨T, hT, rfl⟩ := hc₀
    exact (h.types T hT).constant_wf

/-! ### An audit of the hypotheses, and a correction to the framing

The previous revision of `docs/handoff-inductive-add.md` said the three obligations below
"are to be discharged **from `Faithful` plus `D.WF env`**".  That is **false**, and not
narrowly: `VIndRestore.Faithful`'s three clauses are *all* guarded by `T.name ∈ K`, so they
say nothing whatever about the members the step declares.  At `K = []` every clause is
vacuous — `VIndRestore.faithful_of_nil` (`Theory/Inductive/Restore.lean`) — and a restoration that renames the block's own
member to an arbitrary constant is `Faithful`.  `VEnv.addInductR` still succeeds at it (its
success depends only on freshness and `Nodup` of the names), so the constructor constants it
declares carry result types headed by that constant, and obligation **(A)** fails at the very
first one.  `InductiveDeclExamples.pfnJunk_would_have_passed`
(`Theory/Inductive/NestedBuild.lean`) is that configuration at a real block.

The two hypotheses that could have excluded it, `D.WF env` and `D.Canonical`, **do not
mention `R` at all**, so no strengthening of them could.

The repair is `VIndRestore.OwnId` (`Theory/Inductive/Restore.lean`): *off `K`, the
restoration renames nothing and re-instantiates nothing*.  It is now a conjunct of
`VEnv.AddNested`, hence of `VEnv.AddNestedStep`, hence of the `inductNested` rule's premise;
`VInductDecl'.Built` carries it too, so both end-to-end witnesses supply it
(`ntreeRestore_ownId`, `nfnRestore_ownId`) and `VEnv.AddNested_nil` still holds at
`idRestore` (`VInductDecl'.idRestore_ownId`).  `VIndRestore.OwnId.tyAppR_eq` is what it buys:
at a declared member the restored head **is** `VInductDecl'.tyApp`, so restoration is
invisible in exactly the positions the step declares under their own names.

So the three obligations below are to be discharged from **`OwnId` + `Faithful` + `D.WF env`**,
and `hown` is threaded through `addInductR_ordered'` to record that. -/

/-- **What is actually left, stated once.**

Reading the hypotheses: **(A)** a *declared* constructor's **restored** stored type is a type
in the environment carrying the step's type constants; **(B)** each **renamed** recursor's
**restored** type is a type in the environment carrying those and the constructors; **(C)**
each **restored** ι-rule is a well-formed definitional equation there.

These are the nested-soundness content, and none of them follows from `D.WF env`: `D.WF` is a
statement about the auxiliary block's *own* stored types, in which the companion member is a
block constant, whereas `typeR`/`recTypeR`/`iotaRulesR` have rewritten every companion head
back to the block the environment really holds.  `VIndRestore.Faithful`
(`Theory/Inductive/Restore.lean`) is the hypothesis that licenses that rewrite —
`ty_agree`/`ctor_agree` say the companion member *is* the declared block instantiated — so the
three obligations are to be discharged from `OwnId` + `Faithful` + `D.WF env` — see the audit
above for why `Faithful` alone is not enough, and why that was a defect in the statement
rather than a gap in a proof.

Given them, `Ordered` follows; that is all this theorem says, and it says it so that the
remaining work is three named statements rather than a rule with no proof. -/
theorem addInductR_ordered' (henv : env.Ordered) (h : D.WF env) (hown : R.OwnId D K)
    (hctors : ∀ {e₁ : VEnv}, env.addConstList (D.typeConstsC K) = some e₁ →
      ∀ c ∈ D.ctorConstsCR R K, c.2.WF e₁)
    (hrecs : ∀ {e₁ e₂ : VEnv}, env.addConstList (D.typeConstsC K) = some e₁ →
      e₁.addConstList (D.ctorConstsCR R K) = some e₂ → ∀ c ∈ D.recConstsR R, c.2.WF e₂)
    (hrules : ∀ {e₁ e₂ e₃ : VEnv}, env.addConstList (D.typeConstsC K) = some e₁ →
      e₁.addConstList (D.ctorConstsCR R K) = some e₂ →
      e₂.addConstList (D.recConstsR R) = some e₃ → ∀ df ∈ D.iotaRulesR R, df.WF e₃)
    (he : env.addInductR D K R = some env') : env'.Ordered :=
  addInductR_ordered henv (addInductR_typeConstsC_wf h) hctors hrecs hrules he

/-- **Conservativity: at the identity restoration the three obligations are the ones
`addInduct'` already discharges.**  With no companion members and `D.Canonical`, the restored
constant lists *are* `addInduct'`'s, so `addInductR_ordered'` collapses to
`VInductDecl'.addInduct'_ordered` — nothing has been strengthened, and the three open
obligations are genuinely about the *restoration* rather than about inductives. -/
theorem addInductR_ordered_nil (henv : env.Ordered) (h : D.WF env) (hc : D.Canonical)
    (hrec : ∀ {env₁ env₂ : VEnv}, env.addIndTypes D = some env₁ →
      env₁.addIndCtors D = some env₂ → ∀ c ∈ D.recConsts, VConstant.WF env₂ c.2)
    (hrules : ∀ {env₁ env₂ env₃ : VEnv}, env.addIndTypes D = some env₁ →
      env₁.addIndCtors D = some env₂ → env₂.addIndRecs D = some env₃ →
      ∀ df ∈ D.iotaRules, df.WF env₃)
    (he : env.addInductR D [] D.idRestore = some env') : env'.Ordered :=
  VInductDecl'.addInduct'_ordered henv h hrec hrules
    (by rwa [VEnv.addInductR_eq_addInduct' env hc] at he)

/-! ## A second transcription that does not go through: `DeltaUnique`'s freshness

`Theory/Typing/DeltaUnique.lean`'s `keys_induct` — the `induct` arm of `VEnv.WF'.keys` — turns
on `hfresh`:

> every name occurring in the key of a rule the step emits is **absent** from `env`.

For `addInduct'` that is immediate: an ι-rule's key is `[I_j.rec, C.name]`
(`VInductDecl'.key_iotaRule`) and both are names the step itself declares.  For a nested step
it is **false**, and not marginally: the key of a *companion* member's ι-rule is
`[R.recName I_j.rec, R.ctorName C.name]` (`VInductDecl'.key_iotaRuleR`), whose second component
is the constructor of the block the environment **already holds** — `PFn.mk`, `List.cons` — and
`VIndRestore.Faithful.ctor_agree` says so in as many words.  That is the theorem below.

So the nested arm of `keys_induct` cannot be a transcription; the freshness it can use is the
*head* of the key only.  That is available (`VInductDecl'.recName_mem_allNamesCR` puts the
renamed recursor among the step's own constants, and `addConstList` succeeded, so it is fresh),
but it is a different argument.  Recording it here because it is invisible from the
`addInduct'` side.

**CORRECTION (2026-08-31).**  This paragraph used to end "and because it is the second of the two
obligations — after `addInductR_ordered'` — that the `inductNested` rule waits on".  That is no
longer true, and the sentence above ("cannot be a transcription; the freshness it can use is the
head of the key only") is also too optimistic about what survives.
`Theory/Inductive/NestedKeys.lean` settled the whole question:

* `VEnv.KeyMajorUnique` is not merely hard to re-prove for a nested step, it is **false** —
  `nfn_keyMajorUnique_false` exhibits `[PFn.rec, PFn.mk]` against `[NFn.rec_1, PFn.mk]`, two
  distinct rules with one major.  So no proof was ever going to work.
* The replacement `VEnv.KeyUnique` (the *whole* key determines the rule) is preserved by a nested
  step — `VEnv.keysR_induct`, from `Faithful` plus `VIndRestore.KeysDistinct` — and is not
  refuted by the same witness (`nfn_keys_ne`).
* The sole consumer is re-proved from it: `Pat.iota_rule_uniq_keyUnique`.

**LANDED.**  `WF'.keys` now carries `KeysDeclared ∧ KeyHeadDelta ∧ KeyUnique`, and
`keys_induct`'s key fact is discharged from the freshness of the key's *head* only — so the
non-nested arm and `keysR_induct` finally have the same shape.  `KeyMajorUnique` survives as a
definition because the refutations are statements *about* it, but nothing derives it from
`VEnv.WF` any more.

One correction to what this paragraph predicted: it was **not** two mechanical edits.
`keysU_addDefEq` and `keysU_addDefEqs` had to be written, and the first needs a hypothesis the
`KeyMajorUnique` version did not — `df.key ≠ []`, since with an empty key the `∀ n ∈ df.key`
premises say nothing and `KeyUnique` cannot be established.

So `addInductR_ordered'`'s three obligations — `hctors`, `hrecs`, `hrules` — are now the *only*
thing the `inductNested` rule waits on. -/

/-- **A companion ι-rule's major name is already declared.**  Directly `Faithful.ctor_agree`:
the restoration presents the companion's constructors as constants the environment holds, and
`key_iotaRuleR` puts exactly that name in the rule's key. -/
theorem iotaRulesR_major_not_fresh {env : VEnv} {D : VInductDecl'} {K : List Lean.Name}
    {R : VIndRestore} {npJ : Nat → Nat} {j : Nat} {T : VIndType} {C : VIndCtor}
    (hf : R.Faithful D env K npJ) (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hC : C ∈ T.ctors) : env.contains (R.ctorName C.name) :=
  let ⟨ci, hci, _⟩ := hf.ctor_agree j T hT hK C hC; ⟨ci, hci⟩

/-- …and it really is in the key of a rule the step emits, so the clash is not hypothetical. -/
theorem mem_key_iotaRuleR_major {D : VInductDecl'} {R : VIndRestore} (j q : Nat)
    (C : VIndCtor) : R.ctorName C.name ∈ (D.iotaRuleR R j q C).key := by
  rw [D.key_iotaRuleR R j q C]; exact List.mem_cons_of_mem _ List.mem_cons_self

end VEnv
end Lean4Lean
