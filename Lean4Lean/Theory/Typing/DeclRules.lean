import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# What a definitional-equality rule of a well-formed environment can look like

`VEnv.WF` (`Theory/Typing/Env.lean`) builds an environment from a list of `VDecl` steps.
Only four of those steps add anything to `env.defeqs`, and each adds rules of one fixed
shape:

| step | rule | `lhs` |
|---|---|---|
| `.def v` / `.unsafeDef vs` | `v.toDefEq` | `.const v.name (VLevel.params _)` |
| `.quot` | `quotDefEq` | a six-fold `.lam` |
| `.induct D` | some `df ∈ D.iotaRules` | `mkLams (D.iotaCtx C) (D.iotaLhs j C)` |

`VEnv.WF.defeq_isDeclRule` below is that table, machine-checked.  It is the missing
"⊆" direction: `Theory/Inductive/Lemmas.lean` and `Theory/Typing/QuotLemmas.lean` prove
that each declared rule *is* in the environment; nothing until now proved that no other
rule is.

The immediate consumers are the `extra` cases of the Π/sort inversion inductions
(`Theory/Typing/Injectivity.lean`, and every route to them): a rule's left-hand side is
never a `.sort` and never a `.forallE`, so `IsDefEq.extra` can never be the last step of a
derivation whose left endpoint is one.

This is also the first half of soundness-ledger item **M2** (deriving `VEnv.RuleFreeHead`
from `VEnv.WF`).  The second half — that a *given* constant name heads none of the three
kinds of rule — needs a signature invariant relating names to their declaring step, and is
deliberately not attempted here.

## Relation to `Theory/Typing/PatternRules.lean`

`VEnv.WF.ruleShape` there proves a **strictly richer** version of `WF.defeq_isDeclRule`:
its `VEnv.RuleShape` carries closedness, arities, the recursor/constructor constants and
the staging environments, which is what a `Params` instance needs.  This file exists only
because `Injectivity.lean` cannot afford that import: `PatternRules` pulls in
`PatternDecode`, `DeltaUnique` and `Inductive/StructureClosed`, and `Injectivity` sits
under `UniqueTyping` and hence under all of `Lean4Lean/Verify`.  If the two are ever
consolidated, `VEnv.RuleShape` is the one to keep and `VDefEq.IsDeclRule` is the one to
delete — the corollaries at the bottom of this file are the only part with no counterpart
there.

The three plumbing lemmas `addConst_defeqs`, `addConstList_defeqs` and
`addConsts_defeqs` used to be duplicated here under an `_eq` suffix, because
`DeltaUnique.lean` and `Verify/TypeChecker/Reduce.lean` each declared their own copy and a
downstream file that saw both would fail to compile.  All copies now live in
`Theory/Typing/EnvLemmas.lean`, which every side already imports.
-/

namespace Lean4Lean

/-- The three shapes a `VDefEq` can have in a `VEnv.WF` environment. -/
inductive VDefEq.IsDeclRule : VDefEq → Prop
  /-- a δ-rule, from a `.def` or `.unsafeDef` step -/
  | delta (v : VDefVal) : VDefEq.IsDeclRule v.toDefEq
  /-- the quotient computation rule, from a `.quot` step -/
  | quot : VDefEq.IsDeclRule quotDefEq
  /-- an ι-rule of some inductive block, from an `.induct` step -/
  | iota (D : VInductDecl') {df : VDefEq} (h : df ∈ D.iotaRules) : VDefEq.IsDeclRule df

namespace VExpr

/-- An application spine is either its own head or an `.app`. -/
theorem mkApp_self_or_app : ∀ (as : List VExpr) (f : VExpr),
    f.mkApp as = f ∨ ∃ g a, f.mkApp as = .app g a
  | [], _ => .inl rfl
  | a :: as, f => .inr <| by
    rcases mkApp_self_or_app as (f.app a) with h | ⟨g, b, h⟩
    · exact ⟨f, a, h⟩
    · exact ⟨g, b, h⟩

/-- A λ-telescope is either its own body or a `.lam`. -/
theorem mkLams_self_or_lam : ∀ (As : List VExpr) (b : VExpr),
    mkLams As b = b ∨ ∃ A b', mkLams As b = .lam A b'
  | [], _ => .inl rfl
  | _ :: _, _ => .inr ⟨_, _, rfl⟩

/-- The shape of every rule left-hand side declared by the abstract theory: a constant
applied to a spine, under a (possibly empty) λ-telescope. -/
theorem mkLams_mkApp_shape (As : List VExpr) (c : Lean.Name) (ls : List VLevel)
    (as : List VExpr) :
    (∃ c' ls', mkLams As ((VExpr.const c ls).mkApp as) = .const c' ls') ∨
    (∃ f a, mkLams As ((VExpr.const c ls).mkApp as) = .app f a) ∨
    (∃ A b, mkLams As ((VExpr.const c ls).mkApp as) = .lam A b) := by
  cases As with
  | cons => exact .inr (.inr ⟨_, _, rfl⟩)
  | nil =>
    rcases mkApp_self_or_app as (VExpr.const c ls) with h | ⟨g, a, h⟩
    · exact .inl ⟨c, ls, by simpa [mkLams] using h⟩
    · exact .inr (.inl ⟨g, a, by simpa [mkLams] using h⟩)

end VExpr

namespace VEnv

variable {env env' : VEnv} {df : VDefEq}

/-! ## Reading off `defeqs` through each environment extension -/

theorem addDefEq_defeqs_iff {d} : (env.addDefEq d).defeqs df ↔ df = d ∨ env.defeqs df := .rfl

/-- The converse of `addDefEqList_defeqs`: the fold adds exactly `dfs`. -/
theorem addDefEqList_defeqs_iff : ∀ (dfs : List VDefEq) (env : VEnv),
    (dfs.foldl VEnv.addDefEq env).defeqs df ↔ df ∈ dfs ∨ env.defeqs df
  | [], _ => by simp
  | d :: dfs, env => by
    show (dfs.foldl VEnv.addDefEq (env.addDefEq d)).defeqs df ↔ _
    rw [addDefEqList_defeqs_iff dfs (env.addDefEq d), addDefEq_defeqs_iff]
    simp only [List.mem_cons]
    constructor
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)

/-- The converse of `VEnv.addDefEqs`' half: an `.unsafeDef` block adds exactly its own
δ-rules. -/
theorem addDefEqs_defeqs_iff : ∀ (cis : List VDefVal) (env : VEnv),
    (env.addDefEqs cis).defeqs df ↔ (∃ ci ∈ cis, df = ci.toDefEq) ∨ env.defeqs df
  | [], _ => by simp [VEnv.addDefEqs]
  | ci :: cis, env => by
    show ((env.addDefEq ci.toDefEq).addDefEqs cis).defeqs df ↔ _
    rw [addDefEqs_defeqs_iff cis (env.addDefEq ci.toDefEq), addDefEq_defeqs_iff]
    constructor
    · rintro (⟨c, hc, rfl⟩ | rfl | h)
      · exact .inl ⟨c, .tail _ hc, rfl⟩
      · exact .inl ⟨ci, .head _, rfl⟩
      · exact .inr h
    · rintro (⟨c, hc, rfl⟩ | h)
      · cases hc with
        | head => exact .inr (.inl rfl)
        | tail _ hc => exact .inl ⟨_, hc, rfl⟩
      · exact .inr (.inr h)

theorem addIndRules_defeqs_iff {D : VInductDecl'} :
    (env.addIndRules D).defeqs df ↔ df ∈ D.iotaRules ∨ env.defeqs df :=
  addDefEqList_defeqs_iff ..

theorem addInduct'_defeqs_iff {D : VInductDecl'} (h : env.addInduct' D = some env') :
    env'.defeqs df ↔ df ∈ D.iotaRules ∨ env.defeqs df := by
  rw [addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  rw [addIndRules_defeqs_iff, addConstList_defeqs h1]

theorem addQuot_defeqs_iff (h : env.addQuot = some env') :
    env'.defeqs df ↔ df = quotDefEq ∨ env.defeqs df := by
  unfold VEnv.addQuot at h
  obtain ⟨e1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e2, h2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e3, h3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e4, h4, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  rw [addDefEq_defeqs_iff, addConst_defeqs h4, addConst_defeqs h3,
    addConst_defeqs h2, addConst_defeqs h1]

/-! ## The classification -/

/-- **Every definitional-equality rule of a well-formed environment is a declaration
rule.** -/
theorem WF'.defeq_isDeclRule {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    ∀ {df}, env.defeqs df → df.IsDeclRule := by
  induction H with
  | empty => exact nofun
  | decl hd _ IH =>
    intro df h
    cases hd with
    | «axiom» _ h2 | «opaque» _ h2 => exact IH (addConst_defeqs h2 ▸ h)
    | «example» _ => exact IH h
    | «def» _ h2 =>
      rcases addDefEq_defeqs_iff.1 h with rfl | h
      · exact .delta _
      · exact IH (addConst_defeqs h2 ▸ h)
    | unsafeDef _ h2 =>
      rcases (addDefEqs_defeqs_iff _ _).1 h with ⟨_, _, rfl⟩ | h
      · exact .delta _
      · exact IH (addConsts_defeqs h2 ▸ h)
    | quot _ h2 =>
      rcases (addQuot_defeqs_iff h2).1 h with rfl | h
      · exact .quot
      · exact IH h
    | induct _ h2 =>
      rcases (addInduct'_defeqs_iff h2).1 h with h | h
      · exact .iota _ h
      · exact IH h

theorem WF.defeq_isDeclRule (henv : env.WF) (h : env.defeqs df) : df.IsDeclRule :=
  let ⟨_, H⟩ := henv; H.defeq_isDeclRule h

end VEnv

/-! ## Consequences: which head constructor a rule's `lhs` can have -/

namespace VDefEq

variable {df : VDefEq}

/-- A rule's left-hand side is headed by `.const`, `.app` or `.lam` — never by `.bvar`,
`.sort` or `.forallE`. -/
theorem IsDeclRule.lhs_shape (h : df.IsDeclRule) :
    (∃ c ls, df.lhs = .const c ls) ∨ (∃ f a, df.lhs = .app f a) ∨ ∃ A b, df.lhs = .lam A b := by
  cases h with
  | delta v => exact .inl ⟨_, _, rfl⟩
  | quot => exact .inr (.inr ⟨_, _, rfl⟩)
  | iota D h =>
    simp only [VInductDecl'.iotaRules, List.mem_map] at h
    obtain ⟨⟨⟨j, C⟩, q⟩, -, rfl⟩ := h
    exact VExpr.mkLams_mkApp_shape (D.iotaCtx C) _ _ _

theorem IsDeclRule.lhs_ne_sort (h : df.IsDeclRule) (u : VLevel) : df.lhs ≠ .sort u := by
  rcases h.lhs_shape with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> exact nofun

theorem IsDeclRule.lhs_ne_forallE (h : df.IsDeclRule) (A B : VExpr) :
    df.lhs ≠ .forallE A B := by
  rcases h.lhs_shape with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> exact nofun

/-- Non-vacuity regression: `IsDeclRule` is not the trivially-true predicate.  A rule
rewriting one sort to another satisfies `VDefEq.WF` in a suitable environment but is not a
declaration rule, so `WF.defeq_isDeclRule` above really does rule something out. -/
example : ¬ VDefEq.IsDeclRule ⟨0, .sort .zero, .sort .zero, .sort (.succ .zero)⟩ :=
  fun h => h.lhs_ne_sort _ rfl

end VDefEq

namespace VEnv

variable {env : VEnv} {df : VDefEq}

/-- **No rule rewrites a sort.**  So `IsDefEq.extra` can never be the last step of a
derivation whose left endpoint is a `.sort`. -/
theorem WF.instL_lhs_ne_sort (henv : env.WF) (h : env.defeqs df) (ls : List VLevel)
    (u : VLevel) : df.lhs.instL ls ≠ .sort u := by
  rcases (henv.defeq_isDeclRule h).lhs_shape with ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;>
    rw [e] <;> exact nofun

/-- **No rule rewrites a Π-type.** -/
theorem WF.instL_lhs_ne_forallE (henv : env.WF) (h : env.defeqs df) (ls : List VLevel)
    (A B : VExpr) : df.lhs.instL ls ≠ .forallE A B := by
  rcases (henv.defeq_isDeclRule h).lhs_shape with ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;>
    rw [e] <;> exact nofun

end VEnv
