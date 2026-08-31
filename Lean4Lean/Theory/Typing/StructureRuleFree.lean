import Lean4Lean.Theory.Typing.DeltaUnique
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Inductive.StructureClosed

/-!
# `VEnv.RuleFreeHead` at a structure name, from `VEnv.WF` and `IsStructure` alone

`VEnv.RuleFreeHead env S` (`Theory/Typing/Injectivity.lean`) says that `S` heads no
definitional-equality rule of `env`.  It is the side condition of the whole
constant-application injectivity family — `IsDefEqU.const_app_inv`, `const_forallE_inv`,
`const_sort_inv`, `VEnv.ConstNoConf` — and therefore the live blocker of `TrProj.uniq` and
`TrProj.weak'_inv` (`Verify/Typing/Lemmas.lean`).

**It needs no strengthening of `VEnv.IsStructure`.**  Two earlier rounds concluded the
opposite, and the record should say why the conclusion was wrong rather than just replace it:

* `Theory/Typing/DeclRules.lean`'s header calls the missing half of ledger M2 "a signature
  invariant relating names to their declaring step" and declines it.  `TrProj.uniq`'s
  docstring then reasoned from `IsStructure.decl`'s `env₁ ≤ env` — correctly — that the
  hypothesis places no step of `env`'s *own* `WF` chain, so it cannot by itself rule out a
  δ-rule at `S`, and proposed strengthening `decl`.
* What both missed is that **the provenance argument had already been run**, in
  `Theory/Typing/DeltaUnique.lean` Part III, for exactly this name and by exactly the
  temporal route: `VEnv.WF.iotaTypeNotKey` says no rule of a well-formed environment has a
  *block type name* in its `VDefEq.key`.  Its `WF'` induction is where the "declaring step"
  information lives; `env₁ ≤ env` is not asked to carry it.

So the only gap was a **notational** one: the injectivity family speaks of
`VExpr.headConst?`, Part III speaks of `VDefEq.key`, and nothing related them.  §1 below is
that bridge — every declaration rule's left-hand side is `mkLams As ((.const d ls).mkApp as)`,
whose `headConst?` is `some d` and whose `key` begins with `d` — and §2 is the four-line
consequence.

`IsStructure` is therefore untouched, `IsStructure.mono` still holds with `env ≤ env'`
unchanged, and no construction site (`TypeChecker.Inner.inferProj.WF`, `TrExprS`'s `proj`
sites, `Verify/StructureBridge.lean`'s two bridges) acquires an obligation.  That matters
beyond convenience: `RuleFreeHead env S` is *anti*-monotone in `env`, so a field of
`IsStructure` implying it could not have coexisted with `IsStructure.mono` — see the
"polarity" note at `VEnv.IsStructure.ruleFreeHead` below.
-/

namespace Lean4Lean

/-! ## 1. `headConst?` and `VDefEq.key` agree at every declaration rule

Both instruments peel leading λs and then read the head of an application spine, but they do
it with different code (`Injectivity.lean` keeps a short import list and spells its own out),
and they *disagree* off the declaration shapes: at `.app (.lam _ (.const c _)) a`,
`headConst?` looks through the λ under the application and answers `some c`, while
`VDefEq.key`'s `peelLams`/`spine` pair answers `[]`.  No declaration rule has that shape —
every one is `mkLams As ((.const d ls).mkApp as)` — so the two agree where it matters, and
that hypothesis is what the lemmas below take. -/

/-- `headConst?` looks through a λ-telescope.

Named `_eq` because `Verify/Typing/ConstSpine.lean` already has this statement as
`VExpr.headConst?_mkLams`, and a `Theory/` file may not import a `Verify/` one — so the two
coexist rather than one being reused.  If `ConstSpine.lean`'s copy is ever moved down into
`Theory/`, delete this one. -/
theorem VExpr.headConst?_mkLams_eq : ∀ (As : List VExpr) (b : VExpr),
    (VExpr.mkLams As b).headConst? = b.headConst?
  | [], _ => rfl
  | _ :: As, b => by rw [VExpr.mkLams_cons]; exact VExpr.headConst?_mkLams_eq As b

/-- A constant applied to a spine has no leading λ to peel. -/
theorem VExpr.peelLams_snd_mkApp_const {d : Lean.Name} {ls : List VLevel} {as : List VExpr} :
    (VExpr.peelLams ((VExpr.const d ls).mkApp as)).2 = (VExpr.const d ls).mkApp as := by
  rcases VExpr.mkApp_self_or_app as (.const d ls) with h | ⟨g, a, h⟩ <;> rw [h] <;> rfl

/-- `VDefEq.key`, with the `let` expanded. -/
theorem VDefEq.key_eq (df : VDefEq) :
    df.key = (VExpr.headName (VExpr.peelLams df.lhs).2).toList ++
      (((VExpr.spine (VExpr.peelLams df.lhs).2).2.getLast?.bind VExpr.headName)).toList := rfl

/-- **The head of a declaration-shaped rule's key is its head constant.** -/
theorem VDefEq.mem_key_of_lhs_eq {df : VDefEq} {As as : List VExpr} {d : Lean.Name}
    {ls : List VLevel} (h : df.lhs = VExpr.mkLams As ((VExpr.const d ls).mkApp as)) :
    d ∈ df.key := by
  rw [VDefEq.key_eq, h, VExpr.peelLams_mkLams, VExpr.peelLams_snd_mkApp_const,
    VExpr.headName_mkApp]
  exact List.mem_append_left _ (List.mem_singleton_self _)

/-- The bridge, at one rule of the declaration shape: whatever `headConst?` reports is a key
name. -/
theorem VDefEq.mem_key_of_headConst? {df : VDefEq} {As as : List VExpr} {d : Lean.Name}
    {ls : List VLevel} (h : df.lhs = VExpr.mkLams As ((VExpr.const d ls).mkApp as))
    {c : Lean.Name} (hc : df.lhs.headConst? = some c) : c ∈ df.key := by
  rw [h, VExpr.headConst?_mkLams_eq, VExpr.headConst?_mkApp] at hc
  cases hc
  exact VDefEq.mem_key_of_lhs_eq h

/-- **`headConst?` lands in `key`, at every declaration rule.**  This is the translation
`Theory/Typing/DeltaUnique.lean` Part III was missing a consumer for.

The δ- and ι-cases go through the shape bridge above.  The quotient rule cannot: its λ-prefix
comes from the `vdefeq(...)` macro, so `mkLams ?As _` has no unifier-determined `?As`, and
`rfl` fails to see the shape (this is the one thing in this file that did not work first try).
It does not need the bridge — `key_quotDefEq` computes `quotDefEq.key` outright. -/
theorem VDefEq.IsDeclRule.headConst?_mem_key {df : VDefEq} (H : df.IsDeclRule)
    {c : Lean.Name} (hc : df.lhs.headConst? = some c) : c ∈ df.key := by
  cases H with
  | delta v => exact VDefEq.mem_key_of_headConst? (As := []) (as := []) rfl hc
  | quot =>
    have hq : quotDefEq.lhs.headConst? = some ``Quot.lift := rfl
    cases Option.some.inj (hq.symm.trans hc)
    rw [VEnv.key_quotDefEq]; exact List.mem_cons_self ..
  | iota D hmem =>
    obtain ⟨j, q, C, -, rfl⟩ := VInductDecl'.mem_iotaRules hmem
    exact VDefEq.mem_key_of_headConst? (As := D.iotaCtx C) rfl hc

/-! ## 2. The consequence -/

/-- **`RuleFreeHead` at a structure name.**  No definitional-equality rule of a well-formed
environment is headed by the name of a structure it declares.

Hypotheses: `VEnv.WF env` and `VEnv.IsStructure env S D T C` *as it stands*.  Nothing is
added to `IsStructure`, and that is not merely economy — it is forced.  `RuleFreeHead env S`
is **anti-monotone** in `env` (`env ≤ env'` may add a rule at `S`), so no monotone field of
`IsStructure` can imply it, and `IsStructure.mono` (`Theory/Inductive/Structure.lean`) is
monotone; a field placing the `.induct` step in `env`'s own chain would have had to break
`mono`, hence `TrProj.mono`, hence `TrExprS.mono` and its fifteen call sites.  Passing
`VEnv.WF env` instead is what keeps the anti-monotone conclusion consistent with the monotone
hypothesis: `env.addDefEq (δ-rule at S)` is `≥ env` but is not `WF`.

The work is all in `VEnv.WF.iotaTypeNotKey`: `S` is the name of `D`'s one type, `D`'s one
ι-rule is in `env` (`IsStructure.iotaDefeq`), so `S` is in no rule's key, so — by §1 — `S`
heads no rule. -/
theorem VEnv.IsStructure.ruleFreeHead {env : VEnv} {S : Lean.Name} {D : VInductDecl'}
    {T : VIndType} {C : VIndCtor} (henv : env.WF) (H : env.IsStructure S D T C) :
    env.RuleFreeHead S := by
  intro df hdf hhead
  have hname : (D.types.getD 0 default).name = S := by rw [H.types]; exact H.name
  exact hname ▸ henv.iotaTypeNotKey D 0 0 C H.iotaDefeq df hdf <|
    (henv.defeq_isDeclRule hdf).headConst?_mem_key hhead

/-! ## 3. Non-vacuity

The premises are satisfiable at a real structure environment and the conclusion has content
there: `Verify/Typing/Rigidity.lean`'s `barEnv_ruleFreeHead` proves `barEnv.RuleFreeHead
`Bar`` by a direct computation on `barEnv.defeqs`, and `barEnv_ruleFreeHead'` shows the
`Bar.rec` case is genuinely excluded — so `RuleFreeHead` is not the trivially-true predicate
at an environment holding an inductive block.  The regression below is the *other* direction:
that this lemma's conclusion is not vacuous because some rule of some well-formed environment
really is headed by a constant. -/

/-- Regression: `RuleFreeHead` is refutable, so §2 is not proving a tautology.  A δ-rule for
`v` is headed by `v.name`. -/
example (v : VDefVal) : ¬ (VEnv.empty.addDefEq v.toDefEq).RuleFreeHead v.name :=
  fun h => h v.toDefEq (.inl rfl) rfl

end Lean4Lean
