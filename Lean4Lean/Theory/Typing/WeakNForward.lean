import Lean4Lean.Theory.Typing.StrengthenVerdict

/-!
# Round 8 on the forward direction of `VEnv.IsDefEqU.weakN_iff`

Target: the `sorry` at `Theory/Typing/UniqueTyping.lean:193`, the **forward** half of

```
IsDefEqU.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2
```

under `henv : VEnv.WF env` and `hΓ : OnCtx Γ' (env.IsType U)`.  The reverse half is proved
(`IsDefEqU.weakN`).

**Status: neither closed nor refuted here.**  Rounds 1-7 are in `docs/handoff-weakn.md`; this
round's report is `docs/handoff-weaknforward.md`.  What this file adds is measurement, not a
proof: §1 the obligation with every abbreviation removed, §2 what the two hypotheses are
actually for, §4 a machine-checked **refutation of an informal claim about closed inhabitants
of `Sort (.param i)`** that a sibling stream's residue rests on, together with the discharge
clause that claim was blocking.

Nothing here reaches `sorryAx`.

## Routes already ruled out (enumerated before starting; see `docs/handoff-weakn.md`)

Direct induction on `IsDefEqU` (`trans` **is** the statement, `Strengthening.iff_trans`); the
typed form (`Strengthening.iff_typed`); a propagated/chain restatement; Church-Rosser and
`NormalEq` (circular through `ParRed.weakN_inv`, and `ParRedKWeakN.lean` §1 shows that entry is
the hole restated); `HeadReduction.lean`; a set model for the **proof** direction (vacuous over
an uninhabited entry); `VExpr.Skips`/`IsDefEq.skips` (downstream); the λ-form (needs
`forallE_inv`, `sorryAx`-tainted); `Stratified` (`⊢ₙ` still has `trans`); the open-constant-type
junk environment (`constOpenType_collapse`); junk contexts (`SortDescend`, i.e. the hole);
model-theoretic `⊬` (conditional); all 31 existing `⊬` instruments (head-shape facts, all
lift-stable, so they kill both sides of the `iff`); the identity-function encoding at term level
(`sortConv_encoding_vacuous`); re-deriving the nine/ten typing gates; `PiDescend` as a route to
unblock the tree at large.  **None of these is reattempted here.**
-/

namespace Lean4Lean

open VExpr

namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## 1. The obligation, with every abbreviation removed

`IsDefEqU`, `IsType` and `VExpr.WF` are all `∃`-wrappers around `IsDefEq`; `OnCtx` is a
`List.rec`.  Removing them turns the goal at `UniqueTyping.lean:193` into exactly this: -/

/-- **The honest obligation.**  The forward direction of `IsDefEqU.weakN_iff` with `IsDefEqU`
and `IsType` unfolded: the hypothesis's existential type `A` is *given* (it can be
skolemised out of the antecedent), the conclusion's type `B` is *demanded*, and the only
hypothesis about the environment is that every entry of the **larger** context has a sort
there.  `env` carries no `WF`, `Ordered` or `Closed` hypothesis at all. -/
def WeakNForwardRaw (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 A : VExpr}, Ctx.LiftN n k Γ Γ' →
    OnCtx Γ' (fun Δ B => ∃ u, env.IsDefEq U Δ B B (.sort u)) →
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) A →
    ∃ B, env.IsDefEq U Γ e1 e2 B

/-- …and it is the tree's `StrengtheningTarget` on the nose, so nothing has been lost or
smuggled in by the unfolding. -/
theorem weakNForwardRaw_iff_target : WeakNForwardRaw env U ↔ StrengtheningTarget env U :=
  ⟨fun H _ _ _ _ _ _ W hΓ' ⟨_, h⟩ => H W hΓ' h, fun H _ _ _ _ _ _ _ W hΓ' h => H W hΓ' ⟨_, h⟩⟩

/-! ## 2. What `henv` and `hΓ` are for

The stub at `UniqueTyping.lean:193` is `fun h => have := henv; have := hΓ; sorry`, which
records that nobody had established either hypothesis to be load-bearing.  Measured: -/

/-- **`henv` is not load-bearing in the forward direction.**  `StrengtheningTarget` — which
`weakNForwardRaw_iff_target` shows *is* the obligation — mentions no environment hypothesis, and
discharges the forward direction verbatim.  So the `have := henv` in the stub is not a hint
about the proof: an environment hypothesis cannot be consumed by this half unless the proof
first re-derives one of the *equivalent* forms that carry it. -/
theorem weakN_iff_forward_of_target (H : StrengtheningTarget env U)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr} (W : Ctx.LiftN n k Γ Γ')
    (hΓ : OnCtx Γ' (env.IsType U))
    (h : env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k)) : env.IsDefEqU U Γ e1 e2 :=
  H W hΓ h

/-- **The reverse half needs only `Ordered`, not `WF`.**  `IsDefEqU.weakN` is stated at
`Ordered env` (`Theory/Typing/Lemmas.lean:576`), so `VEnv.WF env` is strictly stronger than
what either half of the `iff` consumes.  Stated here as the `iff` with `henv` weakened, modulo
the open forward half. -/
theorem weakN_iff_of_target_ordered (henv : Ordered env) (H : StrengtheningTarget env U)
    {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr} (W : Ctx.LiftN n k Γ Γ')
    (hΓ : OnCtx Γ' (env.IsType U)) :
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2 :=
  ⟨H W hΓ, fun h => h.weakN henv W⟩

/-- **`hΓ` is a premise of the obligation, and deleting it gives a strictly stronger
statement.**  The free direction, for the record; the converse is *not* free — see
`SetModel/InstDescendBvar.lean`'s `UnguardedStrengthen`, which is the `Lift'`/`HasType` form of
the unguarded statement and is recorded there as strictly stronger than this hole. -/
def WeakNForwardUnguarded (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr}, Ctx.LiftN n k Γ Γ' →
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2

theorem StrengtheningTarget.of_unguarded (H : WeakNForwardUnguarded env U) :
    StrengtheningTarget env U := fun W _ h => H W h

/-- Vacuity control for §2: at `n = 0` the obligation's conclusion **is** its hypothesis, so no
content lives there and a proof attempt that only handles `n = 0` has proved nothing.  (`liftN 0`
is the identity and a `Ctx.LiftN 0 k` forces `Γ' = Γ`.) -/
theorem weakNForward_vacuous_at_zero {k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr}
    (W : Ctx.LiftN 0 k Γ Γ') (h : env.IsDefEqU U Γ' (e1.liftN 0 k) (e2.liftN 0 k)) :
    env.IsDefEqU U Γ e1 e2 := by
  cases W.eq_of_zero; simpa using h


/-! ## 3. Consumer census (measured 2026-09-03; no Lean content, recorded so it is not re-run)

`IsDefEqU.weakN_iff` has **13** direct users — the 12 recorded in `ParRedKWeakN.lean` plus
`typingStrengthening_of_weakN_iff` (`CRPiDescend.lean:352`), added since.  **Eleven apply `.1`
(the open forward half) and nothing else**; the remaining two, `VExpr.WF.weakN_iff`
(`UniqueTyping.lean:197`) and `IsDefEqU.weak'_iff` (`:260`, inside a `rw`), consume the whole
`iff`, and for both the reverse *content* is separately available and hole-free
(`IsDefEqU.weakN`, `IsDefEqU.weak'`, `Theory/Typing/Lemmas.lean`).

**Zero** users anywhere in `Lean4Lean/` apply `.2`/`.mpr` to this theorem or to any of its `iff`
wrappers.  (The `Experimental/` hits apply `.2` to the abstract typing-interface field
`TY.isDefEq_weakN_iff`, a different object.)  So splitting the `iff` into a proved reverse half
and an open forward half frees nothing: the forward half is the entire consumed content.
Totals re-measured today with `scripts/users.lean`: **13 direct** in 6 modules, **351
transitive** in 61 modules (the transitive figure has read 111 / 124 / 296 / 319 / 351 across
rounds, each over a larger import closure — 351 is the current one).
Table and instrument: `docs/handoff-weaknforward.md` §3, §7. -/

/-! ## 4. The `Sort (.param i)` residue: an informal claim, refuted

`Verify/Inductive/StrengthenFamily.lean` §8 bypasses this hole for the nested restriction step,
conditional on one premise — `VInductDecl'.ResultSortInhab`, i.e. an inhabitant of `Sort D.lvl`
over each member's telescope.  Three clauses discharge it (`_of_succ`, `_of_zero`, `_of_lookup`),
and the residue is a block whose `D.lvl` is neither `≈ .succ _` nor `≈ .zero` and which has no
binder at that level — a closed `inductive T : Sort u`, whose telescope is empty.  That file
records, *explicitly marked informal and not machine-checked*:

> a closed inhabitant of `Sort D.lvl` would have to be a `.sort` (forcing `D.lvl ≈ .succ _`)
> or a `.forallE` (forcing `D.lvl ≈ .imax _ _`), so one expects no closed inhabitant to exist

**That claim is false, and this section refutes it.**  The case analysis omits `.const` (and
`.app`): a constant declared at type `Sort u` is a closed inhabitant of `Sort l` for **every**
`l`, in every context, at no cost.  Such a declaration is well formed — `Sort u` is a type in
every environment — so the counterexample is not a junk environment.

Consequences, in the direction that matters: the residue is not evidence that no inhabitant
exists; it is discharged outright in any environment that declares a `Sort u`-valued constant,
which the standard prelude does (`PUnit.{u} : Sort u`, whose `VConstant` is
`⟨1, .sort (.param 0)⟩`).  §4.2 is the missing fourth discharge clause. -/

/-! ### 4.1 A constant declared at a sort inhabits every sort -/

/-- **Every sort is inhabited, in every context, whenever the environment declares one
`Sort u`-valued constant.**  No `WF`, no `Ordered`, no context hypothesis: one `constDF`. -/
theorem hasType_const_sort {c : Lean.Name} {l : VLevel} {ls : List VLevel} {n : Nat}
    {Γ : List VExpr} (hc : env.constants c = some ⟨n, .sort l⟩)
    (hls : ∀ x ∈ ls, x.WF U) (hlen : ls.length = n) :
    env.HasType U Γ (.const c ls) (.sort (l.inst ls)) := by
  have h := IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) (ci := ⟨n, .sort l⟩)
    (ls := ls) (ls' := ls) hc hls hls hlen (List.Forall₂.rfl fun _ _ => rfl)
  simpa [VEnv.HasType, VExpr.instL] using h

/-- The same at one universe parameter, which is the shape `PUnit.{u} : Sort u` has: the
constant instantiated at `l'` inhabits `Sort l'`, for **every** well-formed `l'`. -/
theorem hasType_const_sortParam {c : Lean.Name} {l' : VLevel} {Γ : List VExpr}
    (hc : env.constants c = some ⟨1, .sort (.param 0)⟩) (hl' : l'.WF U) :
    env.HasType U Γ (.const c [l']) (.sort l') := by
  have := hasType_const_sort (U := U) (Γ := Γ) hc (ls := [l'])
    (by simpa using hl') (by simp)
  simpa [VLevel.inst] using this

/-! ### 4.2 The missing fourth discharge clause, in level-only form

`StrengthenFamily.lean`'s `ResultSortInhab` is `∀ T ∈ D.types, env.HasType D.uvars (telescope T)
(b T) (.sort D.lvl)`.  The clause below is that statement's *content* with the block erased: it
holds at **every** context, so in particular at each member's telescope, and at every level, so
in particular at `.param i`.  Stated here rather than in `StrengthenFamily.lean` because that
file is another stream's; §5 of `docs/handoff-weaknforward.md` states the exact edit. -/

/-- **The fourth discharge clause.**  In an environment declaring a `Sort u`-valued constant,
every well-formed level's sort is inhabited over every context — so the residue's premise holds
for a closed `inductive T : Sort u` too. -/
theorem sortInhab_of_const {c : Lean.Name} (hc : env.constants c = some ⟨1, .sort (.param 0)⟩)
    {l' : VLevel} (hl' : l'.WF U) (Γ : List VExpr) :
    ∃ e, env.HasType U Γ e (.sort l') :=
  ⟨_, hasType_const_sortParam hc hl'⟩

/-! ### 4.3 The environment exists and is well formed — so this is not a junk witness -/

/-- `sortWit.{u} : Sort u`, as an axiom. -/
def sortWitCV : VConstVal := ⟨⟨1, .sort (.param 0)⟩, `sortWit⟩

theorem sortWitCV_wf (env : VEnv) : VConstant.WF env sortWitCV.toVConstant :=
  ⟨_, IsDefEq.sortDF (l := .param 0) (l' := .param 0)
    (by exact Nat.zero_lt_one) (by exact Nat.zero_lt_one) (.refl _)⟩

/-- **The witness environment is `VEnv.WF`.**  One `VDecl.WF.axiom` step over the empty
environment; unlike `StrengthenVerdict.lean`'s `univInhab` witness this needs no `unsafeDef`,
so the environment is built from a *pure* declaration and is not inconsistent by construction. -/
theorem exists_sortWitEnv :
    ∃ env : VEnv, VEnv.WF env ∧ env.constants `sortWit = some ⟨1, .sort (.param 0)⟩ := by
  obtain ⟨env', h⟩ : ∃ env', VEnv.empty.addConst `sortWit ⟨1, .sort (.param 0)⟩ = some env' :=
    ⟨_, rfl⟩
  have hcs : env'.constants `sortWit = some ⟨1, .sort (.param 0)⟩ := by
    unfold VEnv.addConst at h
    split at h
    · exact absurd h nofun
    · cases h; simp
  exact ⟨env', ⟨_, .decl (.axiom (ci := sortWitCV) (sortWitCV_wf _) h) .empty⟩, hcs⟩

/-- **THE REFUTATION.**  It is not the case that a closed inhabitant of `Sort (.param i)` must be
a `.sort` or a `.forallE`, nor that none exists: there is a well-formed environment and a closed
term of type `Sort (.param 0)` which is a `.const`.  `StrengthenFamily.lean` §8's informal
normal-form argument is therefore unsound as stated, and machine-checking it is not available as
a way to close that residue. -/
theorem not_forall_sort_param_uninhabited :
    ¬ ∀ (env : VEnv) (U i : Nat), VEnv.WF env → (VLevel.param i).WF U →
        ¬ ∃ e, env.HasType U [] e (.sort (.param i)) := by
  intro H
  obtain ⟨env, henv, hcs⟩ := exists_sortWitEnv
  exact H env 1 0 henv (by exact Nat.zero_lt_one)
    ⟨_, hasType_const_sortParam (U := 1) hcs (by exact Nat.zero_lt_one)⟩

/-! ### 4.4 Negative controls for §4

The refutation would be worthless if the witness were degenerate in either of the two ways that
matter, so both are excluded. -/

/-- (a) The witness is **not** a `.sort` or a `.forallE` — it is exactly the head shape §8's case
analysis omitted. -/
theorem sortWit_head_is_const {l' : VLevel} :
    (VExpr.const `sortWit [l'] : VExpr) ≠ .sort l' ∧
      ∀ A b : VExpr, (VExpr.const `sortWit [l'] : VExpr) ≠ .forallE A b := ⟨nofun, fun _ _ => nofun⟩

/-- (b) The witness environment does **not** collapse the levels: `.param 0` is not `≈` a
successor and not `≈ .zero`, so the block this discharges really is in the residue and not
already covered by `resultSortInhab_of_succ` / `_of_zero`. -/
theorem param_zero_not_succ_not_zero :
    (∀ v : VLevel, ¬ VLevel.succ v ≈ VLevel.param 0) ∧
      ¬ VLevel.imax (.succ .zero) .zero ≈ VLevel.param 0 := by
  constructor
  · intro v h
    have := VLevel.equiv_def.1 h [0]
    simp [VLevel.eval] at this
  · intro h
    have := VLevel.equiv_def.1 h [1]
    simp [VLevel.eval, Lean.Nat.imax] at this

end VEnv
end Lean4Lean
