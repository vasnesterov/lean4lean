import Lean4Lean.Theory.Inductive.Decl
import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Typing.ConstSubstNested
import Lean4Lean.Theory.Typing.SortUniq
import Lean4Lean.Theory.SetModel.Consts

/-!
# `VIndRecArg.exists_indep`, priced

`VIndField.WF.binders_indep` (`Theory/Inductive/Decl.lean`) asks that a recursive field's
binder telescope `ξ` not mention an *earlier recursive* field, and
`VIndRecArg.exists_indep` — a `sorry` in the same file — is the discharge obligation:
`ξ` may be replaced by a definitionally equal telescope that does not.

Nothing here edits `Decl.lean`.  Everything in this file is stated over the hole's own
five hypotheses, so each theorem below is a drop-in for the hole up to the extra
hypothesis it names.

## What is closed here, and what is not

* §2–§3: the obligation is **proved outright** whenever `BindersIndep` already holds —
  in particular when `ξ = []`, when `pre = []`, and when no earlier field is recursive.
  The witness is `r` itself; that is a *degenerate* witness and §7 says so.
* §4: `TeleDefEq → IsDefEqCtx`, the composition that was missing, and with it the three
  `pos`-clauses that `exists_indep`'s conclusion does **not** re-establish.
* §5: the **second** price.  `exists_indep`'s docstring names one open input,
  `IsDefEqU.forallE_inv`.  Any proof that actually *moves* a binder needs a second,
  independent one: composing the caller's `F.type ≡ r.canonType D i` with a binder-wise
  congruence needs the two sorts to agree, i.e. `VEnv.SortUniq`.  There is no
  `IsDefEqType.trans` in the tree (`Theory/Inductive/Lemmas.lean` §`IsDefEqType` has
  `toU`, `isType_l`, `isType_r`, `symm`, `instL`, `weak0`, `mono` and no `trans`), and
  §5 shows why: it *is* sort uniqueness.  `Decl.lean`'s own R3 note records the same
  obstruction for `VIndType.WF.canon` and does not connect it to this hole.
* §6: the **corrected statement**, which as of 2026-09-03 is *in* `Decl.lean`.  The hole's
  conclusion now carries two further conjuncts — the `IsDefEqCtx` of the two binder contexts and
  the telescope congruence — and §6.2b transports the whole `some` branch over exactly that
  (`posSome_transport_of_indepGoal`).  `IndepUpgrade` (the `TeleDefEq` form) stays here because
  `VEnv.TeleDefEq` lives in a module that imports `Decl.lean`; §6.3 is the bridge.
* §7: the witnesses and the controls, including §7.3b — the repaired statement's new
  hypotheses are inhabited (`rai_staged`) **and** exclude §7.2's candidate counterexample
  (`rai_not_staged`), with `raiEnvP_add` showing which half of them does the excluding.
-/

namespace Lean4Lean

/-! ## 0. Two free steps the repaired conclusion needs

Both are what make the *degenerate* witness `r' = r` cost nothing under the strengthened
conclusion (§3): the reflexive `IsDefEqCtx` comes from the hole's own `hOn`, and the reflexive
`IsDefEqType` from its own `hdefeq`.  Neither needs `SortUniq` — the sort is the one `hdefeq`
was already checked at. -/

namespace RecArgIndep

/-- `IsDefEqCtx` is reflexive over an arbitrary base, given `OnCtx` of the extension.
`VEnv.IsDefEqCtx.refl` (`Theory/Typing/Lemmas.lean`) has base `[]` only. -/
theorem isDefEqCtx_refl_suffix {env : VEnv} {U : Nat} {Γ₀ : List VExpr} :
    ∀ {Δ : List VExpr}, OnCtx (Δ ++ Γ₀) (env.IsType U) →
      VEnv.IsDefEqCtx env U Γ₀ (Δ ++ Γ₀) (Δ ++ Γ₀)
  | [], _ => .zero
  | _::_, ⟨h1, _, h2⟩ => .succ (isDefEqCtx_refl_suffix h1) h2

/-- The right-hand side of an `IsDefEqType` is `IsDefEqType` to itself, **at the same sort** —
so this is free, unlike `isDefEqType_trans_of_sortUniq` (§5). -/
theorem isDefEqType_refl_r {env : VEnv} {U : Nat} {Γ : List VExpr} {A B : VExpr}
    (h : env.IsDefEqType U Γ A B) : env.IsDefEqType U Γ B B :=
  let ⟨_, h⟩ := h; ⟨_, h.symm.trans h⟩

end RecArgIndep

/-! ## 1. The obligation as a predicate -/

namespace VIndRecArg

/-- **`VIndRecArg.exists_indep`'s conclusion, verbatim.**  `indepGoal_of_exists_indep`
below machine-checks that this is the hole's conclusion and not a paraphrase of it.

**Updated to the repaired conclusion.**  The first six conjuncts are the original ones
unchanged; the last two are §6's upgrade, now part of the hole's own statement
(`Decl.lean`).  So this file's faithfulness check points at the *new* statement, and §3's
halves below are re-proved against it. -/
def IndepGoal (env : VEnv) (D : VInductDecl') (Γ : List VExpr) (pre : List VIndField)
    (i : Nat) (F : VIndField) (r : VIndRecArg) : Prop :=
  ∃ r' : VIndRecArg,
    r'.idx = r.idx ∧ r'.args = r.args ∧ r'.binders.length = r.binders.length ∧
    (∀ B ∈ r'.binders, D.NoBlock B) ∧
    env.IsDefEqType D.uvars Γ F.type (r'.canonType D i) ∧
    r'.BindersIndep pre i ∧
    VEnv.IsDefEqCtx env D.uvars Γ (r.binders.reverse ++ Γ) (r'.binders.reverse ++ Γ) ∧
    env.IsDefEqType D.uvars Γ (r.canonType D i) (r'.canonType D i)

/-- **Faithfulness of §1.**  This is the *only* declaration in the file whose axiom set
contains `sorryAx`, and it contains it because it applies the hole: it typechecks exactly
when `IndepGoal` is the hole's conclusion. -/
theorem indepGoal_of_exists_indep {env₀ env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (henv₀ : VEnv.Ordered env₀)
    (henv : VEnv.Ordered env)
    (hstage : env₀.addIndTypes D = some env)
    (hlen : pre.length = i)
    (hΓ : Γ = (pre.map (·.type)).reverse ++ D.params.reverse)
    (hpre : ∀ (i' : Nat) (F' : VIndField), pre[i']? = some F' →
      F'.WF env D (pre.take i') (((pre.take i').map (·.type)).reverse ++ D.params.reverse) i')
    (hty : env.HasType D.uvars Γ F.type (.sort F.lvl))
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hOn : OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars))
    (hdefeq : env.IsDefEqType D.uvars Γ F.type (r.canonType D i)) :
    IndepGoal env D Γ pre i F r :=
  VIndRecArg.exists_indep henv₀ henv hstage hlen hΓ hpre hty hbind hOn hdefeq

/-! ## 2. When `BindersIndep` already holds -/

/-- A nullary `ξ` satisfies the clause: there is no binder to check. -/
theorem bindersIndep_of_binders_nil {r : VIndRecArg} {pre : List VIndField} {i : Nat}
    (h : r.binders = []) : r.BindersIndep pre i := by
  intro _ _ _ _ _ _ _ _ hB
  rw [h] at hB; exact absurd hB nofun

/-- No earlier field at all: the clause is vacuous. -/
theorem bindersIndep_of_pre_nil {r : VIndRecArg} {pre : List VIndField} {i : Nat}
    (h : pre = []) : r.BindersIndep pre i := by
  intro _ _ _ hF' _ _ _ _ _
  rw [h] at hF'; exact absurd hF' nofun

/-- **No earlier *recursive* field: the clause is vacuous.**  This is the regime every
constructor in `Theory/Inductive/DeclExamples.lean` except `W'.mk` and `Forest'.cons` is
in, and the regime `Acc.intro` is in — see `accIntroRec_BindersIndep` there. -/
theorem bindersIndep_of_pre_norec {r : VIndRecArg} {pre : List VIndField} {i : Nat}
    (h : ∀ F' ∈ pre, F'.recArg = none) : r.BindersIndep pre i := by
  intro i' _ F' hF' hrec _ _ _ _
  rw [h F' (List.mem_of_getElem? hF')] at hrec
  exact absurd hrec (by simp)

/-! ## 3. The obligation, closed on that regime

The witness is `r` itself, so nothing moves: these are the halves where the obligation is
*about nothing*, and §7.1 records that as degeneracy rather than as a win. -/

/-- **`exists_indep` when the clause already holds** — now against the *repaired*
conclusion.  The witness is still `r`, and the two new conjuncts are still free: the
`IsDefEqCtx` is `hOn` (a hypothesis of the hole, and a conjunct of `pos`) and the
`IsDefEqType` is `hdefeq`'s own right-hand reflexivity, at `hdefeq`'s own sort.  **No
`SortUniq`.** -/
theorem indepGoal_of_bindersIndep {env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hOn : OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars))
    (hdefeq : env.IsDefEqType D.uvars Γ F.type (r.canonType D i))
    (h : r.BindersIndep pre i) : IndepGoal env D Γ pre i F r :=
  ⟨r, rfl, rfl, rfl, hbind, hdefeq, h,
    RecArgIndep.isDefEqCtx_refl_suffix hOn, RecArgIndep.isDefEqType_refl_r hdefeq⟩

/-- **A drop-in for the hole**, with the hole's five hypotheses unchanged and one extra:
no earlier field is recursive.  The extra hypothesis is decidable and is discharged at the
construction site — `VIndCtor.WF.fields` instantiates `pre := C.fields.take i`, so a
caller checks `recArg` on at most `i` fields. -/
theorem exists_indep_of_pre_norec {env₀ env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (_henv₀ : VEnv.Ordered env₀)
    (_henv : VEnv.Ordered env)
    (_hstage : env₀.addIndTypes D = some env)
    (_hlen : pre.length = i)
    (_hΓ : Γ = (pre.map (·.type)).reverse ++ D.params.reverse)
    (_hpre : ∀ (i' : Nat) (F' : VIndField), pre[i']? = some F' →
      F'.WF env D (pre.take i') (((pre.take i').map (·.type)).reverse ++ D.params.reverse) i')
    (_hty : env.HasType D.uvars Γ F.type (.sort F.lvl))
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hOn : OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars))
    (hdefeq : env.IsDefEqType D.uvars Γ F.type (r.canonType D i))
    (hfree : ∀ F' ∈ pre, F'.recArg = none) :
    ∃ r' : VIndRecArg,
      r'.idx = r.idx ∧ r'.args = r.args ∧ r'.binders.length = r.binders.length ∧
      (∀ B ∈ r'.binders, D.NoBlock B) ∧
      env.IsDefEqType D.uvars Γ F.type (r'.canonType D i) ∧
      r'.BindersIndep pre i ∧
      VEnv.IsDefEqCtx env D.uvars Γ (r.binders.reverse ++ Γ) (r'.binders.reverse ++ Γ) ∧
      env.IsDefEqType D.uvars Γ (r.canonType D i) (r'.canonType D i) :=
  indepGoal_of_bindersIndep hbind hOn hdefeq (bindersIndep_of_pre_norec hfree)

/-- The same for a nullary `ξ`. -/
theorem exists_indep_of_binders_nil {env₀ env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (_henv₀ : VEnv.Ordered env₀)
    (_henv : VEnv.Ordered env)
    (_hstage : env₀.addIndTypes D = some env)
    (_hlen : pre.length = i)
    (_hΓ : Γ = (pre.map (·.type)).reverse ++ D.params.reverse)
    (_hpre : ∀ (i' : Nat) (F' : VIndField), pre[i']? = some F' →
      F'.WF env D (pre.take i') (((pre.take i').map (·.type)).reverse ++ D.params.reverse) i')
    (_hty : env.HasType D.uvars Γ F.type (.sort F.lvl))
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hOn : OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars))
    (hdefeq : env.IsDefEqType D.uvars Γ F.type (r.canonType D i))
    (hnil : r.binders = []) :
    ∃ r' : VIndRecArg,
      r'.idx = r.idx ∧ r'.args = r.args ∧ r'.binders.length = r.binders.length ∧
      (∀ B ∈ r'.binders, D.NoBlock B) ∧
      env.IsDefEqType D.uvars Γ F.type (r'.canonType D i) ∧
      r'.BindersIndep pre i ∧
      VEnv.IsDefEqCtx env D.uvars Γ (r.binders.reverse ++ Γ) (r'.binders.reverse ++ Γ) ∧
      env.IsDefEqType D.uvars Γ (r.canonType D i) (r'.canonType D i) :=
  indepGoal_of_bindersIndep hbind hOn hdefeq (bindersIndep_of_binders_nil hnil)

/-- …and for `i = 0`, where the hole's own `hlen` forces `pre = []`. -/
theorem exists_indep_of_i_zero {env₀ env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {F : VIndField} {r : VIndRecArg}
    (_henv₀ : VEnv.Ordered env₀)
    (_henv : VEnv.Ordered env)
    (_hstage : env₀.addIndTypes D = some env)
    (hlen : pre.length = 0)
    (_hΓ : Γ = (pre.map (·.type)).reverse ++ D.params.reverse)
    (_hpre : ∀ (i' : Nat) (F' : VIndField), pre[i']? = some F' →
      F'.WF env D (pre.take i') (((pre.take i').map (·.type)).reverse ++ D.params.reverse) i')
    (_hty : env.HasType D.uvars Γ F.type (.sort F.lvl))
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hOn : OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars))
    (hdefeq : env.IsDefEqType D.uvars Γ F.type (r.canonType D 0)) :
    ∃ r' : VIndRecArg,
      r'.idx = r.idx ∧ r'.args = r.args ∧ r'.binders.length = r.binders.length ∧
      (∀ B ∈ r'.binders, D.NoBlock B) ∧
      env.IsDefEqType D.uvars Γ F.type (r'.canonType D 0) ∧
      r'.BindersIndep pre 0 ∧
      VEnv.IsDefEqCtx env D.uvars Γ (r.binders.reverse ++ Γ) (r'.binders.reverse ++ Γ) ∧
      env.IsDefEqType D.uvars Γ (r.canonType D 0) (r'.canonType D 0) :=
  indepGoal_of_bindersIndep hbind hOn hdefeq
    (bindersIndep_of_pre_nil (List.eq_nil_of_length_eq_zero hlen))

end VIndRecArg

/-! ## 4. `TeleDefEq → IsDefEqCtx`: the composition that was missing

`VEnv.TeleDefEq` (`Theory/Typing/ConstSubstNested.lean`) relates two telescopes entrywise in
declaration order, and `VEnv.IsDefEqCtx` (`Theory/Typing/Lemmas.lean`) relates two *contexts*.
Everything that has to move when a binder telescope is replaced — `OnCtx`, the typing of
`canonResult`, the `HasArgs` derivation for the index arguments — moves along the second, and
nothing in the tree turned the first into it.  `TeleDefEq.rfl` carries no typing, which is why
`OnCtx` of the source telescope's context is the extra input. -/

namespace RecArgIndep

theorem teleDefEq_length_eq {env : VEnv} {U : Nat} :
    ∀ {Γ As As' : List VExpr}, env.TeleDefEq U Γ As As' → As.length = As'.length
  | _, _, _, .nil => rfl
  | _, _, _, .rfl h => congrArg Nat.succ (teleDefEq_length_eq h)
  | _, _, _, .cons _ h => congrArg Nat.succ (teleDefEq_length_eq h)

/-- The general form: a `TeleDefEq` extends any context conversion it sits over. -/
theorem teleDefEq_isDefEqCtx' {env : VEnv} {U : Nat} {Γ₀ : List VExpr} :
    ∀ {Γ₁ Γ₂ As As' : List VExpr}, env.TeleDefEq U Γ₁ As As' →
      OnCtx (As.reverse ++ Γ₁) (env.IsType U) →
      VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂ →
      VEnv.IsDefEqCtx env U Γ₀ (As.reverse ++ Γ₁) (As'.reverse ++ Γ₂) := by
  intro Γ₁ Γ₂ As As' h
  induction h generalizing Γ₂ with
  | nil => exact fun _ H => H
  | rfl _ ih =>
    intro hOn H
    simp only [VExpr.tele_ctx_cons] at hOn ⊢
    obtain ⟨_, hA⟩ := OnCtx.head_of_append hOn
    exact ih hOn (.succ H hA)
  | cons hA _ ih =>
    intro hOn H
    simp only [VExpr.tele_ctx_cons] at hOn ⊢
    exact ih hOn (.succ H hA)

/-- **The composition.**  An entrywise telescope conversion over `Γ` is a context conversion
of the two telescope contexts, with `Γ` as the common base. -/
theorem teleDefEq_isDefEqCtx {env : VEnv} {U : Nat} {Γ As As' : List VExpr}
    (h : env.TeleDefEq U Γ As As') (hOn : OnCtx (As.reverse ++ Γ) (env.IsType U)) :
    VEnv.IsDefEqCtx env U Γ (As.reverse ++ Γ) (As'.reverse ++ Γ) :=
  teleDefEq_isDefEqCtx' h hOn .zero

/-! ## 5. The second price: composing the two defeqs is sort uniqueness

`Theory/Inductive/Lemmas.lean`'s `IsDefEqType` section has `toU`, `isType_l`, `isType_r`,
`symm`, `instL`, `weak0` and `mono` — and **no `trans`**.  That is not an omission.
`IsDefEqType` records the sort the conversion was derived at, `VEnv.IsDefEq.trans` needs both
sides at the *same* type, and a binder-wise congruence (`forallEDF`) delivers `.imax uA v`
whatever sort the caller's own conversion was checked at.  Identifying the two is exactly
`VEnv.SortUniq`.

`Decl.lean`'s own R3 note records this obstruction for `VIndType.WF.canon` ("Composing the two
needs those sorts to agree — i.e. sort uniqueness") and does not connect it to this hole;
`exists_indep`'s docstring names only `IsDefEqU.forallE_inv`.  So the hole has **two**
independent charges against the injectivity family, and only one of them is recorded. -/

/-- **`IsDefEqType` is transitive granted universe uniqueness** — and, per §5's header, only
granted it. -/
theorem isDefEqType_trans_of_sortUniq {env : VEnv} {U : Nat} {Γ : List VExpr} {A B C : VExpr}
    (henv : VEnv.Ordered env) (hsu : env.SortUniq U) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqType U Γ A B) (h2 : env.IsDefEqType U Γ B C) :
    env.IsDefEqType U Γ A C := by
  obtain ⟨u, h1⟩ := h1
  obtain ⟨v, h2⟩ := h2
  have hu : u.WF U := h1.sort_r henv hΓ
  have hv : v.WF U := h2.sort_r henv hΓ
  exact ⟨u, h1.trans (.defeqDF (.sortDF hv hu (hsu hΓ hv hu h2.hasType.1 h1.hasType.2)) h2)⟩

end RecArgIndep

/-! ## 6. The corrected statement

`exists_indep` exists to license one substitution: replace `r` by `r'` inside
`VIndField.WF.pos`'s `some` branch.  Its conclusion does not license it.  Four of the nine
conjuncts of that branch — `OnCtx (ξ.reverse ++ Γ)`, the typing of `canonResult`, the
`HasArgs` derivation for the index arguments, and the `IsDefEqType` itself — are stated
*over the binder telescope*, and the first three have to be re-derived in the **new**
telescope's context.  The conclusion hands back only `IsDefEqType Γ F.type (r'.canonType D i)`,
and extracting an entrywise relation between `r.binders` and `r'.binders` from a conversion
between the two `mkPi`s is `IsDefEqU.forallE_inv` — the very statement the hole is waiting on.
So even a *proof* of `exists_indep` as stated would leave its consumer where it started.

**[analysis, not proved]** that last step: nothing here shows the three clauses are
*un*derivable from the conclusion; what is shown is that the natural derivation is
pi-injectivity, and that carrying the `TeleDefEq` instead makes all four free.

`IndepUpgrade` is the repair in its strongest form: the same existential, witnessed by an
entrywise `TeleDefEq`.  §6.2 transports the whole branch; §6.3 shows it implies the hole's
conclusion.

**What actually landed in `Decl.lean`** (2026-09-03) is one notch weaker than `IndepUpgrade` and
for a hard reason: `VEnv.TeleDefEq` is declared in `Theory/Typing/ConstSubstNested.lean`, which
transitively imports `Decl.lean`, so *no* form of the repair naming `TeleDefEq` can be stated at
the hole.  What the hole now carries is the two things `TeleDefEq` was only ever used to produce
— `VEnv.IsDefEqCtx env D.uvars Γ (ξ.reverse ++ Γ) (ξ'.reverse ++ Γ)` (available at that layer:
`Theory/Typing/Lemmas.lean`) and the telescope congruence `IsDefEqType Γ (r.canonType D i)
(r'.canonType D i)` — on top of the original six conjuncts.  §6.2b is the transport over that
conclusion, so nothing is lost: `IndepUpgrade → IndepGoal` (§6.3) and `IndepGoal → PosSome at r'`
(§6.2b) are both theorems. -/

open VExpr (mkPi liftTele)

namespace VIndField

/-- **`VIndField.WF.pos`'s `some` branch, transcribed.**  `posSome_of_wf` machine-checks the
transcription against `VIndField.WF` itself, so this is not a paraphrase. -/
def PosSome (env : VEnv) (D : VInductDecl') (Γ : List VExpr) (i : Nat) (F : VIndField)
    (r : VIndRecArg) : Prop :=
  r.idx < D.nm ∧
  r.args.length = (D.types.getD r.idx default).indices.length ∧
  (∀ B ∈ r.binders, D.NoBlock B) ∧
  (∀ a ∈ r.args, D.NoBlock a) ∧
  OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars) ∧
  env.HasType D.uvars (r.binders.reverse ++ Γ) (r.canonResult D i) (.sort D.lvl) ∧
  (∀ T', D.types[r.idx]? = some T' →
    env.HasArgs D.uvars (r.binders.reverse ++ Γ)
      (liftTele (r.binders.length + i) T'.indices) r.args) ∧
  env.IsDefEqType D.uvars Γ F.type (r.canonType D i) ∧
  D.ResidualClean (r.binders.length + i) F.type

/-- Faithfulness of the transcription. -/
theorem posSome_of_wf {env : VEnv} {D : VInductDecl'} {Γ : List VExpr} {i : Nat}
    {F : VIndField} {r : VIndRecArg} {pre : List VIndField}
    (h : F.WF env D pre Γ i) (hr : F.recArg = some r) : PosSome env D Γ i F r := by
  have h2 := h.pos; rw [hr] at h2; exact h2

end VIndField

/-- **The repaired obligation.**  `exists_indep`'s existential, witnessed by a telescope that
is *entrywise* definitionally equal to `r.binders` rather than only `mkPi`-equal. -/
def VIndRecArg.IndepUpgrade (env : VEnv) (D : VInductDecl') (Γ : List VExpr)
    (pre : List VIndField) (i : Nat) (r : VIndRecArg) : Prop :=
  ∃ bs : List VExpr,
    env.TeleDefEq D.uvars Γ r.binders bs ∧
    (∀ B ∈ bs, D.NoBlock B) ∧
    (VIndRecArg.mk bs r.idx r.args).BindersIndep pre i

namespace RecArgIndep

/-- **§6.2 — the repaired conclusion transports the whole `some` branch.**  This is what the
obligation was for, and the current conclusion does not deliver it. -/
theorem posSome_transport {env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (henv : VEnv.Ordered env) (hsu : env.SortUniq D.uvars)
    (hΓ : OnCtx Γ (env.IsType D.uvars))
    (h : VIndField.PosSome env D Γ i F r) (hup : r.IndepUpgrade env D Γ pre i) :
    ∃ r' : VIndRecArg, r'.idx = r.idx ∧ r'.args = r.args ∧
      r'.binders.length = r.binders.length ∧
      VIndField.PosSome env D Γ i F r' ∧ r'.BindersIndep pre i := by
  obtain ⟨bs, htele, hnb, hindep⟩ := hup
  obtain ⟨hidx, hargslen, -, hargs, hOn, hres, hha, hdefeq, hrc⟩ := h
  have hlen : bs.length = r.binders.length := (teleDefEq_length_eq htele).symm
  have W := teleDefEq_isDefEqCtx htele hOn
  have hcr : (VIndRecArg.mk bs r.idx r.args).canonResult D i = r.canonResult D i := by
    simp [VIndRecArg.canonResult, hlen]
  refine ⟨⟨bs, r.idx, r.args⟩, rfl, rfl, hlen,
    ⟨hidx, hargslen, hnb, hargs, (W.symm henv).isType' hΓ, ?_, ?_, ?_, ?_⟩, hindep⟩
  · exact hcr ▸ hres.defeqDFC henv W
  · intro T' hT'
    have := (hha T' hT').defeqDFC henv W
    simpa [hlen] using this
  · refine isDefEqType_trans_of_sortUniq henv hsu hΓ hdefeq ?_
    have := VEnv.IsDefEq.mkPi_congrU htele hOn ⟨D.lvl, hres⟩
    show env.IsDefEqType D.uvars Γ (r.canonType D i) _
    rw [VIndRecArg.canonType, VIndRecArg.canonType, hcr]
    exact this
  · simpa [hlen] using hrc

/-- **§6.2b — the transport, over the hole's *actual* conclusion.**  `posSome_transport` above
consumes `IndepUpgrade`, whose `TeleDefEq` cannot appear in `Decl.lean` (that inductive lives in
`Theory/Typing/ConstSubstNested.lean`, which transitively imports `Decl.lean`).  What the hole's
repaired conclusion carries instead is the `IsDefEqCtx` that `TeleDefEq` was only ever used to
produce, plus the telescope congruence as a separate conjunct — and **that is enough**: this is
the same theorem with `IndepGoal` in place of `IndepUpgrade`, so the repaired statement's
consumer is proved, not projected.

**And it costs no `SortUniq`** — measured, not assumed: the hypothesis was there in the first
draft and the unused-variable linter rejected it.  The reason is that the repaired conclusion
keeps the *original* `IsDefEqType Γ F.type (r'.canonType D i)` conjunct alongside the new
telescope congruence, so the consumer never has to compose two conversions; it is whoever
*proves* the hole that must hand over both, and only there does composing them cost sort
uniqueness (`isDefEqType_trans_of_sortUniq`, §5).  `posSome_transport` above still pays it,
because `IndepUpgrade` carries only the telescope side. -/
theorem posSome_transport_of_indepGoal {env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (henv : VEnv.Ordered env)
    (hΓ : OnCtx Γ (env.IsType D.uvars))
    (h : VIndField.PosSome env D Γ i F r)
    (hg : VIndRecArg.IndepGoal env D Γ pre i F r) :
    ∃ r' : VIndRecArg, r'.idx = r.idx ∧ r'.args = r.args ∧
      r'.binders.length = r.binders.length ∧
      VIndField.PosSome env D Γ i F r' ∧ r'.BindersIndep pre i := by
  obtain ⟨r', hidx', hargs', hlen', hnb, hdefeqF, hindep, hctx, -⟩ := hg
  obtain ⟨hidx, hargslen, -, hargsnb, hOn, hres, hha, -, hrc⟩ := h
  have hcr : r'.canonResult D i = r.canonResult D i := by
    simp [VIndRecArg.canonResult, hidx', hargs', hlen']
  refine ⟨r', hidx', hargs', hlen',
    ⟨hidx' ▸ hidx, by rw [hargs', hidx']; exact hargslen, hnb, hargs' ▸ hargsnb,
      (hctx.symm henv).isType' hΓ, hcr ▸ hres.defeqDFC henv hctx, ?_, hdefeqF, hlen' ▸ hrc⟩,
    hindep⟩
  intro T' hT'
  rw [hidx'] at hT'
  have := (hha T' hT').defeqDFC henv hctx
  rw [hargs']
  simpa [hlen'] using this

/-- **§6.3 — the repair is a strengthening.**  `IndepUpgrade` implies `exists_indep`'s
conclusion, so replacing the statement loses nothing that a consumer of the old one had. -/
theorem indepGoal_of_indepUpgrade {env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (henv : VEnv.Ordered env) (hsu : env.SortUniq D.uvars)
    (hΓ : OnCtx Γ (env.IsType D.uvars))
    (hOn : OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars))
    (hres : env.HasType D.uvars (r.binders.reverse ++ Γ) (r.canonResult D i) (.sort D.lvl))
    (hdefeq : env.IsDefEqType D.uvars Γ F.type (r.canonType D i))
    (hup : r.IndepUpgrade env D Γ pre i) :
    VIndRecArg.IndepGoal env D Γ pre i F r := by
  obtain ⟨bs, htele, hnb, hindep⟩ := hup
  have hlen : bs.length = r.binders.length := (teleDefEq_length_eq htele).symm
  have hcr : (VIndRecArg.mk bs r.idx r.args).canonResult D i = r.canonResult D i := by
    simp [VIndRecArg.canonResult, hlen]
  have hcongr : env.IsDefEqType D.uvars Γ (r.canonType D i)
      ((VIndRecArg.mk bs r.idx r.args).canonType D i) := by
    have := VEnv.IsDefEq.mkPi_congrU htele hOn ⟨D.lvl, hres⟩
    show env.IsDefEqType D.uvars Γ (r.canonType D i) _
    rw [VIndRecArg.canonType, VIndRecArg.canonType, hcr]
    exact this
  exact ⟨⟨bs, r.idx, r.args⟩, rfl, rfl, hlen, hnb,
    isDefEqType_trans_of_sortUniq henv hsu hΓ hdefeq hcongr, hindep,
    teleDefEq_isDefEqCtx htele hOn, hcongr⟩

end RecArgIndep

/-! ## 7. Witnesses, degeneracy, and the controls

### 7.1 The closed halves are degenerate, and this is the record of it

§3's witness is `r` itself: `indepGoal_of_bindersIndep` returns `⟨r, rfl, rfl, rfl, …⟩`, so on
that regime the existential is satisfied without moving anything.  **The degeneracy survives the
strengthening**, which was the thing to check when the hole's conclusion grew two conjuncts: the
new `IsDefEqCtx` conjunct at `r' = r` is `isDefEqCtx_refl_suffix hOn` (§0) and the new
`IsDefEqType` conjunct is `isDefEqType_refl_r hdefeq` (§0, at `hdefeq`'s own sort, so **no**
`SortUniq`).  All three of §3's drop-ins are stated and proved against the *repaired* conclusion,
and `hOn` — the one hypothesis they gained — is `pos`'s own `OnCtx` conjunct.  `docs/vacuity-ledger.md`
rows 20–21 are the pattern to avoid — an obligation named after the hard case that, under its
own premise, contains none of it — so the halves are labelled, not headlined.

`Theory/Inductive/DeclExamples.lean` already measures how wide the degenerate regime is:
`accIntroRec_BindersIndep` (`Acc.intro`: the earlier field is not recursive),
`forestCons_BindersIndep` (`Forest'.cons`: two recursive fields, the later one with `ξ = []`),
and `wMk_BindersIndep` (`W'.mk`: two recursive fields, `ξ = [β]` non-empty and the `Skips`
check real).  All three are covered: the first two land in §2 (`bindersIndep_of_pre_norec` and
`bindersIndep_of_binders_nil` respectively), and `W'.mk` — which is in the *non*-vacuous regime,
earlier field recursive and `ξ ≠ []` — lands in §3 rather than §2, because its binder is the
block's *parameter* and so already skips.  Either way `r' = r`: **no witness in the tree needs a
binder to move.**

### 7.2 The residual case is reachable — at a `VEnv.WF` environment

The one thing §2–§3 cannot settle is whether the residual case is empty.  It is not.  Below is
a concrete instance of **all five hypotheses the hole's *first* statement had** at a well-formed environment where
`r` is *not* a witness (`not_bindersIndep_raiRec1`), so any proof of `exists_indep` must
genuinely produce a different telescope there.

`raiB = raiP x` where `x` is the earlier recursive field: block-free (so `hbind` holds), a type
(so `hty` holds), and mentioning `x` (so the clause fails).

### 7.3 …and the control: what makes it reachable is a constant the staged environment cannot have

`raiEnv` declares `raiP : raiI → Sort 1`, a constant whose **type mentions the block**
(`raiCiP_type_hasBlock`).  At the environment `exists_indep` is actually applied in — the one
`VEnv.addIndTypes` has just produced — no such constant can exist, because the block's
constants were added last.  So this witness shows the hypothesis set is *too weak to be
provable by the argument its docstring gives* (that argument assumes nothing in scope can
eliminate an `I`), and the missing hypothesis is a freshness condition on `env`, not another
lemma.

**[analysis, not proved]** whether the conclusion is actually *false* at this instance.  It
would follow from pi-injectivity plus rigidity of a constant spine (`RigidConstAppInv`), and
both are open (`Theory/Typing/Injectivity.lean`, `Theory/Typing/RigidConstPrice.lean`).  So
this is a **candidate counterexample**, not a refutation, and it is graded that way per the
ledger's "grade every refutation by whether its witness is reachable". -/

namespace RecArgIndep

open VExpr (mkPi)

def raiI : Lean.Name := `Lean4Lean.RecArgIndep.I
def raiP : Lean.Name := `Lean4Lean.RecArgIndep.P

theorem raiI_ne_raiP : raiI ≠ raiP := by decide

def raiCiI : VConstant := ⟨0, .sort (.succ .zero)⟩
def raiCiP : VConstant := ⟨0, .forallE (.const raiI []) (.sort (.succ .zero))⟩

def raiEnv0 : VEnv where
  constants n := if raiI = n then some raiCiI else none
  defeqs _ := False

def raiEnv : VEnv where
  constants n := if raiP = n then some raiCiP else if raiI = n then some raiCiI else none
  defeqs _ := False

theorem raiEnv0_add : VEnv.empty.addConst raiI raiCiI = some raiEnv0 := by
  simp [VEnv.addConst, VEnv.empty, raiEnv0]

theorem raiEnv_add : raiEnv0.addConst raiP raiCiP = some raiEnv := by
  simp [VEnv.addConst, raiEnv0, raiEnv, raiI, raiP]

theorem raiEnv_I : raiEnv.constants raiI = some raiCiI := by
  simp [raiEnv, raiI, raiP]

theorem raiEnv_P : raiEnv.constants raiP = some raiCiP := by simp [raiEnv]

/-- `raiI : Sort 1` in any environment declaring it. -/
theorem raiI_hasType {env : VEnv} {U : Nat} {Γ : List VExpr}
    (h : env.constants raiI = some raiCiI) :
    env.HasType U Γ (.const raiI []) (.sort (.succ .zero)) := by
  have := VEnv.IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) (ls := []) (ls' := [])
    h (by simp) (by simp) rfl (by simp)
  simpa [raiCiI, VExpr.instL, VLevel.inst, VEnv.HasType] using this

/-- `raiP : raiI → Sort 1`. -/
theorem raiP_hasType {env : VEnv} {U : Nat} {Γ : List VExpr}
    (h : env.constants raiP = some raiCiP) :
    env.HasType U Γ (.const raiP []) (.forallE (.const raiI []) (.sort (.succ .zero))) := by
  have := VEnv.IsDefEq.constDF (env := env) (uvars := U) (Γ := Γ) (ls := []) (ls' := [])
    h (by simp) (by simp) rfl (by simp)
  simpa [raiCiP, VExpr.instL, VLevel.inst, VEnv.HasType] using this

theorem wf_raiEnv : VEnv.WF raiEnv := by
  refine ⟨[.axiom ⟨raiCiP, raiP⟩, .axiom ⟨raiCiI, raiI⟩],
    .decl (.axiom ?_ raiEnv_add) (.decl (.axiom ?_ raiEnv0_add) .empty)⟩
  · exact ⟨_, VEnv.IsDefEq.forallEDF (raiI_hasType (by simp [raiEnv0]))
      (VEnv.HasType.sort trivial)⟩
  · exact ⟨_, VEnv.HasType.sort trivial⟩

/-! ### The declaration -/

def raiT : VIndType where
  name := raiI
  type := .sort (.succ .zero)
  indices := []
  ctors := []

def raiD : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  types := [raiT]
  isLE := false

/-- Field 0: recursive, `ξ = []`, `π = []`, so its stored type is `raiI` on the nose — the
canonical shape, not a contrived one. -/
def raiRec0 : VIndRecArg := ⟨[], 0, []⟩
def raiF0 : VIndField := ⟨.const raiI [], .succ .zero, some raiRec0⟩

/-- The binder that mentions field 0. -/
def raiB : VExpr := .app (.const raiP []) (.bvar 0)

def raiRec1 : VIndRecArg := ⟨[raiB], 0, []⟩
def raiF1 : VIndField :=
  ⟨mkPi [raiB] (.const raiI []), .imax (.succ .zero) (.succ .zero), some raiRec1⟩

def raiPre : List VIndField := [raiF0]
def raiΓ : List VExpr := [.const raiI []]

/-- Field 0's stored type really is its canonical type. -/
theorem raiF0_canon : raiF0.type = raiRec0.canonType raiD 0 := rfl
/-- Field 1's stored type really is its canonical type — so `hdefeq` is reflexivity. -/
theorem raiF1_canon : raiF1.type = raiRec1.canonType raiD 1 := rfl
/-- The context is the one the hole's `hΓ` names. -/
theorem raiΓ_eq : raiΓ = (raiPre.map (·.type)).reverse ++ raiD.params.reverse := rfl

theorem raiB_noBlock : raiD.NoBlock raiB := by decide
theorem raiB_hasType : raiEnv.HasType 0 raiΓ raiB (.sort (.succ .zero)) := by
  have hf := raiP_hasType (env := raiEnv) (U := 0) (Γ := raiΓ) raiEnv_P
  have ha : raiEnv.HasType 0 raiΓ (.bvar 0) (.const raiI []) := by
    have : raiEnv.HasType 0 raiΓ (.bvar 0) ((VExpr.const raiI []).lift) :=
      VEnv.IsDefEq.bvar .zero
    simpa [VExpr.lift, VExpr.liftN] using this
  simpa [raiB, VExpr.inst, VEnv.HasType] using VEnv.IsDefEq.appDF hf ha

/-- **The hole's `hty`.** -/
theorem raiF1_hasType : raiEnv.HasType 0 raiΓ raiF1.type (.sort raiF1.lvl) :=
  VEnv.IsDefEq.forallEDF raiB_hasType (raiI_hasType raiEnv_I)

/-- **The five hypotheses `VIndRecArg.exists_indep` had before the 2026-09-03 repair, at a
`VEnv.WF` environment.**  They still all hold; what no longer holds is the repaired statement's
`henv₀`+`hstage` pair — see `rai_not_staged` below, which is why this instance is a *record of
why the hypothesis was added* rather than a live candidate counterexample. -/
theorem rai_hyps :
    VEnv.WF raiEnv ∧
    raiPre.length = 1 ∧
    raiΓ = (raiPre.map (·.type)).reverse ++ raiD.params.reverse ∧
    raiEnv.HasType raiD.uvars raiΓ raiF1.type (.sort raiF1.lvl) ∧
    (∀ B ∈ raiRec1.binders, raiD.NoBlock B) ∧
    raiEnv.IsDefEqType raiD.uvars raiΓ raiF1.type (raiRec1.canonType raiD 1) :=
  ⟨wf_raiEnv, rfl, raiΓ_eq, raiF1_hasType,
   fun _ h => by simpa [raiRec1, List.mem_singleton.1 h] using raiB_noBlock,
   ⟨_, raiF1_canon ▸ raiF1_hasType⟩⟩

/-- **…and `r` itself is not a witness there.**  So on this instance the existential has to
produce a telescope different from `r.binders`: the residual case of §2–§3 is non-empty. -/
theorem not_bindersIndep_raiRec1 : ¬ raiRec1.BindersIndep raiPre 1 := by
  intro H
  have := H 0 0 raiF0 rfl (by simp [raiF0]) rfl 0 raiB rfl
  simp [VExpr.skips_iff, VExpr.Skips', raiB] at this

/-- **The control.**  What makes §7.2 reachable is that `raiEnv` declares a constant whose
*type* mentions the block; the staged environment of `VEnv.addIndTypes` cannot. -/
theorem raiCiP_type_hasBlock : VExpr.hasConstB raiD.blockNames raiCiP.type = true := by decide

/-- …and the control is a control: the binder itself is block-free, so `hbind` does not
exclude it, and the failure is not a `NoBlock` failure in disguise. -/
theorem raiB_hasNoBlock : VExpr.hasConstB raiD.blockNames raiB = false := by decide

/-! ### 7.3b The repaired statement *excludes* this instance, and `henv₀` is the half that does it

The repair added `hstage : env₀.addIndTypes D = some env` together with `henv₀ : env₀.Ordered`.
Three facts, all machine-checked, say exactly what that buys:

* `rai_staged` + `ordered_raiEnv0` + `ordered_raiEnv`: the pair is **satisfiable** — `raiEnv0`
  really is a staged environment of `raiD`, over `Ordered`.  So the hypothesis is not vacuous
  and does not empty the statement.
* `raiEnvP_add`: `hstage` **alone** is satisfied at §7.2's `raiEnv`, by the junk environment
  `raiEnvP` that declares `raiP` while `raiI` — the constant `raiP`'s type mentions — is
  undeclared.  `addIndTypes` is pure data, so nothing in `hstage` by itself rules that out.
  **This is why `henv₀` is in the statement**; without it the added hypothesis would be
  decoration.
* `rai_not_staged`: with `Ordered env₀`, `raiEnv` is **not** a staged environment of `raiD` at
  all.  So §7.2's witness no longer satisfies the hole's hypotheses, and
  `rai_junk_not_ordered` is the same fact read the other way.
-/

theorem raiD_typeConsts : raiD.typeConsts = [(raiI, raiCiI)] := rfl

theorem ordered_raiEnv0 : VEnv.Ordered raiEnv0 := by
  refine .const .empty ?_ raiEnv0_add
  exact ⟨_, VEnv.HasType.sort trivial⟩

theorem ordered_raiEnv : VEnv.Ordered raiEnv := by
  refine .const ordered_raiEnv0 ?_ raiEnv_add
  exact ⟨_, VEnv.IsDefEq.forallEDF (raiI_hasType (by simp [raiEnv0]))
    (VEnv.HasType.sort trivial)⟩

/-- **`hstage` is inhabited.**  `raiEnv0` is a staged environment of `raiD`, over `Ordered`. -/
theorem rai_staged : VEnv.empty.addIndTypes raiD = some raiEnv0 := by
  show List.foldlM (fun env (c : Lean.Name × VConstant) => env.addConst c.1 c.2)
    VEnv.empty raiD.typeConsts = some raiEnv0
  rw [raiD_typeConsts]
  simpa using raiEnv0_add

/-- **The repaired statement excludes §7.2's witness.**  No `Ordered` environment stages `raiD`
into `raiEnv`: staging leaves `raiP` declared while `raiI` is not, and `Ordered.constsInC` says
a declared type mentions only declared constants. -/
theorem rai_not_staged :
    ¬ ∃ env₀ : VEnv, VEnv.Ordered env₀ ∧ env₀.addIndTypes raiD = some raiEnv := by
  rintro ⟨env₀, hord, h⟩
  have h' : env₀.addConst raiI raiCiI = some raiEnv := by
    simpa [VEnv.addIndTypes, VEnv.addConstList, raiD_typeConsts] using h
  rcases hI : env₀.constants raiI with _ | ci
  · rw [VEnv.addConst, hI] at h'
    injection h' with h'
    have hP : env₀.constants raiP = some raiCiP := by
      have := congrArg (fun e => e.constants raiP) h'
      simp only at this
      rw [if_neg raiI_ne_raiP] at this
      simpa [raiEnv] using this
    have hc := hord.constsInC hP
    have hIc : env₀.contains raiI := by
      simpa [raiCiP, VExpr.ConstsIn] using hc
    obtain ⟨ci, hci⟩ := hIc
    rw [hI] at hci; exact absurd hci nofun
  · rw [VEnv.addConst, hI] at h'; exact absurd h' nofun

/-- **The control on the control**: `hstage` *without* `henv₀` does not exclude §7.2 — this junk
environment stages `raiD` into `raiEnv`, and it declares `raiP : raiI → Sort 1` while `raiI` is
undeclared. -/
def raiEnvP : VEnv where
  constants n := if raiP = n then some raiCiP else none
  defeqs _ := False

theorem raiEnvP_add : raiEnvP.addIndTypes raiD = some raiEnv := by
  have : raiEnvP.addConst raiI raiCiI = some raiEnv := by
    simp only [VEnv.addConst, raiEnvP, show (if raiP = raiI then some raiCiP else none) = none from
      if_neg (Ne.symm raiI_ne_raiP)]
    show _ = some raiEnv
    unfold raiEnv
    simp only [Option.some.injEq, VEnv.mk.injEq]
    refine ⟨?_, trivial⟩
    funext n
    by_cases h : raiI = n
    · subst h; simp [Ne.symm raiI_ne_raiP]
    · by_cases h2 : raiP = n
      · subst h2; simp [h]
      · simp [h, h2]
  simpa [VEnv.addIndTypes, VEnv.addConstList, raiD_typeConsts] using this

/-- …and it is exactly `henv₀` that rejects it. -/
theorem rai_junk_not_ordered : ¬ VEnv.Ordered raiEnvP :=
  fun h => rai_not_staged ⟨raiEnvP, h, raiEnvP_add⟩

/-! ### 7.4 The repaired obligation is inhabited

Per `docs/vacuity-ledger.md` §0: a carried hypothesis must be discharged or shown inhabited.
`IndepUpgrade` is inhabited on §2's regime, with `TeleDefEq.refl` — which costs nothing —
so §6 is not conditional on something unattainable. -/


/-! ### 7.5 The shape the docstring says needs repairing cannot occur in `r.binders`

`exists_indep`'s docstring argues: *"every occurrence of `a` in a well-formed `B` sits under a
redex and disappears under `whnf`; the `(fun _ : T => Nat) r` example in `pos`'s `none`-branch
comment is the shape."*

That shape is **not an admissible binder**.  `T` is the earlier recursive field's type
`∀ ξ₀, I p π₀`, which mentions a block constant, so the redex mentions one too — and `hbind`
(a hypothesis of the hole, and the `∀ B ∈ r.binders, D.NoBlock B` conjunct of
`VIndField.WF.pos`) demands binders be **syntactically** block-free.  `raiRedex_not_noBlock`
machine-checks it at §7.2's block.

Two caveats, both of which matter:

* **[analysis, not proved]** the redex's *domain* need not be `T` written out: any block-free
  type definitionally equal to `T` would do, and whether one exists at the staged environment
  is a rigidity question (`Theory/Typing/RigidConstPrice.lean`), not a syntactic one.  So this
  refutes the docstring's *example*, not every redex route.
* the docstring's "sits under a redex" is also not exhaustive.  `raiB = raiP x` is block-free,
  well-typed, mentions `x`, and is **not** a redex: `VExpr.betaHead raiB = raiB`
  (`raiB_betaHead`).  Under the freshness hypothesis §7.3 asks for, such a shape needs a
  constant the staged environment cannot hold; without it, it exists — which is §7.2. -/

def raiRedex : VExpr := .app (.lam (.const raiI []) (.sort .zero)) (.bvar 0)

/-- **The docstring's repair example is not an admissible binder.** -/
theorem raiRedex_not_noBlock : ¬ raiD.NoBlock raiRedex := by decide

/-- …and it is genuinely the docstring's shape: it *is* a redex, contracting away the
occurrence, which is what the docstring's argument uses. -/
theorem raiRedex_betaHead : VExpr.betaHead raiRedex = .sort .zero := rfl

/-- **The `raiB` route is not a redex**, so the docstring's "sits under a redex" account does
not cover it. -/
theorem raiB_betaHead : VExpr.betaHead raiB = raiB := rfl

theorem indepUpgrade_of_bindersIndep {env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {r : VIndRecArg}
    (hbind : ∀ B ∈ r.binders, D.NoBlock B) (h : r.BindersIndep pre i) :
    r.IndepUpgrade env D Γ pre i :=
  ⟨r.binders, VEnv.TeleDefEq.refl, hbind, h⟩

end RecArgIndep

/-! ## 8. Axiom audit

Every headline result of this file, `#print axioms`-ed.  `indepGoal_of_exists_indep` is the
one that carries `sorryAx`, and it carries it *by construction*: it is the faithfulness check
that applies the hole.  Everything else must show `[propext, Quot.sound, Classical.choice]` or
less. -/

section Audit
#print axioms Lean4Lean.VIndRecArg.indepGoal_of_exists_indep
#print axioms Lean4Lean.VIndRecArg.bindersIndep_of_binders_nil
#print axioms Lean4Lean.VIndRecArg.bindersIndep_of_pre_nil
#print axioms Lean4Lean.VIndRecArg.bindersIndep_of_pre_norec
#print axioms Lean4Lean.VIndRecArg.indepGoal_of_bindersIndep
#print axioms Lean4Lean.VIndRecArg.exists_indep_of_pre_norec
#print axioms Lean4Lean.VIndRecArg.exists_indep_of_binders_nil
#print axioms Lean4Lean.VIndRecArg.exists_indep_of_i_zero
#print axioms Lean4Lean.RecArgIndep.teleDefEq_length_eq
#print axioms Lean4Lean.RecArgIndep.teleDefEq_isDefEqCtx
#print axioms Lean4Lean.RecArgIndep.isDefEqType_trans_of_sortUniq
#print axioms Lean4Lean.VIndField.posSome_of_wf
#print axioms Lean4Lean.RecArgIndep.posSome_transport
#print axioms Lean4Lean.RecArgIndep.posSome_transport_of_indepGoal
#print axioms Lean4Lean.RecArgIndep.indepGoal_of_indepUpgrade
#print axioms Lean4Lean.RecArgIndep.indepUpgrade_of_bindersIndep
#print axioms Lean4Lean.RecArgIndep.wf_raiEnv
#print axioms Lean4Lean.RecArgIndep.rai_hyps
#print axioms Lean4Lean.RecArgIndep.not_bindersIndep_raiRec1
#print axioms Lean4Lean.RecArgIndep.raiCiP_type_hasBlock
#print axioms Lean4Lean.RecArgIndep.raiB_hasNoBlock
#print axioms Lean4Lean.RecArgIndep.ordered_raiEnv
#print axioms Lean4Lean.RecArgIndep.rai_staged
#print axioms Lean4Lean.RecArgIndep.rai_not_staged
#print axioms Lean4Lean.RecArgIndep.raiEnvP_add
#print axioms Lean4Lean.RecArgIndep.rai_junk_not_ordered
#print axioms Lean4Lean.RecArgIndep.isDefEqCtx_refl_suffix
#print axioms Lean4Lean.RecArgIndep.isDefEqType_refl_r
#print axioms Lean4Lean.RecArgIndep.raiRedex_not_noBlock
#print axioms Lean4Lean.RecArgIndep.raiRedex_betaHead
#print axioms Lean4Lean.RecArgIndep.raiB_betaHead
end Audit

end Lean4Lean
