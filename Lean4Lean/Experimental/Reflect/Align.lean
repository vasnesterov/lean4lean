import Lean4Lean.Experimental.Bridge
import Lean4Lean.Theory.Typing.Strong

/-!
# Reflection `SExpr → VExpr`: the alignment core

`SExpr.mk : VExpr → SExpr` is not injective — it replaces each `VLevel` by its semantic
quotient `SLevel`, so `.sort (max u u)` and `.sort u` share an image.  A reflection of an
`SExpr.IsDefEq` derivation therefore cannot produce *the* `VExpr` preimage of a term, only
*a* preimage, and two branches of the induction that agree on the `SExpr` side may hand back
different `VExpr` terms.

**Every such mismatch is discharged the same way**, and that is what this file packages.  If
`mk x = mk y` then `x` and `y` differ only in `≈`-equivalent levels, which is exactly
`VEnv.EqUpToLevels` (`Theory/Typing/Strong.lean`), and `IsDefEq.eqUpToLevels` transports a
derivation across it.  The three `align*` lemmas below are that observation applied at each
of the three positions a derivation has: its type, its right endpoint, its left endpoint.

They are why the reflection's congruence, binder and transitivity cases are short: a case
that must reconcile two preimages spends one `align` call rather than an inlined
`EqUpToLevels` argument.  Measured, not hoped: see `docs/research-forallE-inv.md` §13.

## Where this sits

`Lean4Lean/Experimental/Reflect/` holds the reflection in three files, split so that the
bulk of it is insulated from the shape model:

* `Align.lean` (this file) — the alignment core;
* the reflection induction itself, which takes `trans'`'s sort-uniqueness as an **explicit
  hypothesis**, in the exact shape of `SExpr.IsDefEq.uniq_sort` and crucially *with*
  `Ctx.WF Γ`;
* a capstone that discharges that hypothesis from `uniq_sort` and states
  `IsDefEqU.forallE_inv`.

Only the capstone imports `Experimental/UniqueTyping.lean`, and so only the capstone depends
on `ShapeLogRelAdequacy.lean` and `ShapeLogRel.lean`.  The `Ctx.WF Γ` is what makes that
hypothesis a *seam* rather than a deferral: it is dischargeable today, unlike
`IsDefEq.toIsDefEq'`'s `huniq`, which quantifies over all contexts with no well-formedness
and is not.  See `docs/research-forallE-inv.md` §12.2 and §13.4.

## What is *not* here

The reflection itself, and the `∃ U'` threading it needs (`VLevel.exists_wf`,
`IsDefEq.mono_uvars`, `IsDefEq.descend`, all in `Theory/Typing/Strong.lean`).

Nothing here mentions `SExpr.IsDefEq`, so this file does not depend on the shape model:
its only import from `Experimental/` is `Bridge.lean`, which is `SExpr.lean` plus the `mk`
homomorphism lemmas.  `[Params]` appears only because `SLevel.mk_inj` carries it as a
section variable, and is confined to the second half of the file.

## Working note: a `simp` lemma that has already fired

**When a `rw`/`simp` lemma will not fire on a goal that visibly contains its pattern, check
whether some other `simp` lemma has already rewritten that goal into a normal form — and if
so, state the normal form as well.**

Two streams have now lost a round to this.  Here it was `SLevel.map_mk_map_rep`, stated as
`(ls.map rep).map mk = ls`, which never matches: `List.map_map` is itself `simp` and rewrites
the goal to `ls.map (mk ∘ rep) = ls` first.  The fix is `SLevel.mk_comp_rep : mk ∘ rep = id`,
the same fact in the shape the goal actually reaches.  The other instance is recorded at
`Theory/Inductive/Lemmas.lean:47–51`, in a file this stream would never open — hence the
copy.
-/

namespace Lean4Lean

open VExpr

/-! ## Inverting `mk` on skeletons

`mk` is structural, so a `VExpr` whose image has a given head constructor has that head
constructor.  Six lemmas, one per `VExpr` former; the reflection uses them to learn, from an
induction hypothesis about an `SExpr` type, the shape of the `VExpr` preimage it produced. -/

theorem SExpr.mk_eq_bvar {e : VExpr} {i} (h : SExpr.mk e = .bvar i) : e = .bvar i := by
  cases e <;> simp [SExpr.mk] at h
  exact h ▸ rfl

theorem SExpr.mk_eq_sort {e : VExpr} {u : SLevel} (h : SExpr.mk e = .sort u) :
    ∃ u', e = .sort u' ∧ SLevel.mk u' = u := by
  cases e <;> simp [SExpr.mk] at h
  exact ⟨_, rfl, h⟩

theorem SExpr.mk_eq_const {e : VExpr} {c ls} (h : SExpr.mk e = .const c ls) :
    ∃ ls', e = .const c ls' ∧ ls'.map SLevel.mk = ls := by
  cases e <;> simp [SExpr.mk] at h
  exact ⟨_, h.1 ▸ rfl, h.2⟩

theorem SExpr.mk_eq_app {e : VExpr} {f a : SExpr} (h : SExpr.mk e = .app f a) :
    ∃ f' a', e = .app f' a' ∧ SExpr.mk f' = f ∧ SExpr.mk a' = a := by
  cases e <;> simp [SExpr.mk] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem SExpr.mk_eq_lam {e : VExpr} {A b : SExpr} (h : SExpr.mk e = .lam A b) :
    ∃ A' b', e = .lam A' b' ∧ SExpr.mk A' = A ∧ SExpr.mk b' = b := by
  cases e <;> simp [SExpr.mk] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem SExpr.mk_eq_forallE {e : VExpr} {A B : SExpr} (h : SExpr.mk e = .forallE A B) :
    ∃ A' B', e = .forallE A' B' ∧ SExpr.mk A' = A ∧ SExpr.mk B' = B := by
  cases e <;> simp [SExpr.mk] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

/-! ## A section of `SLevel.mk`

`SLevel` is `{ f : List Nat → Nat // ∃ l : VLevel, l.eval = f }` (`Experimental/SExpr.lean`),
so it carries its own representative and choosing one needs nothing but `Exists.choose`.
The representative need not be `VLevel.WF` at any particular count — see the section note on
descent in `Theory/Typing/Strong.lean`, which is what makes that harmless. -/

noncomputable def SLevel.rep (s : SLevel) : VLevel := s.2.choose

@[simp] theorem SLevel.mk_rep (s : SLevel) : SLevel.mk s.rep = s := Subtype.ext s.2.choose_spec

/-- Choosing representatives levelwise and mapping back is the identity.  This is what makes
the `const` and `extra` cases land on the nose rather than up to `≈`: composed with
`SExpr.mk_instL`, it gives `mk (e.instL (ls.map rep)) = (mk e).instL ls` exactly.

Stated in the composed form too, because `List.map_map` is itself `simp` and fires first —
without `mk_comp_rep` a goal `(ls.map rep).map mk = ls` normalises to
`ls.map (mk ∘ rep) = ls` and then sticks. -/
@[simp] theorem SLevel.mk_comp_rep : SLevel.mk ∘ SLevel.rep = id := funext SLevel.mk_rep

@[simp] theorem SLevel.map_mk_map_rep (ls : List SLevel) :
    (ls.map SLevel.rep).map SLevel.mk = ls := by simp

/-- `VLevel.exists_wf_list` with the bound taken above an ambient count, which is the form
the reflection's `U ≤ U'` conclusion wants. -/
theorem VLevel.exists_wf_list_ge (U : Nat) (ls : List VLevel) :
    ∃ U', U ≤ U' ∧ ∀ l ∈ ls, l.WF U' :=
  let ⟨_, hn⟩ := VLevel.exists_wf_list ls
  ⟨Nat.max U _, Nat.le_max_left .., fun _ hl => (hn _ hl).mono (Nat.le_max_right ..)⟩

theorem VLevel.exists_wf_ge (U : Nat) (l : VLevel) : ∃ U', U ≤ U' ∧ l.WF U' :=
  let ⟨_, hn⟩ := VLevel.exists_wf l
  ⟨Nat.max U _, Nat.le_max_left .., hn.mono (Nat.le_max_right ..)⟩

/-- `OnCtx (env.IsType ·)` lifted along `U ≤ U'`: the reflection's context invariant has to
follow the `∃ U'` its branches produce. -/
theorem OnCtx.mono_uvars {env : VEnv} {Γ : List VExpr} {U U' : Nat} (le : U ≤ U') :
    OnCtx Γ (env.IsType U) → OnCtx Γ (env.IsType U') :=
  OnCtx.mono fun ⟨_, h⟩ => ⟨_, h.mono_uvars le⟩

variable [Params]

/-- Inverting `Lookup` through `mk`: the `bvar` case's whole content.  The forward
direction is `Lookup.toSExpr` (`Experimental/Bridge.lean`). -/
theorem Lookup.of_map_mk {Γ : List VExpr} : ∀ {i : Nat} {A' : SExpr},
    SExpr.Lookup (Γ.map SExpr.mk) i A' → ∃ A, Lookup Γ i A ∧ SExpr.mk A = A' := by
  induction Γ with
  | nil => intro _ _ h; cases h
  | cons ty _ ih =>
    intro _ _ h
    cases h with
    | zero => exact ⟨ty.lift, .zero, by simp⟩
    | succ h => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, .succ h1, by simp [h2]⟩

theorem VLevel.forall₂_of_map_mk : ∀ {us us' : List VLevel},
    us.map SLevel.mk = us'.map SLevel.mk → List.Forall₂ (· ≈ ·) us us'
  | [], [] => fun _ => .nil
  | [], _::_ => by simp
  | _::_, [] => by simp
  | _::_, _::_ => by
    intro h; simp only [List.map_cons, List.cons.injEq] at h
    exact .cons (SLevel.mk_inj.1 h.1) (VLevel.forall₂_of_map_mk h.2)

namespace VEnv

/-! ## Alignment -/

/-- `SExpr.mk` erases exactly the level information `EqUpToLevels` forgives: two `VExpr`s
with the same image and well-formed levels are `EqUpToLevels`-related. -/
theorem EqUpToLevels.of_mk : ∀ {e e' : VExpr}, SExpr.mk e = SExpr.mk e' →
    e.LevelWF U → e'.LevelWF U → EqUpToLevels U e e' := by
  intro e
  induction e with intro e' eq w1 w2 <;> cases e' <;>
    simp [SExpr.mk, VExpr.LevelWF] at eq w1 w2 ⊢
  | bvar => exact eq ▸ .bvar
  | sort => exact .sort w1 w2 (SLevel.mk_inj.1 eq)
  | const => exact eq.1 ▸ .const w1 w2 (VLevel.forall₂_of_map_mk eq.2)
  | app _ _ ih1 ih2 => exact .app (ih1 eq.1 w1.1 w2.1) (ih2 eq.2 w1.2 w2.2)
  | lam _ _ ih1 ih2 => exact .lam (ih1 eq.1 w1.1 w2.1) (ih2 eq.2 w1.2 w2.2)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 eq.1 w1.1 w2.1) (ih2 eq.2 w1.2 w2.2)

variable {env : VEnv} {Γ : List VExpr} {U : Nat} {e₁ e₂ A : VExpr}

/-- **Align the type.**  Retype a derivation at any `mk`-equal, level-well-formed type.
This is the form the congruence and binder cases want: two sibling induction hypotheses
produce two preimages of one `SExpr` type, and one of them has to give way. -/
theorem IsDefEq.alignT (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEq U Γ e₁ e₂ A) {A' : VExpr} (wA' : A'.LevelWF U)
    (eq : SExpr.mk A = SExpr.mk A') : env.IsDefEq U Γ e₁ e₂ A' := by
  have ⟨_, _, wA⟩ := h.levelWF (CtxStrong.strong henv hΓ).levelWF
  have ⟨_, hty⟩ := h.isType henv hΓ
  exact (hty.eqUpToLevels henv hΓ (EqUpToLevels.of_mk eq wA wA')).defeqDF h

/-- **Align the right endpoint.** -/
theorem IsDefEq.alignR (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEq U Γ e₁ e₂ A) {e₂' : VExpr} (w : e₂'.LevelWF U)
    (eq : SExpr.mk e₂ = SExpr.mk e₂') : env.IsDefEq U Γ e₁ e₂' A := by
  have ⟨_, w2, _⟩ := h.levelWF (CtxStrong.strong henv hΓ).levelWF
  exact h.eqUpToLevels henv hΓ (EqUpToLevels.of_mk eq w2 w)

/-- **Align the left endpoint.**  What `trans` needs, to make one branch's preimage of the
middle term agree with the other's. -/
theorem IsDefEq.alignL (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEq U Γ e₁ e₂ A) {e₁' : VExpr} (w : e₁'.LevelWF U)
    (eq : SExpr.mk e₁ = SExpr.mk e₁') : env.IsDefEq U Γ e₁' e₂ A :=
  (h.symm.alignR henv hΓ w eq).symm

/-! ## Descent, keeping the type

`IsDefEq.descend` (`Theory/Typing/Strong.lean`) drops the type into an existential, which is
all `IsDefEqU` needs.  The `forallE_inv` statement in `Theory/Typing/Injectivity.lean` is
sharper — it says the components are equal *at a sort* — so the capstone needs the same
descent with the type kept.  Same proof; only the last line differs. -/

omit [Params] in
theorem _root_.Lean4Lean.VExpr.LevelWF.mono (le : U ≤ U') {e : VExpr} :
    e.LevelWF U → e.LevelWF U' := by
  induction e with intro h <;> simp [VExpr.LevelWF] at h ⊢
  | sort => exact VLevel.WF.mono le h
  | const _ us => exact fun _ hu => VLevel.WF.mono le (h _ hu)
  | app _ _ ih1 ih2 | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩

omit [Params] in
/-- `IsDefEq.descend` with the type retained: the descended derivation lives at
`A.instL (VLevel.params U)`, which is a sort whenever `A` was. -/
theorem IsDefEq.descend' {U U' : Nat} {e₁ e₂ A a₁ a₂ : VExpr}
    (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEq U' Γ e₁ e₂ A)
    (h1 : EqUpToLevels U' e₁ a₁) (h2 : EqUpToLevels U' e₂ a₂)
    (w1 : a₁.LevelWF U) (w2 : a₂.LevelWF U) :
    env.IsDefEq U Γ a₁ a₂ (A.instL (VLevel.params U)) := by
  have key := H.instL (ls := VLevel.params U) VLevel.params_wf
  rw [OnCtx.instL_id (CtxStrong.strong henv hΓ).levelWF] at key
  have E1 : EqUpToLevels U (e₁.instL (VLevel.params U)) a₁ := by
    have h := EqUpToLevels.instL' (U := U) VLevel.params_wf h1
    rwa [VExpr.LevelWF.instL_id w1] at h
  have E2 : EqUpToLevels U (e₂.instL (VLevel.params U)) a₂ := by
    have h := EqUpToLevels.instL' (U := U) VLevel.params_wf h2
    rwa [VExpr.LevelWF.instL_id w2] at h
  exact ((key.eqUpToLevels henv hΓ E2).symm.eqUpToLevels henv hΓ E1).symm

end VEnv

end Lean4Lean
