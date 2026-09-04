import Lean4Lean.Theory.Typing.ConfluenceRebuildPrice

/-!
# Scoping the Church-Rosser-over-`IsDefEqSE` target: the new rules' orientation

Round of 2026-09-04, `docs/handoff-crse.md`; **§2 and §4 restated 2026-09-04** for the flip of
`VEnv.ParRedSE.structEta`, `docs/handoff-flipland.md`.  **Pricing only** — nothing here repairs
anything and nothing here is a confluence result.

`Theory/Typing/ConfluenceRebuildPrice.lean` §4 re-erects the confluence layer over the
fourteen-constructor relation, adding `NormalEqSE.structEtaL`/`structEtaR` to the conversion and
`ParRedSE.structEta` to the reduction.  Its §7 checks vacuity — but **only at `refEnv`**, where
its own §6 proves the three new rules are dead (`refEnv_no_structEtaSite`).

**The orientation changed under this file.**  The round of 2026-09-04 that first wrote it read
`ParRedSE.structEta` as an *expansion*, `ParRedSE Γ e (η e)`; §1 showed the site re-fires on its
own output, and §2 concluded from that that `VEnv.parRedSES_rigid`'s hypothesis is **false** at
every site, which is what refuted the *method*.  `Theory/Typing/EtaOrient.lean` priced the
contraction and the rule was flipped to `ParRedSE Γ (η e) e`.  §1 and §3 below are **unchanged**
(measured, not assumed: neither mentions a reduction relation).  §2 and §4 are the two statements
that had to be rewritten, and the direction they moved in is the measurement worth keeping.

## What is proved

* §1 `StructEtaSite.iterate` — the site **re-fires on its own output**, and the only thing it
  needs is that the output is typed at the same type.  Every other field of `StructEtaSite` is
  about `S, D, j, T, C, us, ps` and is untouched by replacing `e`.  So the η-expansion is a map
  that re-applies to its own result: `e, η e, η (η e), …` are all sites.  **This is orientation
  blind** — it is a fact about `StructEtaSite`, not about `ParRedSE`, which is why the flip left
  it alone.
* §2 `VEnv.parRedSE_rigid_bvar` and `parRedSE_rigid_sort` — **`VEnv.parRedSES_rigid`'s hypothesis
  is satisfiable, unconditionally**: at every `Params` instance, in every context, with no side
  condition, an atom is `ParRedSE`-rigid.  Three constructors could conclude about an atom and two
  are refuted syntactically — `extra` because `Pattern.Matches` only matches `.const c ls` and
  `.app f a`, and `structEta` because its **redex** is now a `const`-headed application spine.
  This is the flip's whole yield, and it is the exact negation of what stood here before it:
  the pre-flip §2 was `not_parRedSE_rigid_of_structEtaSite`, `¬ (∀ o, ParRedSE Γ e o → o = e)` at
  any site with `η e ≠ e`, and `EtaOrient.lean` §6's positive-field witness is a site whose
  subject is `.bvar 0`.  **So the pre-flip §2 did not survive in its own subject: it is now
  false, not merely unproved.**  What survives is the same fact moved to the other endpoint —
  `not_parRedSE_rigid_etaExpansionG_of_structEtaSite`: the **expansion** `η e` is the redex, so
  *it* is not rigid, under the same two hypotheses and by the same one-line proof up to `.symm`.
* §3 `etaExpansionG_idem_of_no_fields` — the phenomenon is a **positive-fields** one only.  At
  zero fields `VInductDecl'.etaExpansionG` does not mention `e` at all
  (`etaExpansionG_of_no_fields`: it is `(.const C.name us).mkApp ps`), so it is a *constant* map
  and its own fixed point after one step.  Also orientation blind, also unchanged.
* §4 `VEnv.StructEtaStep`, `.sizeOf_lt`, `no_infinite_structEtaStep` and
  `parRedSES_etaIter_down` — **the regress is gone.**  Before the flip this section said the
  opposite in the sharpest available form: `parRedSES_etaIter` built an unbounded `ParRedSES`
  chain `e ≫ η e ≫ η (η e) ≫ …` out of §1, conditional only on every stage being typed.  The
  chain is still there and every stage is still a site (`StructEtaSite.at_stage`, kept verbatim,
  and `EtaStagesTyped` with it) — the flip does not delete the tower, it **reverses the arrows**:
  `parRedSES_etaIter_down` walks the same tower *into* `e`, and `no_infinite_structEtaStep` says
  no chain of contractions runs forever, because each step strictly decreases `sizeOf`.
  (The pre-flip module docstring here promised a declaration called `EtaRegress`; **no such
  declaration ever existed** in this file — the `Prop` is `EtaStagesTyped`.  Corrected
  2026-09-04.)

## Why this is a pricing answer and not a repair

§3 lines up with the model side exactly.  `Theory/SetModel/RecPropSingleton.lean`'s
`eq_singleton_of_recProp` and `Theory/SetModel/RecTypePeel.lean` §8's
`eq_singleton_of_mem_interp_mkPi3` validate **zero-field** surjective pairing, and validate it as
*forced* rather than chosen.  Zero fields is precisely the case where §3 says the eta map is a
fixed point and no orientation question arises.

What the flip bought is exactly §2: every confluence argument in this tree (`ParRed.triangle`'s
measure, `KDiamondJoin.joins_normal_iff`, `parRedSES_rigid`, `CParRed`'s neutrality test) is
stated in terms of `ParRed`-normal forms, and under the expansion the extended relation had none
at a positive-field structure.  It has them now, at the atoms, unconditionally.

What the flip did **not** buy: `NormalEqSE.structEtaL`/`structEtaR` still recurse *on* `η e`
while the reduction now runs `η e ⟶ e`, so at a `structEtaL` node the reduction available at the
subject no longer reaches the term the conversion rule recurses on.  That cost lands on
`NormalEq.descend`, and `EtaOrient.lean` §7 checks that it moves neither of the two refutations
(`descendSEC_uniq_sortUniq_not_all`, `not_parRedStatementSEC_of_propMajor`) — the statement it
costs is already refuted in **both** orientations, at 13 constructors and again at 14.
-/

namespace Lean4Lean

open VExpr

/-! ## §0 Shape and `sizeOf` under `VExpr.mkApp`

**Relocated here 2026-09-04, from `Theory/Typing/EtaOrient.lean` §1–§2, under their existing
fully-qualified names** (so no citer moves).  They have to be upstream of §2 and §4, which need
them, and `EtaOrient.lean` is *downstream* of this file — that mismatch is what forced this
file to carry private copies for one round; both sets are now gone in favour of these.

Nothing here is about eta orientation.  The two facts that matter are: an η-expansion is a
`const`-headed application spine (so it is never an atom, which is §2), and it strictly contains
its own subject at positive fields (so contracting it decreases `sizeOf`, which is §4). -/

namespace VExpr

theorem sizeOf_le_mkApp : ∀ (l : List VExpr) (f : VExpr), sizeOf f ≤ sizeOf (f.mkApp l)
  | [], _ => Nat.le_refl _
  | a :: as, f => by
    refine Nat.le_trans ?_ (sizeOf_le_mkApp as (.app f a))
    simp; omega

theorem mkApp_eq_or_app :
    ∀ (l : List VExpr) (f : VExpr), f.mkApp l = f ∨ ∃ g a, f.mkApp l = .app g a
  | [], _ => .inl rfl
  | a :: as, f => by
    rcases mkApp_eq_or_app as (.app f a) with h | ⟨g, b, h⟩
    · exact .inr ⟨f, a, by simpa [VExpr.mkApp] using h⟩
    · exact .inr ⟨g, b, by simpa [VExpr.mkApp] using h⟩

theorem sizeOf_lt_mkApp_of_mem :
    ∀ (l : List VExpr) {a : VExpr}, a ∈ l → ∀ (f : VExpr), sizeOf a < sizeOf (f.mkApp l)
  | b :: as, a, h, f => by
    rcases List.mem_cons.1 h with rfl | h
    · refine Nat.lt_of_lt_of_le ?_ (sizeOf_le_mkApp as (.app f a))
      simp
    · exact sizeOf_lt_mkApp_of_mem as h _

end VExpr

namespace VInductDecl'

variable (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)

theorem sizeOf_lt_projCoreG {ps is : List VExpr} {i j : Nat} {earlier : List VExpr} {e : VExpr} :
    sizeOf e < sizeOf (D.projCoreG T C us ps is i j earlier e) := by
  show sizeOf e < sizeOf ((VExpr.const (Lean.mkRecName T.name) (D.projLvls C us i)).mkApp _)
  exact VExpr.sizeOf_lt_mkApp_of_mem _ (by simp) _

theorem sizeOf_lt_projTermG {ps is : List VExpr} {i j : Nat} {e : VExpr} :
    sizeOf e < sizeOf (D.projTermG T C us ps is i j e) :=
  D.sizeOf_lt_projCoreG T C us

/-- **The expansion strictly grows its subject, at positive fields.**  The subject sits inside the
zeroth projection, which is one of the spine arguments. -/
theorem sizeOf_lt_etaExpansionG {ps : List VExpr} {j : Nat} {e : VExpr}
    (hf : 0 < C.fields.length) :
    sizeOf e < sizeOf (D.etaExpansionG T C us ps j e) := by
  have hmem : D.projTermG T C us ps [] 0 j e ∈ ps ++ D.projAllG T C us ps j e := by
    refine List.mem_append_right _ ?_
    simpa [projAllG] using ⟨0, hf, rfl⟩
  exact Nat.lt_trans (D.sizeOf_lt_projTermG T C us)
    (VExpr.sizeOf_lt_mkApp_of_mem _ hmem _)

theorem etaExpansionG_ne_bvar {ps : List VExpr} {j : Nat} {e : VExpr} {i : Nat} :
    D.etaExpansionG T C us ps j e ≠ .bvar i := by
  rcases VExpr.mkApp_eq_or_app (ps ++ D.projAllG T C us ps j e) (.const C.name us) with h | ⟨g, a, h⟩ <;>
    rw [etaExpansionG, h] <;> exact nofun

theorem etaExpansionG_ne_sort {ps : List VExpr} {j : Nat} {e : VExpr} {u : VLevel} :
    D.etaExpansionG T C us ps j e ≠ .sort u := by
  rcases VExpr.mkApp_eq_or_app (ps ++ D.projAllG T C us ps j e) (.const C.name us) with h | ⟨g, a, h⟩ <;>
    rw [etaExpansionG, h] <;> exact nofun

theorem etaExpansionG_ne_lam {ps : List VExpr} {j : Nat} {e A b : VExpr} :
    D.etaExpansionG T C us ps j e ≠ .lam A b := by
  rcases VExpr.mkApp_eq_or_app (ps ++ D.projAllG T C us ps j e) (.const C.name us) with h | ⟨g, a, h⟩ <;>
    rw [etaExpansionG, h] <;> exact nofun

theorem etaExpansionG_ne_forallE {ps : List VExpr} {j : Nat} {e A B : VExpr} :
    D.etaExpansionG T C us ps j e ≠ .forallE A B := by
  rcases VExpr.mkApp_eq_or_app (ps ++ D.projAllG T C us ps j e) (.const C.name us) with h | ⟨g, a, h⟩ <;>
    rw [etaExpansionG, h] <;> exact nofun

theorem etaExpansionG_ne {ps : List VExpr} {j : Nat} {e : VExpr} (hf : 0 < C.fields.length) :
    D.etaExpansionG T C us ps j e ≠ e :=
  fun h => absurd (h ▸ D.sizeOf_lt_etaExpansionG T C us hf) (Nat.lt_irrefl _)

end VInductDecl'

namespace VEnv

/-! ## §1 The site re-fires on its own output

Unchanged by the flip, and unchangeable by it: `StructEtaSite` mentions no reduction relation. -/

/-- **The structure-eta site is closed under its own expansion**, given only the expansion's
typing.  A `structure` update: the nine other fields of `VEnv.StructEtaSite` do not mention `e`.

Pre-flip this was the reason `ParRedSE.structEta` was a non-terminating expansion.  Post-flip it
is the reason the *tower* exists at all — §4 walks it downward. -/
theorem StructEtaSite.iterate {env : VEnv} {univs : Nat} {Γ : List VExpr} {S : Lean.Name}
    {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor}
    {us : List VLevel} {ps : List VExpr} {e : VExpr}
    (h : StructEtaSite env univs Γ S D j T C us ps e)
    (ht : env.IsDefEqSE univs Γ (D.etaExpansionG T C us ps j e)
      (D.etaExpansionG T C us ps j e) ((VExpr.const S us).mkApp ps)) :
    StructEtaSite env univs Γ S D j T C us ps (D.etaExpansionG T C us ps j e) :=
  { h with typed := ht }

/-! ## §2 Hence rigidity, and it is unconditional at the atoms

**Restated 2026-09-04 for the flip.**  What stood here was
`not_parRedSE_rigid_of_structEtaSite : ¬ (∀ o, ParRedSE Γ e o → o = e)`, given a site at `e` and
`D.etaExpansionG T C us ps j e ≠ e`, proved `fun hrig => hne (hrig _ (.structEta h))`.  Its
docstring read, verbatim:

> **`VEnv.parRedSES_rigid`'s hypothesis is false at a structure-eta site.**  One `structEta`
> step already moves `e`, so `e` is not `ParRedSE`-normal.
>
> `parRedSES_rigid` is the tool `not_parRedStatementSE_of_propMajor` uses, and `ParRed`-normality
> is the tool `ParRed.triangle`, `CParRed.exists` and `KDiamondJoin.joins_normal_iff` are built
> on.  All of them lose their footing here.

That statement is **refuted** by `parRedSE_rigid_bvar` below at every site whose subject is a
bound variable, and `EtaOrient.lean` §6's positive-field witness
(`MutField.declEnv_structEtaSite`) is such a site.  The negative fact itself is not gone, it has
moved one term along the step: it is `not_parRedSE_rigid_etaExpansionG_of_structEtaSite`. -/

section
variable [Params]
open Params

/-- **The reduction relation is rigid at a bound variable, with no side condition at all.**
Three constructors could conclude about a `.bvar`: `bvar` itself (which returns it unchanged),
`extra` (impossible — `Pattern.Matches` only matches `.const c ls` and `.app f a`), and
`structEta` (impossible — post-flip its *redex* is a `mkApp` of a `const`, never a `.bvar`).

The subject is stated as a variable plus an equation because `structEta`'s redex
`D.etaExpansionG …` is not a constructor application, so `cases` cannot unify against a fixed
`.bvar i` index. -/
theorem ParRedSE.rigid_of_eq_bvar {Γ : List VExpr} {a o : VExpr} (H : ParRedSE Γ a o) :
    ∀ i, a = .bvar i → o = a := by
  cases H with
  | bvar => exact fun _ _ => rfl
  | extra _ hm => exact fun _ h => absurd (h ▸ hm) nofun
  | structEta _ => exact fun _ h => absurd h (VInductDecl'.etaExpansionG_ne_bvar _ _ _ _)
  | _ => exact fun _ h => absurd h nofun

/-- **`VEnv.parRedSES_rigid`'s hypothesis is satisfiable**, at every `Params` instance and every
context: a bound variable is `ParRedSE`-rigid.

**This is the flip's yield, and it is also the refutation of what §2 used to say.**  Before the
flip the same statement was *false* at every structure-eta site whose subject is a `.bvar` —
that was `not_parRedSE_rigid_of_structEtaSite`, and `EtaOrient.lean` §6's positive-field witness
has subject `.bvar 0`.  Nothing about the environment, the site, or `Params` is needed here. -/
theorem parRedSE_rigid_bvar {Γ : List VExpr} {i : Nat} :
    ∀ o, ParRedSE Γ (.bvar i) o → o = .bvar i :=
  fun _ H => H.rigid_of_eq_bvar i rfl

/-- The same at a sort. -/
theorem ParRedSE.rigid_of_eq_sort {Γ : List VExpr} {a o : VExpr} (H : ParRedSE Γ a o) :
    ∀ u, a = .sort u → o = a := by
  cases H with
  | sort => exact fun _ _ => rfl
  | extra _ hm => exact fun _ h => absurd (h ▸ hm) nofun
  | structEta _ => exact fun _ h => absurd h (VInductDecl'.etaExpansionG_ne_sort _ _ _ _)
  | _ => exact fun _ h => absurd h nofun

theorem parRedSE_rigid_sort {Γ : List VExpr} {u : VLevel} :
    ∀ o, ParRedSE Γ (.sort u) o → o = .sort u :=
  fun _ H => H.rigid_of_eq_sort u rfl

/-- **The surviving half of the pre-flip §2.**  Rigidity still fails at a structure-eta site —
but at the **expansion**, not at the subject, because the expansion is now the redex.  Same two
hypotheses as the pre-flip statement, same one-line proof up to `.symm`.

This is the honest answer to "does the old negative result survive at all": *as a fact about the
η-expansion, yes; as a fact about the site's subject, no* — see `parRedSE_rigid_bvar`. -/
theorem not_parRedSE_rigid_etaExpansionG_of_structEtaSite {Γ : List VExpr} {S : Lean.Name}
    {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor}
    {us : List VLevel} {ps : List VExpr} {e : VExpr}
    (h : StructEtaSite env univs Γ S D j T C us ps e)
    (hne : D.etaExpansionG T C us ps j e ≠ e) :
    ¬ (∀ o, ParRedSE Γ (D.etaExpansionG T C us ps j e) o
        → o = D.etaExpansionG T C us ps j e) :=
  fun hrig => hne (hrig _ (.structEta h)).symm

end

/-! ## §3 …and the phenomenon is positive-fields-only

At zero fields the expansion does not mention its subject, so it is a constant map and one step
is all there is.  This is exactly the case the set model's forced validation covers.  Unchanged
by the flip: no reduction relation appears. -/

/-- **The zero-field expansion is its own fixed point.**  `etaExpansionG_of_no_fields` says both
sides are `(.const C.name us).mkApp ps`. -/
theorem etaExpansionG_idem_of_no_fields {D : VInductDecl'} {T : VIndType} {C : VIndCtor}
    {us : List VLevel} {ps : List VExpr} {j : Nat} {e : VExpr} (h : C.fields = []) :
    D.etaExpansionG T C us ps j (D.etaExpansionG T C us ps j e)
      = D.etaExpansionG T C us ps j e := by
  rw [VInductDecl'.etaExpansionG_of_no_fields _ _ _ _ h,
    VInductDecl'.etaExpansionG_of_no_fields _ _ _ _ h]

/-! ## §4 The tower, and it now terminates

**Restated 2026-09-04 for the flip.**  What stood here was

```lean
/-- **The unbounded chain.**  `ParRedSES` reaches the `n`-th η-expansion for every `n`. -/
theorem parRedSES_etaIter … : ∀ n, ParRedSES Γ e (etaIterG D T C us ps j n e)
  | 0 => .rfl
  | n + 1 => (parRedSES_etaIter h ht n).tail (.structEta (h.at_stage ht n))
```

under the section note "No witness of `StructEtaSite` exists anywhere in the tree, so the 'every
stage is typed' side condition cannot be discharged today" — which `EtaOrient.lean` §6 has since
falsified twice over (`MutField.unitEnv_structEtaSite`, `MutField.declEnv_structEtaSite`), and
`Theory/Typing/ParamsStruct.lean` §2–§3 removed the environment pin from as well.

`etaIterG`, `EtaStagesTyped` and `StructEtaSite.at_stage` are **kept verbatim** — they are facts
about the tower, not about the arrow, and `EtaOrient.lean` consumes all three.  What the flip
changes is the direction: the chain runs down, and it stops. -/

/-- The `n`-fold η-expansion. -/
def etaIterG (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (ps : List VExpr) (j : Nat) : Nat → VExpr → VExpr
  | 0, e => e
  | n + 1, e => D.etaExpansionG T C us ps j (etaIterG D T C us ps j n e)

section
variable [Params]
open Params

/-- **Every stage of the η-tower is typed** — the side condition §1 needs to iterate.  Stated as
a `Prop` rather than assumed inline, so that a witness can be pointed at it;
`EtaOrient.lean` §6 and `ParamsStruct.lean` §3 provide the sites, and this is the one remaining
premise. -/
def EtaStagesTyped (Γ : List VExpr) (S : Lean.Name) (D : VInductDecl') (j : Nat) (T : VIndType)
    (C : VIndCtor) (us : List VLevel) (ps : List VExpr) (e : VExpr) : Prop :=
  ∀ n, env.IsDefEqSE univs Γ (etaIterG D T C us ps j n e) (etaIterG D T C us ps j n e)
    ((VExpr.const S us).mkApp ps)

/-- **The site fires at every stage.**  Orientation blind: this is §1 iterated. -/
theorem StructEtaSite.at_stage {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
    {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e : VExpr}
    (h : StructEtaSite env univs Γ S D j T C us ps e)
    (ht : EtaStagesTyped Γ S D j T C us ps e) :
    ∀ n, StructEtaSite env univs Γ S D j T C us ps (etaIterG D T C us ps j n e)
  | 0 => h
  | n + 1 => (h.at_stage ht n).iterate (ht (n + 1))

/-- **The tower, traversed downward.**  The pre-flip `parRedSES_etaIter` reached the `n`-th
expansion *from* `e`; the same tower is now a `ParRedSES` chain *into* `e`, and by
`no_infinite_structEtaStep` below it stops there. -/
theorem parRedSES_etaIter_down {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
    {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e : VExpr}
    (h : StructEtaSite env univs Γ S D j T C us ps e)
    (ht : EtaStagesTyped Γ S D j T C us ps e) :
    ∀ n, ParRedSES Γ (etaIterG D T C us ps j n e) e
  | 0 => .rfl
  | n + 1 => ReflTransGen.trans (.tail .rfl (.structEta (h.at_stage ht n)))
      (parRedSES_etaIter_down h ht n)

/-- One structure-eta step, at a positive-field structure. -/
def StructEtaStep (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ S D j T C us ps, StructEtaSite env univs Γ S D j T C us ps b ∧
    0 < C.fields.length ∧ a = D.etaExpansionG T C us ps j b

theorem StructEtaStep.toParRedSE {Γ : List VExpr} {a b : VExpr}
    (h : StructEtaStep Γ a b) : ParRedSE Γ a b := by
  obtain ⟨_, _, _, _, _, _, _, hs, _, rfl⟩ := h; exact .structEta hs

/-- **The step strictly decreases `sizeOf`.**  This is the whole content of "the reduction does
not regress", and it is exactly what the pre-flip orientation could not have: §1 says the site
re-fires on its own output and `VInductDecl'.sizeOf_lt_etaExpansionG` says the output is strictly bigger,
so the pre-flip chain was `sizeOf`-*increasing* and unbounded. -/
theorem StructEtaStep.sizeOf_lt {Γ : List VExpr} {a b : VExpr}
    (h : StructEtaStep Γ a b) : sizeOf b < sizeOf a := by
  obtain ⟨_, D, _, T, C, us, _, _, hf, rfl⟩ := h
  exact D.sizeOf_lt_etaExpansionG T C us hf

/-- **No infinite chain of structure-eta steps.**  Stated as "no `Nat`-indexed chain", which is
the form a termination argument consumes — and it is the *direct negation* of what §4 used to
prove, `parRedSES_etaIter`, which built a chain of exactly this shape for every `n`. -/
theorem no_infinite_structEtaStep {Γ : List VExpr} (f : Nat → VExpr)
    (h : ∀ n, StructEtaStep Γ (f n) (f (n + 1))) : False := by
  have key : ∀ n, sizeOf (f n) + n ≤ sizeOf (f 0) := by
    intro n; induction n with
    | zero => omega
    | succ n ih => have := (h n).sizeOf_lt; omega
  have := key (sizeOf (f 0) + 1); omega

end

end VEnv

end Lean4Lean

/-! ## §5 The axiom sweep, inline

Per `docs/handoff-crse.md`'s process rule: `#print axioms` on **every** declaration this file
adds, in the file, where the claim cannot go stale.  One round in this project had a declaration
silently elaborate to a hole because `autoImplicit` bound an out-of-scope name; only its own
axioms line caught it.  Expected: everything `sorryAx`-free.

§0's eleven relocated lemmas are swept here too, since this file is now their home. -/

#print axioms Lean4Lean.VExpr.sizeOf_le_mkApp
#print axioms Lean4Lean.VExpr.mkApp_eq_or_app
#print axioms Lean4Lean.VExpr.sizeOf_lt_mkApp_of_mem
#print axioms Lean4Lean.VInductDecl'.sizeOf_lt_projCoreG
#print axioms Lean4Lean.VInductDecl'.sizeOf_lt_projTermG
#print axioms Lean4Lean.VInductDecl'.sizeOf_lt_etaExpansionG
#print axioms Lean4Lean.VInductDecl'.etaExpansionG_ne_bvar
#print axioms Lean4Lean.VInductDecl'.etaExpansionG_ne_sort
#print axioms Lean4Lean.VInductDecl'.etaExpansionG_ne_lam
#print axioms Lean4Lean.VInductDecl'.etaExpansionG_ne_forallE
#print axioms Lean4Lean.VInductDecl'.etaExpansionG_ne
#print axioms Lean4Lean.VEnv.StructEtaSite.iterate
#print axioms Lean4Lean.VEnv.ParRedSE.rigid_of_eq_bvar
#print axioms Lean4Lean.VEnv.parRedSE_rigid_bvar
#print axioms Lean4Lean.VEnv.ParRedSE.rigid_of_eq_sort
#print axioms Lean4Lean.VEnv.parRedSE_rigid_sort
#print axioms Lean4Lean.VEnv.not_parRedSE_rigid_etaExpansionG_of_structEtaSite
#print axioms Lean4Lean.VEnv.etaExpansionG_idem_of_no_fields
#print axioms Lean4Lean.VEnv.etaIterG
#print axioms Lean4Lean.VEnv.EtaStagesTyped
#print axioms Lean4Lean.VEnv.StructEtaSite.at_stage
#print axioms Lean4Lean.VEnv.parRedSES_etaIter_down
#print axioms Lean4Lean.VEnv.StructEtaStep
#print axioms Lean4Lean.VEnv.StructEtaStep.toParRedSE
#print axioms Lean4Lean.VEnv.StructEtaStep.sizeOf_lt
#print axioms Lean4Lean.VEnv.no_infinite_structEtaStep
