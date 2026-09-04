import Lean4Lean.Theory.Typing.CRSEScope

/-!
# Re-orienting the structure-eta reduction rule as a contraction

Round of 2026-09-04, `docs/handoff-etaorient.md`.  **Pricing and orientation only** — nothing here
is a confluence result and nothing here repairs `NormalEq.descend` or `NormalEq.parRed`.

`Theory/Typing/CRSEScope.lean` refuted the *method*, not the relation:
`VEnv.StructEtaSite.iterate` shows the eta site re-fires on its own output needing only that the
output is typed, so `VEnv.ParRedSE.structEta` — stated as `ParRedSE Γ e (η e)` — is an expansion
with an unbounded chain `e ≫ η e ≫ η (η e) ≫ …`, and `VEnv.not_parRedSE_rigid_of_structEtaSite`
turns that into the failure of `VEnv.parRedSES_rigid`'s hypothesis at every site.  Its verdict was
that the rule must be **oriented as a contraction** before any normal-form machinery ports.
This file does that and prices it.

## What is proved

* §1–§2 `sizeOf` under `VExpr.mkApp`, then
  `VInductDecl'.sizeOf_lt_etaExpansionG` — **the expansion strictly grows its subject at positive
  fields**, and `etaExpansionG_ne` — so `η e ≠ e` there.  Four shape lemmas
  (`etaExpansionG_ne_bvar/_sort/_lam/_forallE`) record that an η-expansion is always a
  `const`-headed application spine.
* §3 `VEnv.ParRedSEC` — `VEnv.ParRedSE`'s nine constructors with the tenth flipped to
  `ParRedSEC Γ (D.etaExpansionG T C us ps j e) e`; plus `ParRedSEC.rfl`, `ParRedSECS` and
  `parRedSECS_rigid`, all verbatim ports.
* §4 `VEnv.parRedSEC_rigid_bvar` and `parRedSEC_rigid_sort` — **`parRedSES_rigid`'s hypothesis is
  satisfiable, unconditionally**, at every `Params` instance and in every context.  Three
  constructors could conclude about an atom and two of them are refuted syntactically: `extra`
  because `Pattern.Matches` only matches `.const c ls` and `.app f a`, and `structEtaC` because
  its redex is a `const`-headed spine.  **This is the sharpest single measurement of what the flip
  buys**: under the expansion orientation the same statement is not merely unproved, it is *false*
  at any site (`not_parRedSE_rigid_of_structEtaSite`), and §6's positive-field witness is a site
  whose subject is `.bvar 0`.
* §5 `VEnv.StructEtaStepC`, `.sizeOf_lt`, `no_infinite_structEtaStepC` — **the regress is gone**:
  a contraction step strictly decreases `sizeOf`, so there is no `Nat`-indexed chain of them.
  Compare `VEnv.parRedSES_etaIter`, which is the *positive* statement of exactly that shape for the
  expansion orientation.  `parRedSECS_etaIter_down` traverses `CRSEScope`'s η-tower in the other
  direction, into `e`, where it stops.
  The literal dual of `StructEtaSite.iterate` also fails, and provably at the witness:
  `iterate` needs only typing of the output, whereas a *new* contraction redex needs the output to
  *be* an η-expansion, which `etaExpansionG_ne_bvar` forbids for `.bvar 0`.
* §6 **the three new SE rules, fired for the first time.**  `MutField.unitEnv_structEtaSite` and
  `MutField.declEnv_structEtaSite` are the first `VEnv.StructEtaSite` witnesses anywhere in the
  tree — at the zero-field member `A` of `MutField.decl` (subject: the axiom `MutField.foo`) and at
  its **positive-field** member `B` (`bCtor.fields.length = 1`, subject `.bvar 0`).  Neither needs a
  `Params` instance and neither needs `VEnv.WF`; `VEnv.WF declEnv` is open for everybody and is
  *not* used.  On top of them: `ParRedSE.structEta`, `ParRedSEC.structEtaC`,
  `NormalEqSE.structEtaL` and `NormalEqSE.structEtaR` all fired at both shapes.
* §7 **neither refuted statement moves.**  `descendSEC_uniq_sortUniq_not_all` and
  `not_parRedStatementSEC_of_propMajor` are the two refutations ported to the contracted relation;
  the first goes through by inertness (`StructEtaSite.not_of_no_defeqs` is orientation-blind) and
  the second by porting the argument (its four moves — `appDF`, `proofIrrel`, `extra`, rigidity —
  are all still there).  If anything the second is *strengthened*, because §4 makes its `hrig`
  hypothesis satisfiable where the expansion orientation made it false.

## What re-orientation costs, and what breaks

**The `Params` firings are conditional, and not because of eta.**  `VEnv.StructEtaSite` takes no
`Params` instance, so §6's two site witnesses are unconditional.  But `NormalEqSE`, `ParRedSE` and
`ParRedSEC` all live under `variable [Params]`, and `Params.extra_pat` demands that *every*
`env.defeqs` rule be `Pat`-registered.  `StructEtaSite.isStruct` is `env.IsStructureG`, and
`IsStructureG.not_of_no_defeqs` holds precisely because `IsStructureG.decl` puts the block's
**ι-rules** into `env.defeqs`.  Registering an ι-rule is `PatWF`'s ι case, which
`Theory/Typing/ParamsBuild.lean` says needs `IsDefEqU.forallE_inv` — one of the tree's four holes.
So the §6 firings carry `env = unitEnv` / `env = declEnv` hypotheses, and **no `Params` instance
satisfying them exists today**.  That is an obstruction on `Params`, not on the eta rule, and it
is the same in either orientation.

**What the expansion form gave that the contraction does not.**  `ParRedSE.structEta` composed
with `NormalEqSE.structEtaL`/`structEtaR` in the obvious way: the conversion rule peels
`η e` on one side and the reduction rule *produced* `η e`, so `descend`'s "the conversion rule has
a reduct to descend to" discipline was satisfied by construction (that is the stated reason
`ConfluenceRebuildPrice` §4 chose the expansion).  Under the contraction the reduction runs
`η e ⟶ e` while `structEtaL`/`structEtaR` still recurse *on* `η e`, so at a `structEtaL` node the
reduction available at the subject `e` no longer reaches the term the conversion rule recurses on.
**That is the real cost, and it is a cost on `descend` alone** — `NormalEqSE` itself is unchanged
(§7's `ParRedStatementSEC` reuses it verbatim, and it is orientation-symmetric because it peels
rather than produces).  It is also a cost against a statement that is already refuted at 13
constructors and again at 14 in either orientation (§7), so nothing that was working stops working.

**The edit this implies to a file I do not own, stated and not made.**  Making `ParRedSEC` *the*
rule means replacing `Theory/Typing/ConfluenceRebuildPrice.lean:433-435`

```
  /-- **New.** -/
  | structEta :
    StructEtaSite env univs Γ S D j T C us ps e →
    ParRedSE Γ e (D.etaExpansionG T C us ps j e)
```

with

```
  /-- **New.**  Oriented as a contraction; see `Theory/Typing/EtaOrient.lean`. -/
  | structEta :
    StructEtaSite env univs Γ S D j T C us ps e →
    ParRedSE Γ (D.etaExpansionG T C us ps j e) e
```

and nothing else in that file: its `ParRedSE.rfl`, `parRedSES_rigid` and
`parRedSE_iff_of_no_defeqs` all go through unchanged (§3 and §7 are those three proofs, ported
verbatim against the flipped constructor).  `CRSEScope.lean`'s §2 and §4 would then have to be
restated or deleted, since `not_parRedSE_rigid_of_structEtaSite` and `parRedSES_etaIter` are about
the expansion.  **Both files belong to other rounds; nothing here touches them.**

## Consuming module

None, and deliberately: this is a pricing/refutation file about the orientation of a rule declared
in a file this round does not own, exactly as `CRSEScope.lean` is.  Its content becomes citable the
moment the edit above is made, and §7's two ports are then the replacements for
`ConfluenceRebuildPrice` §5.1 and §5.2.
-/

namespace Lean4Lean

open VExpr

/-! ## §1 `sizeOf` under `mkApp` -/

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

/-! ## §2 The expansion strictly grows its subject, at positive fields -/

namespace VInductDecl'

variable (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)

theorem sizeOf_lt_projCoreG {ps is : List VExpr} {i j : Nat} {earlier : List VExpr} {e : VExpr} :
    sizeOf e < sizeOf (D.projCoreG T C us ps is i j earlier e) := by
  show sizeOf e < sizeOf ((VExpr.const (Lean.mkRecName T.name) (D.projLvls C us i)).mkApp _)
  exact VExpr.sizeOf_lt_mkApp_of_mem _ (by simp) _

theorem sizeOf_lt_projTermG {ps is : List VExpr} {i j : Nat} {e : VExpr} :
    sizeOf e < sizeOf (D.projTermG T C us ps is i j e) :=
  D.sizeOf_lt_projCoreG T C us

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

/-! ## §3 The contracted rule -/

namespace VEnv

section
variable [Params]
open Params

/-- **`VEnv.ParRedSE` with the structure-eta step oriented as a contraction.**  The eight other
constructors are `ConfluenceRebuildPrice.lean`'s verbatim; only the tenth is flipped, from
`ParRedSE Γ e (D.etaExpansionG T C us ps j e)` to
`ParRedSEC Γ (D.etaExpansionG T C us ps j e) e`. -/
inductive ParRedSEC : List VExpr → VExpr → VExpr → Prop where
  | bvar : ParRedSEC Γ (.bvar i) (.bvar i)
  | sort : ParRedSEC Γ (.sort u) (.sort u)
  | const : ParRedSEC Γ (.const c ls) (.const c ls)
  | app : ParRedSEC Γ f f' → ParRedSEC Γ a a' → ParRedSEC Γ (.app f a) (.app f' a')
  | lam : ParRedSEC Γ A A' → ParRedSEC (A::Γ) body body' →
    ParRedSEC Γ (.lam A body) (.lam A' body')
  | forallE : ParRedSEC Γ A A' → ParRedSEC (A::Γ) B B' →
    ParRedSEC Γ (.forallE A B) (.forallE A' B')
  | beta : ParRedSEC (A::Γ) e₁ e₁' → ParRedSEC Γ e₂ e₂' →
    ParRedSEC Γ (.app (.lam A e₁) e₂) (e₁'.inst e₂')
  | extra {p : Pattern} {r : p.RHS × p.Check} {e : VExpr}
      {m1 : p.LPath → List VLevel} {m2 m2' : p.Path → VExpr} :
    Params.Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqSEU env univs Γ) m1 m2 →
    (∀ a, ParRedSEC Γ (m2 a) (m2' a)) → ParRedSEC Γ e (r.1.apply m1 m2')
  /-- **The contraction.** -/
  | structEtaC :
    StructEtaSite env univs Γ S D j T C us ps e →
    ParRedSEC Γ (D.etaExpansionG T C us ps j e) e

protected theorem ParRedSEC.rfl : ∀ {Γ : List VExpr} {e : VExpr}, ParRedSEC Γ e e
  | _, .bvar .. => .bvar
  | _, .sort .. => .sort
  | _, .const .. => .const
  | _, .app .. => .app ParRedSEC.rfl ParRedSEC.rfl
  | _, .lam .. => .lam ParRedSEC.rfl ParRedSEC.rfl
  | _, .forallE .. => .forallE ParRedSEC.rfl ParRedSEC.rfl

/-- The reflexive-transitive closure, as `VEnv.ParRedSES` is. -/
def ParRedSECS (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRedSEC Γ)

/-- `VEnv.parRedSES_rigid` over the contracted relation, verbatim. -/
theorem parRedSECS_rigid {Γ : List VExpr} {e o : VExpr}
    (hrig : ∀ o, ParRedSEC Γ e o → o = e) (H : ParRedSECS Γ e o) : o = e := by
  induction H with
  | rfl => rfl
  | tail _ h ih => cases ih; exact hrig _ h

/-! ## §4 Rigidity, and it is unconditional at the atoms -/

/-- **The contraction relation is rigid at a bound variable, with no side condition at all.**
Three constructors could conclude about a `.bvar`: `bvar` itself (which returns it unchanged),
`extra` (impossible — `Pattern.Matches` only matches `.const c ls` and `.app f a`), and
`structEtaC` (impossible — its redex is a `mkApp` of a `const`, never a `.bvar`).

The subject is stated as a variable plus an equation because `structEtaC`'s redex
`D.etaExpansionG …` is not a constructor application, so `cases` cannot unify against a fixed
`.bvar i` index. -/
theorem ParRedSEC.rigid_of_eq_bvar {Γ : List VExpr} {a o : VExpr} (H : ParRedSEC Γ a o) :
    ∀ i, a = .bvar i → o = a := by
  cases H with
  | bvar => exact fun _ _ => rfl
  | extra _ hm => exact fun _ h => absurd (h ▸ hm) nofun
  | structEtaC _ => exact fun _ h => absurd h (VInductDecl'.etaExpansionG_ne_bvar _ _ _ _)
  | _ => exact fun _ h => absurd h nofun

/-- **`VEnv.parRedSECS_rigid`'s hypothesis is satisfiable**, at every `Params` instance and every
context: a bound variable is `ParRedSEC`-rigid.  Contrast
`VEnv.not_parRedSE_rigid_of_structEtaSite`, which makes the *same* hypothesis false for the
expansion-oriented relation at every structure-eta site — and §6's witness is a site whose
subject is `.bvar 0`. -/
theorem parRedSEC_rigid_bvar {Γ : List VExpr} {i : Nat} :
    ∀ o, ParRedSEC Γ (.bvar i) o → o = .bvar i :=
  fun _ H => H.rigid_of_eq_bvar i rfl

/-- The same at a sort. -/
theorem ParRedSEC.rigid_of_eq_sort {Γ : List VExpr} {a o : VExpr} (H : ParRedSEC Γ a o) :
    ∀ u, a = .sort u → o = a := by
  cases H with
  | sort => exact fun _ _ => rfl
  | extra _ hm => exact fun _ h => absurd (h ▸ hm) nofun
  | structEtaC _ => exact fun _ h => absurd h (VInductDecl'.etaExpansionG_ne_sort _ _ _ _)
  | _ => exact fun _ h => absurd h nofun

theorem parRedSEC_rigid_sort {Γ : List VExpr} {u : VLevel} :
    ∀ o, ParRedSEC Γ (.sort u) o → o = .sort u :=
  fun _ H => H.rigid_of_eq_sort u rfl

/-! ## §5 No regress -/

/-- One structure-eta step in the contracted direction, at a positive-field structure. -/
def StructEtaStepC (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ S D j T C us ps, StructEtaSite env univs Γ S D j T C us ps b ∧
    0 < C.fields.length ∧ a = D.etaExpansionG T C us ps j b

theorem StructEtaStepC.toParRedSEC {Γ : List VExpr} {a b : VExpr}
    (h : StructEtaStepC Γ a b) : ParRedSEC Γ a b := by
  obtain ⟨_, _, _, _, _, _, _, hs, _, rfl⟩ := h; exact .structEtaC hs

/-- **The step strictly decreases `sizeOf`.**  This is the whole content of "the contraction does
not regress", and it is exactly what the expansion orientation cannot have:
`VEnv.StructEtaSite.iterate` shows the site re-fires on its own output, and §2 shows the output is
strictly bigger, so the expansion's chain is `sizeOf`-increasing and unbounded. -/
theorem StructEtaStepC.sizeOf_lt {Γ : List VExpr} {a b : VExpr}
    (h : StructEtaStepC Γ a b) : sizeOf b < sizeOf a := by
  obtain ⟨_, D, _, T, C, us, _, _, hf, rfl⟩ := h
  exact D.sizeOf_lt_etaExpansionG T C us hf

/-- **No infinite chain of contractions.**  Stated as "no `Nat`-indexed chain", which is the form
a termination argument consumes; `VEnv.parRedSES_etaIter` is the *positive* statement of exactly
this shape for the expansion orientation, so the two are directly comparable. -/
theorem no_infinite_structEtaStepC {Γ : List VExpr} (f : Nat → VExpr)
    (h : ∀ n, StructEtaStepC Γ (f n) (f (n + 1))) : False := by
  have key : ∀ n, sizeOf (f n) + n ≤ sizeOf (f 0) := by
    intro n; induction n with
    | zero => omega
    | succ n ih => have := (h n).sizeOf_lt; omega
  have := key (sizeOf (f 0) + 1); omega

/-- **The η-tower, traversed downward.**  `VEnv.parRedSES_etaIter` reaches the `n`-th expansion
from `e` in the expansion orientation; here the same tower is a `ParRedSECS` chain *into* `e`, and
by `no_infinite_structEtaStepC` it stops there. -/
theorem parRedSECS_etaIter_down {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
    {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e : VExpr}
    (h : StructEtaSite env univs Γ S D j T C us ps e)
    (ht : EtaStagesTyped Γ S D j T C us ps e) :
    ∀ n, ParRedSECS Γ (etaIterG D T C us ps j n e) e
  | 0 => .rfl
  | n + 1 => ReflTransGen.trans (.tail .rfl (.structEtaC (h.at_stage ht n)))
      (parRedSECS_etaIter_down h ht n)

end

end VEnv

/-! ## §6 The three rules, fired -/

namespace MutField

/-- **Site witness 1 — the zero-field member.**  `StructEtaPrice` §5's `structEtaSE_foo` premises,
bundled as `VEnv.StructEtaSite`.  Takes no `Params` instance and no `VEnv.WF`. -/
theorem unitEnv_structEtaSite :
    VEnv.StructEtaSite unitEnv 0 [] `MutField.A decl 0 aTy aCtor [] []
      ((VExpr.const `MutField.foo []).mkApp []) where
  isStruct := unitEnv_IsStructureG_0
  indices := rfl
  recFields := rfl
  nuvars := rfl
  levelWF := nofun
  np := rfl
  args := .nil
  typed := unitEnv_foo_hasType.toSE
  small := .inr (by simp [aCtor])

/-- **Site witness 2 — the positive-field member**, `bCtor.fields.length = 1`. -/
theorem declEnv_structEtaSite :
    VEnv.StructEtaSite declEnv 0 bCtx `MutField.B decl 1 bTy bCtor [] [] (.bvar 0) where
  isStruct := declEnv_IsStructureG
  indices := rfl
  recFields := rfl
  nuvars := rfl
  levelWF := nofun
  np := rfl
  args := .nil
  typed := VEnv.IsDefEq.toSE (.bvar (.zero ..))
  small := .inr bCtor_field_prop

/-- The positive-field member really is positive-field. -/
theorem bCtor_fields_pos : 0 < bCtor.fields.length := by decide

/-- …and the expansion there differs from its subject, so `not_parRedSE_rigid_of_structEtaSite`
has something to bite on. -/
theorem declEnv_etaExpansionG_ne :
    decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0) ≠ .bvar 0 :=
  decl.etaExpansionG_ne bTy bCtor [] bCtor_fields_pos

/-- The zero-field firing of `IsDefEqSE.structEta`, kept in the *raw* `etaExpansionG` form
(`StructEtaPrice`'s `structEtaSE_foo` has already rewritten it to `.const MutField.A.mk []`). -/
theorem unitEnv_isDefEqSE_eta :
    unitEnv.IsDefEqSE 0 [] ((VExpr.const `MutField.foo []).mkApp [])
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
      ((VExpr.const `MutField.A []).mkApp []) :=
  VEnv.structEtaGSE unitEnv unitEnv_IsStructureG_0 rfl rfl rfl nofun rfl .nil
    unitEnv_foo_hasType (.inr (by simp [aCtor]))

/-- The expansion is typed at the zero-field site — `NormalEqSE.refl`'s premise. -/
theorem unitEnv_eta_hasType :
    unitEnv.IsDefEqSE 0 [] (decl.etaExpansionG aTy aCtor [] [] 0
        ((VExpr.const `MutField.foo []).mkApp []))
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
      ((VExpr.const `MutField.A []).mkApp []) :=
  unitEnv_isDefEqSE_eta.symm.trans unitEnv_isDefEqSE_eta

/-- The same at the positive-field site; `structEtaSE_B` is already in raw form. -/
theorem declEnv_eta_hasType :
    declEnv.IsDefEqSE 0 bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0))
      (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0))
      ((VExpr.const `MutField.B []).mkApp []) :=
  structEtaSE_B.symm.trans structEtaSE_B

section
variable [VEnv.Params]
open VEnv VEnv.Params

/-- Site witness 1, moved onto a `Params` instance sitting over `unitEnv`. -/
theorem unitEnv_site_at_params (he : env = unitEnv) (hu : univs = 0) :
    StructEtaSite env univs [] `MutField.A decl 0 aTy aCtor [] []
      ((VExpr.const `MutField.foo []).mkApp []) := by
  rw [he, hu]; exact unitEnv_structEtaSite

/-- Site witness 2, likewise. -/
theorem declEnv_site_at_params (he : env = declEnv) (hu : univs = 0) :
    StructEtaSite env univs bCtx `MutField.B decl 1 bTy bCtor [] [] (.bvar 0) := by
  rw [he, hu]; exact declEnv_structEtaSite

/-! ### `ParRedSE.structEta` — the expansion orientation, both shapes -/

theorem unitEnv_parRedSE_structEta (he : env = unitEnv) (hu : univs = 0) :
    ParRedSE [] ((VExpr.const `MutField.foo []).mkApp [])
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp [])) :=
  .structEta (unitEnv_site_at_params he hu)

theorem declEnv_parRedSE_structEta (he : env = declEnv) (hu : univs = 0) :
    ParRedSE bCtx (.bvar 0) (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) :=
  .structEta (declEnv_site_at_params he hu)

/-! ### `ParRedSEC.structEtaC` — the contraction, both shapes -/

theorem unitEnv_parRedSEC_structEtaC (he : env = unitEnv) (hu : univs = 0) :
    ParRedSEC [] (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
      ((VExpr.const `MutField.foo []).mkApp []) :=
  .structEtaC (unitEnv_site_at_params he hu)

theorem declEnv_parRedSEC_structEtaC (he : env = declEnv) (hu : univs = 0) :
    ParRedSEC bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) (.bvar 0) :=
  .structEtaC (declEnv_site_at_params he hu)

/-! ### `NormalEqSE.structEtaL` / `structEtaR` — both shapes -/

theorem unitEnv_normalEqSE_structEtaL (he : env = unitEnv) (hu : univs = 0) :
    NormalEqSE [] ((VExpr.const `MutField.foo []).mkApp [])
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp [])) := by
  refine .structEtaL (unitEnv_site_at_params he hu)
    (.refl (A := (VExpr.const `MutField.A []).mkApp []) ?_)
  show IsDefEqSE env univs _ _ _ _
  rw [he, hu]; exact unitEnv_eta_hasType

theorem unitEnv_normalEqSE_structEtaR (he : env = unitEnv) (hu : univs = 0) :
    NormalEqSE [] (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
      ((VExpr.const `MutField.foo []).mkApp []) := by
  refine .structEtaR (unitEnv_site_at_params he hu)
    (.refl (A := (VExpr.const `MutField.A []).mkApp []) ?_)
  show IsDefEqSE env univs _ _ _ _
  rw [he, hu]; exact unitEnv_eta_hasType

theorem declEnv_normalEqSE_structEtaL (he : env = declEnv) (hu : univs = 0) :
    NormalEqSE bCtx (.bvar 0) (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) := by
  refine .structEtaL (declEnv_site_at_params he hu)
    (.refl (A := (VExpr.const `MutField.B []).mkApp []) ?_)
  show IsDefEqSE env univs _ _ _ _
  rw [he, hu]; exact declEnv_eta_hasType

theorem declEnv_normalEqSE_structEtaR (he : env = declEnv) (hu : univs = 0) :
    NormalEqSE bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) (.bvar 0) := by
  refine .structEtaR (declEnv_site_at_params he hu)
    (.refl (A := (VExpr.const `MutField.B []).mkApp []) ?_)
  show IsDefEqSE env univs _ _ _ _
  rw [he, hu]; exact declEnv_eta_hasType

/-! ### The before/after, at the positive-field site -/

/-- **What re-orientation buys, machine-checked at a positive-field structure.**  Left: with the
expansion orientation the subject `.bvar 0` is *not* `ParRedSE`-rigid, which is
`CRSEScope`'s `not_parRedSE_rigid_of_structEtaSite` instantiated for the first time.  Right: with
the contraction orientation it *is* rigid, and unconditionally — `parRedSEC_rigid_bvar` needs
neither the site nor any hypothesis on the environment. -/
theorem declEnv_rigidity_flips (he : env = declEnv) (hu : univs = 0) :
    ¬ (∀ o, ParRedSE bCtx (.bvar 0) o → o = .bvar 0) ∧
      (∀ o, ParRedSEC bCtx (.bvar 0) o → o = .bvar 0) :=
  ⟨not_parRedSE_rigid_of_structEtaSite (declEnv_site_at_params he hu) declEnv_etaExpansionG_ne,
    parRedSEC_rigid_bvar⟩

end

end MutField

/-! ## §7 The two refuted statements, re-checked under the contraction -/

namespace VEnv

section
variable [Params]
open Params

/-- **The contracted relation is the old one at a defeq-free environment**, exactly as
`VEnv.parRedSE_iff_of_no_defeqs` is: the flip changes nothing here, because the new rule dies on
`StructEtaSite.not_of_no_defeqs` in either direction. -/
theorem parRedSEC_iff_of_no_defeqs (hd : ∀ df, ¬ env.defeqs df)
    {Γ : List VExpr} {e₁ e₂ : VExpr} :
    ParRedSEC Γ e₁ e₂ ↔ ParRed Γ e₁ e₂ := by
  constructor
  · intro H
    induction H with
    | bvar => exact .bvar
    | sort => exact .sort
    | const => exact .const
    | app _ _ ih1 ih2 => exact .app ih1 ih2
    | lam _ _ ih1 ih2 => exact .lam ih1 ih2
    | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
    | beta _ _ ih1 ih2 => exact .beta ih1 ih2
    | extra r1 r2 r3 _ ih =>
      exact .extra r1 r2 (r3.map fun _ _ h => (isDefEqSEU_iff_of_no_defeqs hd).1 h) ih
    | structEtaC hs => exact absurd hs (StructEtaSite.not_of_no_defeqs hd)
  · intro H
    induction H with
    | bvar => exact .bvar
    | sort => exact .sort
    | const => exact .const
    | app _ _ ih1 ih2 => exact .app ih1 ih2
    | lam _ _ ih1 ih2 => exact .lam ih1 ih2
    | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
    | beta _ _ ih1 ih2 => exact .beta ih1 ih2
    | extra r1 r2 r3 _ ih =>
      exact .extra r1 r2 (r3.map fun _ _ h => (isDefEqSEU_iff_of_no_defeqs hd).2 h) ih

theorem parRedSECS_iff_of_no_defeqs (hd : ∀ df, ¬ env.defeqs df)
    {Γ : List VExpr} {e₁ e₂ : VExpr} :
    ParRedSECS Γ e₁ e₂ ↔ ParRedS Γ e₁ e₂ := by
  constructor
  · intro H
    induction H with
    | rfl => exact .rfl
    | tail _ h ih => exact ih.tail ((parRedSEC_iff_of_no_defeqs hd).1 h)
  · intro H
    induction H with
    | rfl => exact .rfl
    | tail _ h ih => exact ih.tail ((parRedSEC_iff_of_no_defeqs hd).2 h)

/-- `VEnv.ParRedStatementSE` over the contracted reduction.  **The conversion argument is
unchanged**: `NormalEqSE` appears verbatim, because `structEtaL`/`structEtaR` peel the expansion
on one side and are indifferent to which way the reduction runs. -/
def ParRedStatementSEC : Prop :=
  CRSchema (fun Γ => OnCtx Γ IsTypeSE) NormalEqSE ParRedSECS ParRedSEC

/-- **`VEnv.not_parRedStatementSE_of_propMajor` ports to the contracted relation line for line.**
So re-orientation does **not** move this refutation: the four moves it makes — `NormalEqSE.appDF`,
`NormalEqSE.proofIrrel`, `ParRedSEC.extra`, rigidity — are all still available, and none of them
mentions the eta rule.  If anything the refutation gets *stronger*, because its `hrig` hypothesis
is what `parRedSEC_rigid_bvar` shows is now satisfiable where
`not_parRedSE_rigid_of_structEtaSite` made it false. -/
theorem not_parRedStatementSEC_of_propMajor
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (hΓ : OnCtx Γ IsTypeSE)
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqSEU env univs Γ) m1 m2)
    (hf : HasTypeSE Γ f (.forallE A B))
    (hA : HasTypeSE Γ A (.sort .zero))
    (ha : HasTypeSE Γ a A) (hb : HasTypeSE Γ b A)
    (hrig : ∀ o, ParRedSEC Γ (.app f a) o → o = .app f a)
    (hne : ¬ NormalEqSE Γ (.app f a) (Pattern.RHS.apply m1 m2 r.1)) :
    ¬ ParRedStatementSEC := by
  intro H
  have h1 : NormalEqSE Γ (.app f a) (.app f b) :=
    .appDF hf hf ha hb (.refl hf) (.proofIrrel hA ha hb)
  have h2 : ParRedSEC Γ (.app f b) (Pattern.RHS.apply m1 m2 r.1) :=
    .extra r1 r2 r3 fun _ => ParRedSEC.rfl
  obtain ⟨o, ho, hno⟩ := H hΓ h1 h2
  cases parRedSECS_rigid hrig ho
  exact hne hno

end

end VEnv

/-- `Lean4Lean.DescendStatementSE` over the contracted reduction. -/
def DescendStatementSEC (I : VEnv.Params) : Prop :=
  DescendStatementP (@VEnv.NormalEqSE I) (@VEnv.ParRedSECS I) (@VEnv.HasTypeSE I) I.univs
    (@VEnv.IsTypeSE I)

/-- **The contracted descent statement is the same proposition at a defeq-free environment**, as
the expansion-oriented one is. -/
theorem descendStatementSEC_iff_of_no_defeqs (I : VEnv.Params)
    (hd : ∀ df, ¬ I.env.defeqs df) :
    DescendStatementSEC I ↔ DescendStatement I :=
  (descendStatementP_congr
      (fun _ _ _ => VEnv.normalEqSE_iff_of_no_defeqs hd)
      (fun _ _ _ => VEnv.parRedSECS_iff_of_no_defeqs hd)
      (fun _ _ _ => VEnv.hasTypeSE_iff_of_no_defeqs hd)
      (fun _ _ => VEnv.isTypeSE_iff_of_no_defeqs hd)).trans
    (descendStatementP_iff I)

/-- **`Lean4Lean.descendSE_uniq_sortUniq_not_all` stays refuted under the contraction.**  The
transport is by *inertness*, and `StructEtaSite.not_of_no_defeqs` says nothing about which way the
rule points, so re-orientation cannot move this one. -/
theorem descendSEC_uniq_sortUniq_not_all :
    ¬ (DescendStatementSEC refParams ∧ refEnv.SortUniq 0 ∧ refEnv.UniqTyping 0) := fun ⟨h, hsu, huq⟩ =>
  descend_uniq_sortUniq_not_all
    ⟨(descendStatementSEC_iff_of_no_defeqs refParams fun _ => refEnv_no_defeqs).1 h, hsu, huq⟩

end Lean4Lean

/-! ## §8 The axiom sweep, inline

`#print axioms` on **every** declaration this file adds, in the file, where the claim cannot go
stale.  Expected: everything `sorryAx`-free — in particular §6's firings, whose only hypotheses are
`env = unitEnv` / `env = declEnv`, and which must **not** pull in `VEnv.WF declEnv`. -/

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
#print axioms Lean4Lean.VEnv.ParRedSEC
#print axioms Lean4Lean.VEnv.ParRedSEC.rfl
#print axioms Lean4Lean.VEnv.ParRedSECS
#print axioms Lean4Lean.VEnv.parRedSECS_rigid
#print axioms Lean4Lean.VEnv.ParRedSEC.rigid_of_eq_bvar
#print axioms Lean4Lean.VEnv.parRedSEC_rigid_bvar
#print axioms Lean4Lean.VEnv.ParRedSEC.rigid_of_eq_sort
#print axioms Lean4Lean.VEnv.parRedSEC_rigid_sort
#print axioms Lean4Lean.VEnv.StructEtaStepC
#print axioms Lean4Lean.VEnv.StructEtaStepC.toParRedSEC
#print axioms Lean4Lean.VEnv.StructEtaStepC.sizeOf_lt
#print axioms Lean4Lean.VEnv.no_infinite_structEtaStepC
#print axioms Lean4Lean.VEnv.parRedSECS_etaIter_down
#print axioms Lean4Lean.MutField.unitEnv_structEtaSite
#print axioms Lean4Lean.MutField.declEnv_structEtaSite
#print axioms Lean4Lean.MutField.bCtor_fields_pos
#print axioms Lean4Lean.MutField.declEnv_etaExpansionG_ne
#print axioms Lean4Lean.MutField.unitEnv_isDefEqSE_eta
#print axioms Lean4Lean.MutField.unitEnv_eta_hasType
#print axioms Lean4Lean.MutField.declEnv_eta_hasType
#print axioms Lean4Lean.MutField.unitEnv_site_at_params
#print axioms Lean4Lean.MutField.declEnv_site_at_params
#print axioms Lean4Lean.MutField.unitEnv_parRedSE_structEta
#print axioms Lean4Lean.MutField.declEnv_parRedSE_structEta
#print axioms Lean4Lean.MutField.unitEnv_parRedSEC_structEtaC
#print axioms Lean4Lean.MutField.declEnv_parRedSEC_structEtaC
#print axioms Lean4Lean.MutField.unitEnv_normalEqSE_structEtaL
#print axioms Lean4Lean.MutField.unitEnv_normalEqSE_structEtaR
#print axioms Lean4Lean.MutField.declEnv_normalEqSE_structEtaL
#print axioms Lean4Lean.MutField.declEnv_normalEqSE_structEtaR
#print axioms Lean4Lean.MutField.declEnv_rigidity_flips
#print axioms Lean4Lean.VEnv.parRedSEC_iff_of_no_defeqs
#print axioms Lean4Lean.VEnv.parRedSECS_iff_of_no_defeqs
#print axioms Lean4Lean.VEnv.ParRedStatementSEC
#print axioms Lean4Lean.VEnv.not_parRedStatementSEC_of_propMajor
#print axioms Lean4Lean.DescendStatementSEC
#print axioms Lean4Lean.descendStatementSEC_iff_of_no_defeqs
#print axioms Lean4Lean.descendSEC_uniq_sortUniq_not_all
