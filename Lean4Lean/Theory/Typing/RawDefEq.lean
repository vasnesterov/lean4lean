import Lean4Lean.Theory.Typing.Lemmas

/-!
# The reference's conversion judgment, and why this tree's differs

`~/lean-type-theory/axioms.tex:30–41` defines Carneiro's definitional equality.  It is a
**three-place** judgment `Γ ⊢ e ≡ e'`, and of its eleven rules exactly **one** — application
— mentions a type, where `Γ ⊢ e ≡ e' : α` is stated (`:41`) to *abbreviate*
`Γ ⊢ e ≡ e' ∧ Γ ⊢ e : α ∧ Γ ⊢ e' : α`.  In particular:

* `symm` and `trans` (`:32–33`) carry **no type at all**;
* the λ and ∀ congruences (`:36–37`) carry no type;
* `refl`, `β`, `η` and proof irrelevance carry *typing* premises, but no shared type index;
* the conversion rule (`:19`) is a rule of the **typing** judgment, not of `≡`.

`Lean4Lean.VEnv.IsDefEq` (`Theory/Typing/Basic.lean`) instead makes the type an **index of
the judgment**, so every rule shares it: `trans` demands one `A` for both halves, `lamDF`
one level `u` and one codomain `B`, `forallEDF` one `u` and one `v`.  `IsDefEqU` — the
reference's actual judgment — is then *derived* as `∃ A, IsDefEq … A`, the opposite
direction from the reference.

**This is the single load-bearing divergence, and it is what put `IsDefEqU.forallE_inv` in
the confluence development.**  Composing two `IsDefEqU` facts is not a rule here, it is a
theorem (`IsDefEq.uniqU`), so `UniqueTyping.lean` must export `trans_l`, `trans_r`,
`transU_*`, `of_l`, `of_r`, `defeqU_*` — a family with no counterpart in the reference —
and `ChurchRosser.lean` uses it in 23 of its 85 declarations, including every backbone
lemma.  The same pressure shapes `NormalEq`: the reference's `≡ₚ` has *untyped* congruence
rules (`unique.tex:113–118`), while `NormalEq.appDF` demands one `.forallE A B` typing both
functions and `NormalEq.lamDF` one domain and one level, because that is what it takes to
convert a `NormalEq` back into a type-indexed `IsDefEq`.  Reconciling two independently
derived Π types is exactly `forallE_inv` + `uniq`.

So the Π-injectivity dependency traced in `Injectivity.lean`'s `sort_inv` docstring is real
*for this tree's confluence development* but is **an artifact of the port, not of the
mathematics**: the reference's proof never incurs it.

## What this file is

The reference's judgment, transcribed, plus the erasure `IsDefEq.raw`.  It is the base layer
a faithful port of `unique.tex` would run its κ-reduction and `≡ₚ` over, and it sits below
`Injectivity.lean` — it needs nothing but `Theory/Typing/Lemmas.lean`.

Two things the erasure demonstrates mechanically rather than by reading LaTeX:

* `trans` and `symm` are type-free **rules** here, so composing conversions carries no
  `uniq` obligation — the 23 backbone uses in `ChurchRosser.lean` simply do not arise;
* `IsDefEq.defeqDF` — the conversion rule — erases to *nothing*: its case in `IsDefEq.raw`
  is `exact ih2`.  In the three-place presentation the conversion rule has no content.

## What this file is *not*

It is not a proof that the port is repairable.  The converse, `IsDefEqRaw → IsDefEqU`, is
the reference's "Regularity continued" (`typesys.tex`), and its `trans` case needs `uniq` —
which is fine there and would be fine here, because the reference's confluence development
never needs the four-place form; it is recovered once, at the end, at the previous
stratification index.  Nobody has written that development against this relation.  Until
someone does, treat this file as a foundation stone, not as progress on `sort_inv`.
-/

namespace Lean4Lean
namespace VEnv

section
variable (env : VEnv) (U : Nat)

/-- **Carneiro's `Γ ⊢ e ≡ e'`** (`~/lean-type-theory/axioms.tex:30–41`), transcribed.

Rule-for-rule with the reference; the only adaptation is that the reference's separate
typing judgment `Γ ⊢ e : α` is spelled `env.HasType U Γ e A`, which in this tree is the
diagonal of `IsDefEq`.  The application rule expands the reference's `Γ ⊢ e ≡ e' : α`
abbreviation (`:41`) into its three conjuncts. -/
inductive IsDefEqRaw : List VExpr → VExpr → VExpr → Prop where
  | refl : env.HasType U Γ e A → IsDefEqRaw Γ e e
  | symm : IsDefEqRaw Γ e e' → IsDefEqRaw Γ e' e
  | trans : IsDefEqRaw Γ e₁ e₂ → IsDefEqRaw Γ e₂ e₃ → IsDefEqRaw Γ e₁ e₃
  | sortDF : l.WF U → l'.WF U → l ≈ l' → IsDefEqRaw Γ (.sort l) (.sort l')
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    IsDefEqRaw Γ (.const c ls) (.const c ls')
  /-- The reference's one type-annotated rule, with `Γ ⊢ e ≡ e' : α` expanded. -/
  | app :
    IsDefEqRaw Γ f f' → env.HasType U Γ f (.forallE A B) → env.HasType U Γ f' (.forallE A B) →
    IsDefEqRaw Γ a a' → env.HasType U Γ a A → env.HasType U Γ a' A →
    IsDefEqRaw Γ (.app f a) (.app f' a')
  | lam : IsDefEqRaw Γ A A' → IsDefEqRaw (A::Γ) body body' →
    IsDefEqRaw Γ (.lam A body) (.lam A' body')
  | forallE : IsDefEqRaw Γ A A' → IsDefEqRaw (A::Γ) B B' →
    IsDefEqRaw Γ (.forallE A B) (.forallE A' B')
  | beta : env.HasType U (A::Γ) e B → env.HasType U Γ e' A →
    IsDefEqRaw Γ (.app (.lam A e) e') (e.inst e')
  | eta : env.HasType U Γ e (.forallE A B) →
    IsDefEqRaw Γ (.lam A (.app e.lift (.bvar 0))) e
  | proofIrrel :
    env.HasType U Γ p (.sort .zero) → env.HasType U Γ h p → env.HasType U Γ h' p →
    IsDefEqRaw Γ h h'
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
    IsDefEqRaw Γ (df.lhs.instL ls) (df.rhs.instL ls)

end

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {e₁ e₂ A : VExpr}

/-- **Erasure.**  Every type-indexed conversion is a reference conversion.

Uses no injectivity and no unique typing — which is the point.  Note the two cases that
carry the message: `trans`/`symm` go straight through, because in the three-place
presentation they take no type; and `defeqDF`, the conversion rule, erases to `ih2`. -/
theorem IsDefEq.raw (H : env.IsDefEq U Γ e₁ e₂ A) : env.IsDefEqRaw U Γ e₁ e₂ := by
  induction H with
  | bvar h => exact .refl (.bvar h)
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 ih1 ih2 =>
    exact .app ih1 h1.hasType.1 h1.hasType.2 ih2 h2.hasType.1 h2.hasType.2
  | lamDF _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallE ih1 ih2
  | defeqDF _ _ _ ih2 => exact ih2
  | beta h1 h2 => exact .beta h1 h2
  | eta h1 => exact .eta h1
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3
  | extra h1 h2 h3 => exact .extra h1 h2 h3

theorem IsDefEqU.raw : env.IsDefEqU U Γ e₁ e₂ → env.IsDefEqRaw U Γ e₁ e₂
  | ⟨_, h⟩ => h.raw

end VEnv
end Lean4Lean
