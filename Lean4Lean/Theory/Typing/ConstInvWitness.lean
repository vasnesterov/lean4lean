import Lean4Lean.Theory.Typing.Injectivity

/-!
# Why const-application injectivity carries two side conditions

`IsDefEqU.const_app_inv` (`Theory/Typing/Injectivity.lean`) says that a definitional
equality between two applications of the *same* constant forces the arguments to agree.
Stated without side conditions it is **false**, and this file exhibits the two witnesses,
machine-checked.

Both end at the same place: they force
`env.IsDefEqU 0 [] (.sort .zero) (.forallE (.sort .zero) (.sort .zero))` — that is, `Prop`
definitionally equal to `Prop → Prop` — which `IsDefEqU.sort_forallE_inv` denies.  So each
witness is a refutation *relative to* `sort_forallE_inv`, which is the weakest thing they
could be relative to: it is one of the three statements this same file family is about, and
nobody proposes dropping it.

## W1 — a reducible head

A constant whose value is a constant function identifies all its arguments.  This is what
the `RuleFreeHead` side condition excludes, and it is already recorded in
`docs/design-inductive.md`'s ledger entry I13.

## W2 — a `Prop`-valued application

**This one is not repaired by `RuleFreeHead`,** which is why it is worth having in the
tree rather than in a document.  `mkP` below is an *axiom*: no `VDefEq` mentions it, so
every notion of "rule-free head" holds of it — the environment's `defeqs` is left
completely unconstrained by `w2`, so the witness stands even in an environment with no
rules at all.  Yet `IsDefEq.proofIrrel` identifies `mkP A` with `mkP B` outright, **with no
reduction whatever**, because both inhabit the same proposition.

The second side condition is therefore not `RuleFreeHead`-flavoured at all: it asks that
the *application* be a type rather than a proof.  All five consumers of the injectivity
statement use it at the type of a term, so they satisfy it for free — see
`docs/research-const-inv.md` §3 and §6.
-/

namespace Lean4Lean

open VExpr

/-! ## The three terms both witnesses need -/

/-- `Prop`. -/
abbrev vprop : VExpr := .sort .zero
/-- `Type 0`. -/
abbrev vtype0 : VExpr := .sort (.succ .zero)
/-- `Prop → Prop`, which is also a `Type 0`. -/
abbrev vpropArrow : VExpr := .forallE vprop vprop

theorem hasType_vprop {env : VEnv} {Γ} : env.HasType 0 Γ vprop vtype0 :=
  .sortDF trivial trivial rfl

theorem imax_one_one : VLevel.imax (.succ .zero) (.succ .zero) ≈ VLevel.succ .zero := by
  funext ls; simp [VLevel.eval, Lean.Nat.imax]

theorem hasType_vpropArrow {env : VEnv} {Γ} : env.HasType 0 Γ vpropArrow vtype0 :=
  .defeqDF (.sortDF (l := .imax (.succ .zero) (.succ .zero)) ⟨trivial, trivial⟩ trivial
      imax_one_one)
    (.forallEDF hasType_vprop hasType_vprop)

/-! ## W1 — a reducible head identifies all arguments -/

/-- `f : Type 0 → Type 0 := fun _ => Prop`, as the `VDefEq` a `def` step installs
(`VDefVal.toDefEq`, `Theory/VDecl.lean`). -/
def constFnRule : VDefEq :=
  ⟨0, .const `f [], .lam vtype0 vprop, .forallE vtype0 vtype0⟩

variable {env : VEnv}

/-- Every argument of `f` gives back `Prop`: `.extra` unfolds the constant, `.beta` applies
the constant function. -/
theorem w1_step (hf : env.defeqs constFnRule) {A : VExpr} (hA : env.HasType 0 [] A vtype0) :
    env.IsDefEq 0 [] (.app (.const `f []) A) vprop vtype0 :=
  have hextra : env.IsDefEq 0 [] (.const `f []) (.lam vtype0 vprop) (.forallE vtype0 vtype0) :=
    .extra (ls := []) hf nofun rfl
  (VEnv.IsDefEq.appDF hextra hA).trans (.beta hasType_vprop hA)

/-- **W1.**  `f Prop ≡ f (Prop → Prop)`, at two arguments that had better not be
definitionally equal. -/
theorem w1 (hf : env.defeqs constFnRule) :
    env.IsDefEqU 0 [] (.app (.const `f []) vprop) (.app (.const `f []) vpropArrow) :=
  ⟨_, (w1_step hf hasType_vprop).trans (w1_step hf hasType_vpropArrow).symm⟩

/-! ## W2 — a `Prop`-valued application identifies all arguments

`env.defeqs` is not mentioned below.  The witness therefore holds in an environment with no
definitional-equality rules whatsoever, so no strengthening of `RuleFreeHead` can exclude
it. -/

/-- `P : Prop`, an axiom. -/
def propAx : VConstant := ⟨0, vprop⟩
/-- `mkP : Type 0 → P`, an axiom. -/
def mkPAx : VConstant := ⟨0, .forallE vtype0 (.const `P [])⟩

/-- **W2.**  Any two `Type 0`s give definitionally equal proofs, by `proofIrrel` alone —
no reduction, and no rule in the environment. -/
theorem w2 (hP : env.constants `P = some propAx) (hmk : env.constants `mkP = some mkPAx)
    {A B : VExpr} (hA : env.HasType 0 [] A vtype0) (hB : env.HasType 0 [] B vtype0) :
    env.IsDefEqU 0 [] (.app (.const `mkP []) A) (.app (.const `mkP []) B) :=
  have hPty : env.HasType 0 [] (.const `P []) vprop :=
    .constDF (ls := []) (ls' := []) hP nofun nofun rfl .nil
  have happ {C : VExpr} (hC : env.HasType 0 [] C vtype0) :
      env.HasType 0 [] (.app (.const `mkP []) C) (.const `P []) :=
    .appDF (.constDF (ls := []) (ls' := []) hmk nofun nofun rfl .nil) hC
  ⟨_, .proofIrrel hPty (happ hA) (happ hB)⟩

/-! ## What each witness forces

Injectivity is applied here as a hypothesis at exactly the instance each witness produces,
so what is machine-checked is that the instance *is* derivable and that it *does* force the
bad conclusion. -/

/-- **W1 forces `Prop ≡ Prop → Prop`.** -/
theorem w1_forces (hf : env.defeqs constFnRule)
    (inj : ∀ {A B : VExpr},
      env.IsDefEqU 0 [] (.app (.const `f []) A) (.app (.const `f []) B) →
      env.IsDefEqU 0 [] A B) :
    env.IsDefEqU 0 [] vprop vpropArrow := inj (w1 hf)

/-- **W2 forces `Prop ≡ Prop → Prop`**, with no assumption on `env.defeqs` at all. -/
theorem w2_forces (hP : env.constants `P = some propAx) (hmk : env.constants `mkP = some mkPAx)
    (inj : ∀ {A B : VExpr},
      env.IsDefEqU 0 [] (.app (.const `mkP []) A) (.app (.const `mkP []) B) →
      env.IsDefEqU 0 [] A B) :
    env.IsDefEqU 0 [] vprop vpropArrow :=
  inj (w2 hP hmk hasType_vprop hasType_vpropArrow)

/-- …and that conclusion is exactly what `sort_forallE_inv` denies.  (Sorry-tainted, since
`sort_forallE_inv` is itself one of `Injectivity.lean`'s open statements; the *derivations*
above are not.)

The taint is unavoidable rather than incidental: refuting a definitional equality is
precisely what `Injectivity.lean` exists to do, so any witness of this kind must bottom out
in one of its statements.  What is *not* tainted is everything above — that the two
applications really are definitionally equal. -/
theorem absurd_of_prop_eq_propArrow (henv : env.WF)
    (h : env.IsDefEqU 0 [] vprop vpropArrow) : False :=
  VEnv.IsDefEqU.sort_forallE_inv (Γ := []) henv trivial h

/-! ## Regression tests

The two theorems below are the point of this file being code rather than a document.  Each
takes the injectivity statement **with one side condition dropped** and derives `False`.  If
someone later "simplifies" `IsDefEqU.const_app_inv` by removing either condition, the
corresponding theorem here becomes a proof of `False` from a provable hypothesis — and this
file stops compiling for a reason that points straight at the change. -/

/-- **Dropping `RuleFreeHead` is inconsistent.**  `inj` is `const_app_inv` restricted to one
head and one environment, with the rule-free condition removed. -/
theorem drop_ruleFreeHead_inconsistent (henv : env.WF) (hf : env.defeqs constFnRule)
    (inj : ∀ {A B : VExpr},
      env.IsDefEqU 0 [] (.app (.const `f []) A) (.app (.const `f []) B) →
      env.IsDefEqU 0 [] A B) :
    False := absurd_of_prop_eq_propArrow henv (w1_forces hf inj)

/-- **Dropping the application-is-a-type condition is inconsistent**, and `RuleFreeHead`
does not rescue it: `env.defeqs` is unconstrained here, so `mkP` heads no rule under any
reading of that condition. -/
theorem drop_isType_inconsistent (henv : env.WF)
    (hP : env.constants `P = some propAx) (hmk : env.constants `mkP = some mkPAx)
    (inj : ∀ {A B : VExpr},
      env.IsDefEqU 0 [] (.app (.const `mkP []) A) (.app (.const `mkP []) B) →
      env.IsDefEqU 0 [] A B) :
    False := absurd_of_prop_eq_propArrow henv (w2_forces hP hmk inj)

end Lean4Lean
