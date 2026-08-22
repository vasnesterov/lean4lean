import Lean4Lean.Experimental.Bridge
import Lean4Lean.Experimental.UniqueTyping

/-!
# The two `VExpr`-side injectivity statements, relative to a `Params` instance

`Lean4Lean/Theory/Typing/Injectivity.lean` has three `sorry`s. Two of them —
`IsDefEqU.sort_inv` and `IsDefEqU.sort_forallE_inv` — have conclusions (`u ≈ v` and
`False`) that live entirely outside `VExpr`, so they need only the **forward** half of
the `VExpr ↔ SExpr` bridge (`VEnv.IsDefEq.toSExpr`). This file discharges both, *relative
to a `Params` instance for the environment in question*.

What is still missing to close them in `Theory/Typing/Injectivity.lean`:

1. **`Params` and `ParamsExtra` instances.** `Injectivity.lean`'s statements quantify over
   every `env` with `VEnv.WF env`; applying anything here needs `Params` with
   `Params.env = env`, plus `ParamsExtra`. Nothing in the repo instantiates either (nor the
   analogous `VEnv.Params` used by `Theory/Typing/ChurchRosser.lean`). `Params` alone is
   satisfiable trivially — `Pat := fun _ _ => False` discharges `pat_simple`/`pat_wf`/
   `pat_uniq` vacuously — so `ParamsExtra` is the real content: with a trivial `Pat` its
   `extra_pat` field is *false* for any environment carrying a definitional equality rule.
   That is exactly why it is a class field and no longer an `axiom`.

2. **`SExpr.LR.adequacy`'s `const` case** (`ShapeLogRelAdequacy.lean:154`) and the open
   declarations of `SExpr.lean` that the results below transitively use. See the module
   docstring of `Bridge.lean` and the ledger accompanying this change.

Nothing in *this* file or in `Bridge.lean` adds a `sorry` or an `axiom`.
-/

namespace Lean4Lean

open Lean4Lean Params SExpr

variable [Params] [ParamsExtra]

/--
**Sort injectivity**, relative to `Params`. Uses only `VEnv.IsDefEq.toSExpr` (sorry-free)
and `SExpr.sort_inv`.

`SLevel.mk` identifies exactly the `≈`-equivalent `VLevel`s, so the `SExpr`-side
conclusion `SLevel.mk u = SLevel.mk v` is literally `u ≈ v`.
-/
theorem VEnv.IsDefEqU.sort_inv_params {Γ : List VExpr} {u v : VLevel} {U : Nat}
    (H : Params.env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  let ⟨_, H⟩ := H.toSExpr; SLevel.mk_inj.1 (SExpr.sort_inv H)

/--
**Sort/Π disjointness**, relative to `Params`.

`SExpr.sort_forallE_inv` needs the ambient type to be a sort, while `IsDefEqU` supplies an
arbitrary one; the gap is closed on the `SExpr` side with `SExpr.HasTypeS.uniq`
(`Experimental/UniqueTyping.lean`), which retypes the derivation at `.sort (mk u).succ`.
-/
theorem VEnv.IsDefEqU.sort_forallE_inv_params {Γ : List VExpr} {u : VLevel} {A B : VExpr}
    {U : Nat} : ¬Params.env.IsDefEqU U Γ (.sort u) (.forallE A B) := by
  rintro ⟨V, H⟩
  have H' := VEnv.IsDefEq.toSExpr H
  have h1 := (SExpr.IsDefEq.toHasTypeS H').1
  have h2 : HasTypeS (Γ.map SExpr.mk) (.sort (SLevel.mk u))
      (.sort (SLevel.mk u).succ) true := .base .sort'
  have ⟨_, hw⟩ := h1.uniq h2
  exact SExpr.sort_forallE_inv (hw.defeqDF H')

end Lean4Lean
