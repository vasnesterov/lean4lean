import Lean.Expr
import Lean.LocalContext
import Lean.Util.InstantiateLevelParams

namespace Lean
namespace Expr

/-- Beta-reduces an application `(fun x₁ ... xₙ => b) a₁ ... aₙ aₙ₊₁ ... aₘ` in the two cases where
no substitution is needed: to `b aₙ₊₁ ... aₘ` when `b` has no loose bound variables, and to
`aᵢ aₙ₊₁ ... aₘ` when `b` is the bound variable `xᵢ`. In any other case `e` is returned unchanged —
this is what makes it cheap. -/
def cheapBetaReduce (e : Expr) : Expr := Id.run do
  if !e.isApp then return e
  let fn := e.getAppFn
  if !fn.isLambda then return e
  let args := e.getAppArgs
  let rec cont i fn :=
    -- Divergence from the C++ kernel: where it drops the consumed arguments outright, we
    -- apply the (then trivial) substitution. `Expr.hasLooseBVars` reads the cached 20-bit
    -- `looseBVarRange` field, which is wrong for a term whose `bvar` indices overflow it
    -- (lean4#8554); a cached bit that wrongly reported "no loose bvars" would otherwise
    -- drop a substitution that is actually needed. `instantiateRevRange` is the identity
    -- exactly when the bit is honest, so the value computed is unchanged, and the C wrapper
    -- returns immediately when the cached range is 0, so the fast path survives.
    -- See `divergences.md`.
    if !fn.hasLooseBVars then
      mkAppRange (fn.instantiateRevRange 0 i args) i args.size args
    else if let .bvar n := fn then
      assert! n < i
      mkAppRange args[i - n - 1]! i args.size args
    else
      e
  let rec loop i fn :=
    if i < args.size then
      match fn with
      | .lam _ _ body .. => loop (i + 1) body
      | _ => cont i fn
    else cont i fn
  return loop 0 fn

end Expr
