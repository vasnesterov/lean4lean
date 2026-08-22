import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive.Lemmas

namespace Lean4Lean
namespace VEnv

theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct' env decl = some env') : Ordered env' :=
  VInductDecl'.addInduct'_ordered_final henv hdecl henv'
