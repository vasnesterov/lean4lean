import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Quot

namespace Lean4Lean

def VDefVal.WF (env : VEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

/-- Add a block of constants, without their defining equations. -/
def VEnv.addConsts (env : VEnv) (cis : List VDefVal) : Option VEnv :=
  cis.foldlM (fun env ci => env.addConst ci.name ci.toVConstant) env

/-- Add the defining equations of a block, after all of its constants. -/
def VEnv.addDefEqs (env : VEnv) (cis : List VDefVal) : VEnv :=
  cis.foldl (fun env ci => env.addDefEq ci.toDefEq) env

inductive VDecl.WF : VEnv → VDecl → VEnv → Prop where
  | axiom :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.axiom ci) env'
  | def :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)
  /-- A `partial`/`unsafe` mutual block. The values are checked in `env'`, which already
  carries the block's own constants, so this rule is *circular by design*: it is the only
  `VDecl.WF` rule that can make a well-formed environment inconsistent. See `VDecl` and
  `Theory/MutualDefUnsound.lean`; `VDecl.isPure` excludes it. -/
  | unsafeDef :
    (∀ ci ∈ cis, ci.toVConstant.WF env) →
    env.addConsts cis = some env' →
    (∀ ci ∈ cis, ci.WF env') →
    VDecl.WF env (.unsafeDef cis) (env'.addDefEqs cis)
  | opaque :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.opaque ci) env'
  | example :
    ci.WF env →
    VDecl.WF env (.example ci) env
  | quot :
    env.QuotReady →
    env.addQuot = some env' →
    VDecl.WF env .quot env'
  | induct :
    decl.WF env →
    env.addInduct' decl = some env' →
    VDecl.WF env (.induct decl) env'

/-- A declaration step other than `.axiom` and `.unsafeDef`: the *pure* fragment.
All other steps are conservative, in that `VDecl.WF` requires them to typecheck
*in the environment before the step*, so (by the intended metatheory) they cannot
introduce inconsistency over the standard prelude. `Theory/Consistency.lean`
states consistency for exactly this fragment.

Both exclusions are load-bearing. `.axiom` is obvious. `.unsafeDef` models a
`partial`/`unsafe` mutual block, whose values are checked in the environment that
already carries the block's own constants; `Theory/MutualDefUnsound.lean`
exhibits a well-formed `.unsafeDef` step producing an inhabitant of `falseProp`,
so any fragment containing it is *provably* inconsistent. -/
def VDecl.isPure : VDecl → Prop
  | .axiom _ => False
  | .unsafeDef _ => False
  | _ => True

instance : ∀ d : VDecl, Decidable d.isPure
  | .axiom _ | .unsafeDef _ => .isFalse id
  | .def _ | .opaque _ | .example _ | .quot | .induct _ => .isTrue trivial

/-- The weaker half of `VDecl.isPure`: not a `partial`/`unsafe` block. `.axiom` steps
are still permitted, so this is what the *refinement layer* can supply on its own
(`TrEnv'.wf_noUnsafe`); ruling out further axioms is separate bookkeeping about the
kernel-level declaration list. -/
def VDecl.noUnsafe : VDecl → Prop
  | .unsafeDef _ => False
  | _ => True

theorem VDecl.isPure.noUnsafe : ∀ {d : VDecl}, d.isPure → d.noUnsafe
  | .def _, _ | .opaque _, _ | .example _, _ | .quot, _ | .induct _, _ => trivial

inductive VEnv.WF' : List VDecl → VEnv → Prop where
  | empty : VEnv.WF' [] .empty
  | decl {env} : VDecl.WF env d env' → env.WF' ds → env'.WF' (d::ds)

def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env
