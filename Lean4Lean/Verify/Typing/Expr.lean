import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Inductive.Structure
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.VLCtx
import Lean4Lean.Verify.Axioms

namespace Lean4Lean
open Lean

def Closed : Expr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .fvar _, _ | .sort .., _ | .const .., _ | .lit .., _ => True
  | .app f a, k => Closed f k ∧ Closed a k
  | .lam _ d b _, k
  | .forallE _ d b _, k => Closed d k ∧ Closed b (k+1)
  | .letE _ d v b _, k => Closed d k ∧ Closed v k ∧ Closed b (k+1)
  | .proj _ _ e, k | .mdata _ e, k => Closed e k
  | .mvar .., _ => False

nonrec abbrev _root_.Lean.Expr.Closed := @Closed

/-- This is very inefficient, only use for spec purposes -/
def _root_.Lean.Expr.fvarsList : Expr → List FVarId
  | .bvar _ | .sort .. | .const .. | .lit .. | .mvar .. => []
  | .fvar fv => [fv]
  | .app f a => f.fvarsList ++ a.fvarsList
  | .lam _ d b _
  | .forallE _ d b _ => d.fvarsList ++ b.fvarsList
  | .letE _ d v b _ => d.fvarsList ++ v.fvarsList ++ b.fvarsList
  | .proj _ _ e | .mdata _ e => e.fvarsList

variable (fvars : FVarId → Prop) in
def FVarsIn : Expr → Prop
  | .bvar _ => True
  | .fvar fv => fvars fv
  | .sort u => u.hasMVar' = false
  | .const _ us => ∀ u ∈ us, u.hasMVar' = false
  | .lit .. => True
  | .app f a => FVarsIn f ∧ FVarsIn a
  | .lam _ d b _
  | .forallE _ d b _ => FVarsIn d ∧ FVarsIn b
  | .letE _ d v b _ => FVarsIn d ∧ FVarsIn v ∧ FVarsIn b
  | .proj _ _ e | .mdata _ e => FVarsIn e
  | .mvar .. => False

nonrec abbrev _root_.Lean.Expr.FVarsIn := @FVarsIn

def VLocalDecl.WF (env : VEnv) (U : Nat) (Γ : List VExpr) : VLocalDecl → Prop
  | .vlam type => env.IsType U Γ type
  | .vlet type value => env.HasType U Γ value type

def VLCtx.FVWF : VLCtx → Prop
  | [] => True
  | (ofv, _) :: (Δ : VLCtx) =>
    VLCtx.FVWF Δ ∧ (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars)

variable (env : VEnv) (U : Nat) in
def VLCtx.WF : VLCtx → Prop
  | [] => True
  | (ofv, d) :: (Δ : VLCtx) =>
    VLCtx.WF Δ ∧ (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars) ∧
    VLocalDecl.WF env U Δ.toCtx d

theorem VLCtx.WF.fvwf : ∀ {Δ}, VLCtx.WF env U Δ → Δ.FVWF
  | [], h => h
  | _ :: _, ⟨h1, h2, _⟩ => ⟨h1.fvwf, h2⟩

variable (env : VEnv) (U : Nat) in
/-- The abstract counterpart of `Lean.Expr.proj`.

`VExpr` has no projection constructor, so a projection has to be translated into the term
it *is*: an application of the structure's recursor,
`VInductDecl'.projTerm` (`Theory/Inductive/Structure.lean`).  The structure's level and
parameter arguments are not syntactically present in `.proj s i e` — they have to be read
off the *type of `e`* — which is why this takes `env` and `U`; `TrExprS` has both in scope
at the only call site.

Given `Γ, s, i, e`, every remaining input is pinned by the premises, so `e''` is a
function of them *provided* `s` determines the block.  That last step is the one thing
`VEnv.IsStructure` deliberately does not supply (ledger G4); see `TrProj.uniq`. -/
inductive TrProj : List VExpr → Name → Nat → VExpr → VExpr → Prop
  | mk {S : Name} {D T C us ps ιs Γ e i} :
    env.IsStructure S D T C →
    -- the level and parameter arguments, read off the type of `e`
    env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ ιs)) →
    us.length = D.uvars → ps.length = D.np → ιs.length = T.indices.length →
    i < C.fields.length →
    -- **Recorded, not derived** — the three clauses below.
    --
    -- They are all consequences of the `HasType` above, but extracting them means peeling
    -- the application spine with `HasType.app_inv` (`Typing/Strong.lean:769`), which returns
    -- an *existential* domain, and pinning that domain to `S`'s declared parameter/index
    -- telescope means relating it to `T.type` — which by F1 is only *definitionally*
    -- `mkPi (params ++ indices) (sort lvl)`.  That is `IsDefEqU.forallE_inv`
    -- (`Typing/Injectivity.lean`, `sorry`), the same family that blocks `TrProj.uniq`,
    -- `.defeqDFC` and `.weak'_inv`.
    --
    -- `Theory/Inductive/Decl.lean` reached this identical wall independently and took the
    -- identical door: see `VIndField.WF.pos`'s index clause and `VIndCtor.WF.args_ty`,
    -- whose justification transfers verbatim.
    --
    -- What makes this a relocation of a proof obligation rather than an assumption is that
    -- the checker *demonstrably* establishes each clause, at these sites:
    --   * `inferProj` whnfs `e`'s type and destructures it as `I args`
    --     (`TypeChecker.lean:235-236`), requiring `args.size = numParams + numIndices`
    --     (`TypeChecker.lean:243`);
    --   * the `.app` branch of `inferType'` checks every argument against its domain with
    --     `isDefEq dType aType` (`TypeChecker.lean:298-312`), via `inferApp`
    --     (`TypeChecker.lean:190`);
    --   * `inferConstant` checks `ps.length = ls.length` and `checkLevel` on each level
    --     (`TypeChecker.lean:121-133`).
    --
    -- **The obligation moves to `inferProj.WF`** (`Verify/TypeChecker/InferType.lean`),
    -- where it is discharged from those checks — not dropped.
    --
    -- This also subsumes the level obligation of `TrProj.wf`: `hus` is why `wf` can reach
    -- `recApp_hasType''`'s `hls`, and `wf`'s own `hΓ` is needed for other reasons.
    (hus : ∀ l ∈ us, l.WF U) →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs →
    -- **F17, transcribed.**  Either the block eliminates into an arbitrary universe, or
    -- every field the encoding's motives actually project must be a proof.
    --
    -- `inferProj` (`TypeChecker.lean:249-259`) walks the field telescope and checks
    -- `isProp dom` — when the structure's sort is not `isNeverZero` — for the projected
    -- field and for each earlier field whose binder is *used* by the rest of the
    -- telescope, dropping unused ones with `else r := b` and no check at all.
    -- `VIndCtor.FieldUsed` is the abstract image of that `b.hasLooseBVars`.
    --
    -- The guard matters: `structure Bar : Prop where (n : Nat) (h : True)` is not
    -- large-eliminating, yet both kernels accept a hand-built `.proj Bar 1`, because
    -- field 0 is unused by `h`'s type.  A blanket `∀ k ≤ i` would reject it — a
    -- divergence from the C++ kernel, and a second narrowing of the `bugs-found` item 10
    -- kind.  Measured, not assumed.
    --
    -- Discharged in `inferProj.WF` from those same checks, like the clauses above.
    --
    -- Note the reachability caveat: in practice `isLE = false` plus a projection already
    -- forces every *involved* field to be a `Prop`, and a one-type/one-constructor block
    -- with all-`Prop` fields satisfies `LECond`, so Lean would have set `isLE = true`.
    -- This branch is reachable only because `VInductDecl'.isLE` is a *claim* the record
    -- permits to be conservative rather than a derived fact.  Recorded, not relied on.
    (D.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    TrProj Γ S i e (D.projTerm T C us ps ιs i e)

def VEnv.ContainsLits (env : VEnv) : Literal → Prop
  | .natVal _ => env.contains ``Nat
  | .strVal _ => env.contains ``Char.ofNat ∧ env.contains ``String.ofList

variable (env : VEnv) (Us : List Name) in
inductive TrExprS : VLCtx → Expr → VExpr → Prop
  | bvar : Δ.find? (.inl i) = some (e, A) → TrExprS Δ (.bvar i) e
  | fvar : Δ.find? (.inr fv) = some (e, A) → TrExprS Δ (.fvar fv) e
  | sort : VLevel.ofLevel Us u = some u' → TrExprS Δ (.sort u) (.sort u')
  | const :
    env.constants c = some ci →
    us.mapM (VLevel.ofLevel Us) = some us' →
    us.length = ci.uvars →
    TrExprS Δ (.const c us) (.const c us')
  | app :
    env.HasType Us.length Δ.toCtx f' (.forallE A B) →
    env.HasType Us.length Δ.toCtx a' A →
    TrExprS Δ f f' → TrExprS Δ a a' → TrExprS Δ (.app f a) (.app f' a')
  | lam :
    env.IsType Us.length Δ.toCtx ty' →
    TrExprS Δ ty ty' → TrExprS ((none, .vlam ty') :: Δ) body body' →
    TrExprS Δ (.lam name ty body bi) (.lam ty' body')
  | forallE :
    env.IsType Us.length Δ.toCtx ty' →
    env.IsType Us.length (ty' :: Δ.toCtx) body' →
    TrExprS Δ ty ty' → TrExprS ((none, .vlam ty') :: Δ) body body' →
    TrExprS Δ (.forallE name ty body bi) (.forallE ty' body')
  | letE :
    env.HasType Us.length Δ.toCtx val' ty' →
    TrExprS Δ ty ty' → TrExprS Δ val val' →
    TrExprS ((none, .vlet ty' val') :: Δ) body body' →
    TrExprS Δ (.letE name ty val body nd) body'
  | lit : env.ContainsLits l → TrExprS Δ l.toConstructor e → TrExprS Δ (.lit l) e
  | mdata : TrExprS Δ e e' → TrExprS Δ (.mdata d e) e'
  | proj :
    TrExprS Δ e e' → TrProj env Us.length Δ.toCtx s i e' e'' →
    TrExprS Δ (.proj s i e) e''

def TrExpr (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) (e' : VExpr) : Prop :=
  ∃ e₂, TrExprS env Us Δ e e₂ ∧ env.IsDefEqU Us.length Δ.toCtx e₂ e'

def VExpr.bool : VExpr := .const ``Bool []
def VExpr.boolTrue : VExpr := .const ``Bool.true []
def VExpr.boolFalse : VExpr := .const ``Bool.false []
def VExpr.boolLit : Bool → VExpr
  | .false => .boolFalse
  | .true => .boolTrue

def VExpr.nat : VExpr := .const ``Nat []
def VExpr.natZero : VExpr := .const ``Nat.zero []
def VExpr.natSucc : VExpr := .const ``Nat.succ []
def VExpr.natLit : Nat → VExpr
  | 0 => .natZero
  | n+1 => .app .natSucc (.natLit n)

def VExpr.char : VExpr := .const ``Char []
def VExpr.string : VExpr := .const ``String []
def VExpr.stringOfList : VExpr := .const ``String.ofList []
def VExpr.listChar : VExpr := .app (.const ``List [.zero]) .char
def VExpr.listCharNil : VExpr := .app (.const ``List.nil [.zero]) .char
def VExpr.listCharCons : VExpr := .app (.const ``List.cons [.zero]) .char
def VExpr.charOfNat : VExpr := .const ``Char.ofNat []
def VExpr.listCharLit : List Char → VExpr
  | [] => .listCharNil
  | a :: as => .app (.app .listCharCons (.app .charOfNat (.natLit a.toNat))) (.listCharLit as)

def VExpr.trLiteral : Literal → VExpr
  | .natVal n => .natLit n
  | .strVal s => .app .stringOfList (.listCharLit s.toList)

def VEnv.ReflectsNatNat (env : VEnv) (fc : Name) (f : Nat → Nat) :=
  env.contains fc →
  ∀ a, env.IsDefEqU 0 [] (.app (.const fc []) (.natLit a)) (.natLit (f a))

def VEnv.ReflectsNatNatNat (env : VEnv) (fc : Name) (f : Nat → Nat → Nat) :=
  env.contains fc →
  ∀ a b, env.IsDefEqU 0 [] (.app (.app (.const fc []) (.natLit a)) (.natLit b)) (.natLit (f a b))

def VEnv.ReflectsNatNatBool (env : VEnv) (fc : Name) (f : Nat → Nat → Bool) :=
  env.contains fc →
  ∀ a b, env.IsDefEqU 0 [] (.app (.app (.const fc []) (.natLit a)) (.natLit b)) (.boolLit (f a b))

/-- The term `f` computes the boolean operation `g` on boolean literals. This is what the
`Nat.land`/`Nat.lor`/`Nat.xor` branches of the primitive recognizer check about the boolean
operation they pass to `Nat.bitwise`. -/
def VEnv.ReflectsBoolBoolBool (env : VEnv) (f : VExpr) (g : Bool → Bool → Bool) :=
  ∀ a b, env.IsDefEqU 0 [] (.app (.app f (.boolLit a)) (.boolLit b)) (.boolLit (g a b))

/-- `Nat.bitwise` is the one primitive whose semantics are second order: it is applied to a
boolean operation supplied by the *later* declaration of `Nat.land`/`Nat.lor`/`Nat.xor`, so
the operation is in general a term that does not exist yet when `Nat.bitwise` is recognized.
The statement is therefore relativized to an arbitrary extension `env'` of `env`; without
that relativization the field would not be monotone (`ReflectsBoolBoolBool` occurs
negatively, and a later declaration may introduce a new `f`). -/
def VEnv.ReflectsNatBitwise (env : VEnv) :=
  env.contains ``Nat.bitwise →
  ∀ (env' : VEnv), env ≤ env' → ∀ (f : VExpr) (g : Bool → Bool → Bool),
    env'.ReflectsBoolBoolBool f g → ∀ a b, env'.IsDefEqU 0 []
      (.app (.app (.app (.const ``Nat.bitwise []) f) (.natLit a)) (.natLit b))
      (.natLit (Nat.bitwise g a b))

structure VEnv.HasPrimitives (env : VEnv) : Prop where
  bool : env.contains ``Bool → env.contains ``Bool.false ∧ env.contains ``Bool.true
  boolFalse : env.constants ``Bool.false = some ci → ci = { uvars := 0, type := .bool }
  boolTrue : env.constants ``Bool.true = some ci → ci = { uvars := 0, type := .bool }
  nat : env.contains ``Nat → env.contains ``Nat.zero ∧ env.contains ``Nat.succ
  natZero : env.constants ``Nat.zero = some ci → ci = { uvars := 0, type := .nat }
  natSucc : env.constants ``Nat.succ = some ci →
    ci = { uvars := 0, type := .forallE .nat .nat }
  natAdd : env.ReflectsNatNatNat ``Nat.add Nat.add
  natPred : env.ReflectsNatNat ``Nat.pred Nat.pred
  natSub : env.ReflectsNatNatNat ``Nat.sub Nat.sub
  natMul : env.ReflectsNatNatNat ``Nat.mul Nat.mul
  natPow : env.ReflectsNatNatNat ``Nat.pow Nat.pow
  natGcd : env.ReflectsNatNatNat ``Nat.gcd Nat.gcd
  natMod : env.ReflectsNatNatNat ``Nat.mod Nat.mod
  natDiv : env.ReflectsNatNatNat ``Nat.div Nat.div
  natBEq : env.ReflectsNatNatBool ``Nat.beq Nat.beq
  natBLE : env.ReflectsNatNatBool ``Nat.ble Nat.ble
  natBitwise : env.ReflectsNatBitwise
  natLAnd : env.ReflectsNatNatNat ``Nat.land Nat.land
  natLOr : env.ReflectsNatNatNat ``Nat.lor Nat.lor
  natXor : env.ReflectsNatNatNat ``Nat.xor Nat.xor
  natShiftLeft : env.ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft
  natShiftRight : env.ReflectsNatNatNat ``Nat.shiftRight Nat.shiftRight
  charOfNat : env.constants ``Char.ofNat = some ci →
    ci = { uvars := 0, type := .forallE .nat .char }
  stringOfList : env.constants ``String.ofList = some ci →
    ci = { uvars := 0, type := .forallE .listChar .string } ∧
    env.HasType 0 [] .listCharNil .listChar ∧
    env.HasType 0 [] .listCharCons (.forallE .char <| .forallE .listChar .listChar)
