# Design: `VInductDecl.WF` and `VEnv.addInduct`

The abstract specification of inductive types for `Lean4Lean/Theory/Inductive.lean`.

Read-only design study. No repo file was modified.

---

## 0. Executive summary

Six decisions, two of which are *blocking findings* that need sign-off before any code
is written.

1. **`VInductDecl` must change shape.** The current record (`uvars`, `nparams`,
   `types : List VInductiveType` where a `VInductiveType` is just a name + a closed
   `VExpr` type) does not determine the recursor. The kernel builds the recursor from
   the *whnf-normalised* telescopes it walked while checking, and those are not
   recoverable from the stored types (`Add.lean:79,85,89` whnf at every spine step). So
   `addInduct` cannot be a function of the current `VInductDecl`. I propose a structured
   `VInductDecl` that carries the parameter telescope, per-type index telescope,
   per-constructor field telescope with each field classified recursive/non-recursive,
   and the constructor's result indices — with the *surface* types kept alongside and
   tied to the canonical ones by `IsDefEqU`. §2.

2. **The `Params`/`Pattern` API cannot express recursor ι-rules as it stands, and it
   cannot express the *existing* `quotDefEq` either.** `VDefEq.lhs` is a **closed** term
   (`VDefEq.WF` types it in `[]`), so any rule with parameters is λ-wrapped; but
   `Pattern.Matches` only matches `const`/`app` spines, never a `lam`. Therefore
   `Params.extra_pat` is today satisfiable only by environments whose every defeq is a
   bare δ-rule `.const c ls ≡ v`. Minimal fix in §7.1: relax `extra_pat` to "peel `n`
   leading lambdas, then match". `IsDefEq`, `VDefEq`, `Pattern.Matches`, the `vdefeq`
   elaborator and **`Theory/Quot.lean` all stay exactly as they are** — one class field
   and one proof change. (The alternative the coordinator raised, putting `VDefEq` in
   applied form with pattern metavariables, would force `quotDefEq`, the `vdefeq`
   elaborator and `QuotLemmas.lean` to be re-encoded, plus a substitution premise on
   `IsDefEq.extra`. Rejected; see §7.1.)

3. **`Pattern` additionally needs per-`const`-leaf universe levels.** `Matches` keeps
   only the level list of the *head* constant (`Matches.app` drops `f2`). The ι-rule's
   pattern is `rec.{ls} a … (c.{ls'} b …)`, and the rule's right-hand side is built at
   `ls`; discharging `pat_wf` needs `ls ≈ ls'`, which is currently unstateable. Fix in
   §7.2: index `m1` by an `LPath` and add a `Check.level` form. This is *also* needed by
   `quotDefEq` (`Quot.lift.{u,v}` vs `Quot.mk.{u}`).

4. **Side conditions carry their weight: `Pattern.Check` breaks the injectivity
   circularity.** `pat_wf` for an ι-redex `rec p m e ι (c p' b)` needs `ι ≡ π[p,b]`,
   `p' ≡ p` and `ls ≈ ls'` — all three follow from well-typedness only via
   *rigid-head application* injectivity, which is downstream of Church–Rosser, which is
   downstream of `Params`. (Π-injectivity and unique typing are a different matter: they
   live in `Injectivity`/`UniqueTyping`, which `ChurchRosser` *imports*, so `Params`'s
   fields may use them freely.) Putting the three into the rule's `Check` makes them
   *hypotheses* of `pat_wf`, and `extra_pat` discharges them by reflexivity/β. No
   circularity. §7.3.

4b. **Two further `Params` axioms are needed and only one of them is true as proposed.**
   `pat_major_not_pi` (a major premise never has a Π-type) *is* satisfied by `addInduct`
   environments, but its proof is a new rigidity lemma of the `sort_forallE_inv` class,
   not something the inductive spec can discharge by itself; what the spec must supply is
   the fact that an inductive type constant is never the head of any rule. `pat_major_prop`
   (major is a proof ⇒ redex is a proof) is **false for large-eliminating `Prop`
   inductives** — `Eq.rec`/`Acc.rec` are exactly the counterexamples. §7.6 gives the
   corrected split and the canonicity lemma that `LECond` was designed to deliver.

5. **Structure eta is not expressible as a `VDefEq` and never will be.** It is an
   extensionality rule (surjective pairing); its LHS is a bare variable. It needs a new
   `IsDefEq` constructor and matching `NormalEq` constructors, exactly parallel to the
   existing `eta`/`NormalEq.etaL/etaR`. §6.3. K-like reduction, by contrast, needs
   **nothing**: it is `proofIrrel` + the ordinary ι-rule (§6.1).

6. **Nested inductives *do* concern this layer.** `ElimNestedInductive` runs before
   `AddInductive.run`, but `Environment.addInductive` then *rewrites the environment* with
   `restoreNested`: the constants that end up in `env'` have types mentioning
   `List (Tree α)`, not the auxiliary `_nested.List_1 α`, and those two constants are not
   definitionally equal. So the final environment is not an instance of the non-nested
   `addInduct` for any declaration. §9.3 gives a generalisation that covers it
   ("companion types") and recommends scoping it as a follow-on.

Everything below is written against the repo as of `cf90def`.

---

## 1. What the kernel actually checks — the facts the spec must match

Extracted from `Lean4Lean/Inductive/Add.lean` and `Lean4Lean/Inductive/Reduce.lean`.
These are the constraints the design has to satisfy; each is cited.

| # | Fact | Where |
|---|---|---|
| F1 | The *inductive types'* pi-spines are walked **with `whnf` at every step**. So `T.type` is only definitionally a pi-telescope. | `checkInductiveTypes`, `Add.lean:79,85,89,95` |
| F2 | The *constructor types'* pi-spines are walked **without whnf**. So a constructor type is syntactically `∀ params fields, I p args`. | `checkConstructors.loop`, `Add.lean:218` |
| F3 | The parameter binder types come from the **first** inductive type; later types and every constructor only have to be `isDefEq` to them. | `Add.lean:82, 221` |
| F4 | Result levels of the block's types must be `isEquiv`, not equal. | `Add.lean:102` |
| F5 | Constructor result: head is literally `.const I_j (lparams.map .param)`, the first `nparams` args are literally the parameter fvars, the remaining args contain **no** occurrence of the block's type constants. | `isValidIndAppIdx`, `Add.lean:157` |
| F6 | Every non-parameter constructor argument `dom` gets `ensureType dom = Sort ℓ'` and must satisfy `ℓ.isAlwaysZero ∨ ℓ.geq' ℓ'`. | `Add.lean:226` |
| F7 | Positivity: `whnf dom`; if it has no occurrence of the block's types, accept. Otherwise it must be `∀ξ. I_j p π` with every `ξ`-domain and every index `π` occurrence-free. (`checkPositivity` walks with `whnf`; ending at `isValidIndApp?`.) So each field is *either* occurrence-free *or* strictly of that shape. | `checkPositivity`, `isRecArg`, `Add.lean:184,173` |
| F8 | A field may depend on **earlier recursive fields** (Carneiro's grammar forbids this; the kernel allows it, e.g. mutual `A`/`B : A → Type`). | `loopCtorArgs` binds all fields in one flat telescope, `Add.lean:335` |
| F9 | Large elimination: `resultLevel.isNeverZero`, or exactly one type in the block with ≤1 constructor, and in the 1-constructor case every non-parameter field whose type's sort is not `isAlwaysZero` occurs syntactically among the result type's arguments. | `isLargeEliminator`, `Add.lean:258` |
| F10 | The elimination level is a **fresh universe parameter prepended** to the declaration's: `getRecLevelParams elimLevel lparams = u :: lparams`. Otherwise `.zero` and the same parameters. | `Add.lean:413,416` |
| F11 | Recursor type: `∀ params motives minors indices (major), motive_j indices major`; motives/minors/indices come from the whnf'd telescopes; `inferImplicit` only touches binder info (invisible to `VExpr`). | `Add.lean:477` |
| F12 | `I_j.rec` gets a rule for **its own** constructors only; the minor index is threaded across the whole block. | `mkRecRules`, `Add.lean:419,471` |
| F13 | `RecursorRule.rhs = λ params motives minors fields. minor_q fields ihs`, and reduction applies it to `recArgs[0 .. firstIndexIdx)` then to the constructor's last `nfields` arguments. **Indices are dropped; the constructor's level arguments are ignored.** The kernel's reduct is a β-*redex* chain, not a substituted term. | `mkRecRules`, `Add.lean:441`; `inductiveReduceRec`, `Reduce.lean:99–107` |
| F14 | Recursive-argument IH: `v_i = λ x::ξ. I_{r}.rec params motives minors π[b,x] (u_i x)` where `ξ`, `π` come from `whnf (inferType u_i)`. | `mkRecRules.loopU`, `Add.lean:430` |
| F15 | K-like reduction fires for a single-type, `isAlwaysZero`-level, single-constructor block whose constructor takes only parameters; `toCtorWhenK` checks `isDefEq` of the major's type against the nullary constructor's type. | `isKTarget`, `Add.lean:289`; `toCtorWhenK`, `Reduce.lean:29` |
| F16 | Structure eta fires for a non-recursive single-constructor type whose sort `isNeverZero`; `expandEtaStruct` rebuilds `mk p (proj 0 e) …`. | `toCtorWhenStruct`, `Reduce.lean:58` |
| F17 | `inferProj` allows indices, requires a single constructor, whnfs the constructor type at each of the `numParams + idx` steps, and — when the structure's sort is not `isNeverZero` — requires every dependent field domain and the projected domain to be a `Prop`. | `TypeChecker.lean:233` |

Two divergences from Carneiro (`~/lean-type-theory/axioms.tex` §"Inductive types") that the
design must be aware of:

* F8 above: Carneiro's `\ctor` rule for recursive arguments uses a non-dependent arrow,
  so later fields may not mention a recursive field. The kernel allows it. **The spec
  follows the kernel** (more permissive); the model has to cope (§10).
* F6: Carneiro requires `imax(ℓ',ℓ) ≤ ℓ`; the kernel requires the strictly stronger
  `ℓ ≈ 0 ∨ ℓ' ≤ ℓ`. **The spec uses Carneiro's**, which is implied by the kernel's, so
  refinement goes through and the spec is not hostage to the kernel's level-algebra
  incompleteness. (This is the `imax 1 u ≤ u` point in `divergences.md:14`; the *spec*
  accepts `inductive T.{u} : Sort u where mk : Bool → T`, the *checker* rejects it. That
  direction is harmless.)

---

## 2. Data: the new `VInductDecl`

`Lean4Lean/Theory/VDecl.lean` currently has

```lean
structure VInductiveType extends VConstVal where ctors : List VConstVal
structure VInductDecl where uvars : Nat; nparams : Nat; types : List VInductiveType
```

This is *only* a list of names and closed types. Two things are missing and cannot be
recovered: (a) the whnf'd telescopes (F1), (b) the classification of fields as
recursive/non-recursive together with the `ξ`/`π` data (F7, F14). Both are inputs to the
recursor type and the ι-rules. So the record has to carry them.

`Theory/` is explicitly free ("proof machinery you can freely design", `CLAUDE.md`), and
`Verify/Soundness.lean` (frozen) does not mention `VInductDecl`. The only downstream
users are `Theory/Consistency.lean` (three literals, §11.1) and
`Verify/Environment/Basic.lean`'s empty `AddInduct` (§9).

### 2.1 Telescope conventions

Two conventions coexist in the repo: contexts (`List VExpr`, **innermost-first**, as in
`Lookup`/`OnCtx`) and telescopes-as-written. I use **declaration order** (outermost
first) for stored telescopes, and `.reverse` to obtain the corresponding context. New
helpers, to go in `Theory/VExpr.lean`:

```lean
namespace VExpr

/-- `mkPi [A₁,…,Aₙ] B = ∀ A₁ … Aₙ, B`.  `Aᵢ` lives in context `(As.take i).reverse ++ Γ₀`,
`B` in `As.reverse ++ Γ₀`. -/
def mkPi : List VExpr → VExpr → VExpr
  | [],      B => B
  | A :: As, B => .forallE A (mkPi As B)

def mkLams : List VExpr → VExpr → VExpr
  | [],      b => b
  | A :: As, b => .lam A (mkLams As b)

/-- `f.mkApp [a₁,…,aₙ] = f a₁ … aₙ`. -/
def mkApp (f : VExpr) : List VExpr → VExpr
  | []      => f
  | a :: as => (VExpr.app f a).mkApp as

/-- The arguments that apply a function to a telescope of length `n` whose innermost
binder is at de Bruijn index `lo`: `[.bvar (lo+n-1), …, .bvar lo]` (declaration order). -/
def bvars (lo n : Nat) : List VExpr := (List.range n).map fun i => .bvar (lo + n - 1 - i)

/-- Re-index a declaration-order telescope living over `Γ₀` so that it lives over
`Ξ ++ Γ₀` with `|Ξ| = m`. -/
def liftTele (m : Nat) (As : List VExpr) : List VExpr :=
  As.zipIdx.map fun (A, i) => A.liftN m i

/-- The composite re-indexing used throughout: a term over `(fields<i).reverse ++ P.reverse`
into a context where `off` binders were inserted between the fields and `P`, and `d`
binders below the fields; `j` is the number of binders *inside* the term's own scope. -/
def shift (off d : Nat) (i : Nat) (e : VExpr) (j := 0) : VExpr :=
  (e.liftN off (i + j)).liftN d j

def shiftTele (off d i : Nat) (As : List VExpr) : List VExpr :=
  As.zipIdx.map fun (A, j) => shift off d i A j

end VExpr
```

`shift`/`shiftTele` are the only index arithmetic in the whole construction; every
occurrence below is an instance of them. (`liftTele m = shiftTele m 0 0`.)

### 2.2 The record

```lean
namespace Lean4Lean

/-- Data of a recursive constructor field, i.e. one of the form `∀ ξ, I_idx params args`. -/
structure VIndRecArg where
  /-- `ξ`, in declaration order, over `params ++ fields<i`.  Contains no block constant. -/
  binders : List VExpr
  /-- which type of the block this field recurses into -/
  idx : Nat
  /-- `π`, the index arguments, over `params ++ fields<i ++ ξ`.  No block constant. -/
  args : List VExpr

/-- One constructor field, in the context `params ++ fields<i`. -/
structure VIndField where
  /-- The field's type, exactly as it appears in the constructor's type. -/
  type : VExpr
  /-- A level with `⊢ type : Sort lvl`.  (Sorts are not unique in the abstract theory
  — `IsDefEqU.sort_inv` is open — so the witness is recorded, not derived.) -/
  lvl  : VLevel
  /-- `none` for a non-recursive field; `some r` when `type` is definitionally
  `mkPi r.binders (I_{r.idx} params r.args)`. -/
  «rec» : Option VIndRecArg

structure VIndCtor where
  name : Name
  /-- The constructor's own parameter binder types (F3): `nparams` of them, pairwise
  definitionally equal to the block's `params` but not necessarily syntactically equal. -/
  params : List VExpr
  /-- The fields, in declaration order, over the block's `params`. -/
  fields : List VIndField
  /-- The index arguments of the result, over `params ++ fields`.  No block constant (F5). -/
  args : List VExpr

structure VIndType where
  name : Name
  /-- The type **as stored in the environment**.  Only definitionally a pi-telescope (F1). -/
  type : VExpr
  /-- The index telescope, in declaration order, over the block's `params`. -/
  indices : List VExpr
  ctors : List VIndCtor

structure VInductDecl where
  uvars  : Nat
  /-- The parameter telescope, in declaration order.  `nparams = params.length`. -/
  params : List VExpr
  /-- The common result universe of the block (F4 absorbs the `≈` slack into `canon`). -/
  lvl    : VLevel
  types  : List VIndType
  /-- Whether the recursor eliminates into an arbitrary universe (F9/F10). A *claim*;
  `WF` only constrains it in the `true` direction, so it need not be decidable. -/
  isLE   : Bool
```

Note `VIndCtor` has **no** `type` field: by F2 the constructor's stored type is exactly
`mkPi (C.params ++ C.fields.map (·.type)) (C.canonResult …)`, so it is *derived*
(`VIndCtor.type`, §3). `VIndType.type` on the other hand must be stored, because F1
makes it only definitionally the canonical form.

### 2.3 Derived accessors

```lean
namespace VInductDecl
variable (D : VInductDecl)

abbrev np   : Nat := D.params.length
abbrev nm   : Nat := D.types.length
/-- All constructors of the block in kernel order, tagged with their type's index (F12). -/
def ctorsAll : List (Nat × VIndCtor) :=
  D.types.zipIdx.flatMap fun (T, j) => T.ctors.map fun C => (j, C)
abbrev nmin : Nat := D.ctorsAll.length

def blockNames : List Name := D.types.map (·.name)
def allNames : List Name :=
  D.types.flatMap fun T => T.name :: mkRecName T.name :: T.ctors.map (·.name)

def elimLvl  : VLevel := if D.isLE then .param 0 else .zero          -- F10
def recUvars : Nat    := if D.isLE then D.uvars + 1 else D.uvars     -- F10
/-- The block's own universe parameters in its own numbering. -/
def ownLvls  : List VLevel := VLevel.params D.uvars
/-- The same, in the recursor's numbering (shifted by 1 when `isLE`). -/
def selfLvls : List VLevel :=
  (List.range D.uvars).map fun i => .param (if D.isLE then i + 1 else i)
```

and the occurrence check of F5/F7:

```lean
def VExpr.NoConsts (S : List Name) : VExpr → Prop
  | .bvar _ | .sort _ => True
  | .const c _        => c ∉ S
  | .app a b | .lam a b | .forallE a b => NoConsts S a ∧ NoConsts S b

def VInductDecl.NoBlock (D : VInductDecl) (e : VExpr) : Prop := e.NoConsts D.blockNames
```

`mkRecName n := .str n "rec"` (Lean's `mkRecName`), so `Theory/` need not import
`Lean.Declaration` for it.

---

## 3. Canonical types

All of these are *definitions*; `WF` ties the stored types to them.

```lean
namespace VInductDecl
variable (D : VInductDecl)

/-- `I_j` at the block's own levels, applied to the parameters (which sit `k` binders
away) and to `args`. -/
def tyApp (j k : Nat) (args : List VExpr) : VExpr :=
  (VExpr.const (D.types.getD j default).name D.ownLvls).mkApp (bvars k D.np ++ args)

/-- The same at the *recursor's* level numbering (used inside recursor types/ι-rules). -/
def tyApp' (j k : Nat) (args : List VExpr) : VExpr :=
  (VExpr.const (D.types.getD j default).name D.selfLvls).mkApp (bvars k D.np ++ args)

def ctorApp' (C : VIndCtor) (k : Nat) (args : List VExpr) : VExpr :=
  (VExpr.const C.name D.selfLvls).mkApp (bvars k D.np ++ args)

/-- Canonical type of the `j`-th inductive type. -/
def VIndType.canonType (T : VIndType) : VExpr :=
  mkPi (D.params ++ T.indices) (.sort D.lvl)

/-- Canonical type of a recursive field: `i` = number of preceding fields. -/
def VIndRecArg.canonResult (r : VIndRecArg) (i : Nat) : VExpr :=
  D.tyApp r.idx (r.binders.length + i) r.args
def VIndRecArg.canonType (r : VIndRecArg) (i : Nat) : VExpr :=
  mkPi r.binders (r.canonResult D i)

/-- Result type of a constructor, over `params ++ fields`. -/
def VIndCtor.canonResult (j : Nat) (C : VIndCtor) : VExpr :=
  D.tyApp j C.fields.length C.args
/-- Type of a constructor, exactly as stored in the environment (F2). -/
def VIndCtor.type (j : Nat) (C : VIndCtor) : VExpr :=
  mkPi (C.params ++ C.fields.map (·.type)) (C.canonResult D j)
```

---

## 4. `VInductDecl.WF`

The kernel checks constructors in the environment that **already contains the block's
type constants** (`Add.lean:458`), and a constructor's type mentions them. So the
constructor conditions cannot be stated in `env`; the definition stages the environment,
mirroring `declareInductiveTypes` / `checkConstructors`.

```lean
/-- Add only the block's type constants. -/
def VEnv.addIndTypes (env : VEnv) (D : VInductDecl) : Option VEnv :=
  D.types.foldlM (fun env T => env.addConst T.name ⟨D.uvars, T.type⟩) env
```

### 4.1 Fields

```lean
/-- `Γ` is `(C.fields.take i).map (·.type) |>.reverse ++ D.params.reverse`, the context of
field `i`. -/
structure VIndField.WF (env : VEnv) (D : VInductDecl) (Γ : List VExpr) (i : Nat)
    (F : VIndField) : Prop where
  /-- the recorded sort is a sort of the field's type -/
  hasType : env.HasType D.uvars Γ F.type (.sort F.lvl)
  /-- Carneiro's level constraint, implied by F6 -/
  level   : VLevel.imax F.lvl D.lvl ≤ D.lvl
  /-- strict positivity, F7 -/
  pos     :
    match F.rec with
    | none   => D.NoBlock F.type
    | some r =>
      r.idx < D.nm ∧
      r.args.length = (D.types.getD r.idx default).indices.length ∧
      (∀ B ∈ r.binders, D.NoBlock B) ∧
      (∀ a ∈ r.args, D.NoBlock a) ∧
      OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars) ∧
      env.HasType D.uvars (r.binders.reverse ++ Γ) (r.canonResult D i) (.sort D.lvl) ∧
      env.IsDefEqU D.uvars Γ F.type (r.canonType D i)
```

Remarks.

* `pos` in the `none` case is *only* an occurrence condition — no shape condition. That
  is exactly F7's early return.
* The explicit `OnCtx` and `HasType` for `ξ`/`I p π` avoid needing Π-inversion
  (`IsDefEqU.forallE_inv` is a `sorry`) to extract them from `hasType` + the defeq. The
  refinement supplies them directly, because `isRecArg`/`checkPositivity` walked the
  telescope with genuine `withLocalDecl`s.
* `IsDefEqU` (not `IsDefEq … (.sort _)`) suffices: `IsDefEqU.of_l` upgrades it using
  `hasType`.

### 4.2 Constructors

```lean
structure VIndCtor.WF (env : VEnv) (D : VInductDecl) (j : Nat) (T : VIndType)
    (C : VIndCtor) : Prop where
  /-- F3: the constructor's own parameter binders are a defeq copy of the block's -/
  params_len : C.params.length = D.np
  params_eq  : env.IsDefEqCtx D.uvars [] C.params.reverse D.params.reverse
  /-- every field is well-formed in its own context -/
  fields : ∀ i F, C.fields[i]? = some F →
    F.WF env D (((C.fields.take i).map (·.type)).reverse ++ D.params.reverse) i
  /-- F5 -/
  args_len   : C.args.length = T.indices.length
  args_fresh : ∀ a ∈ C.args, D.NoBlock a
  /-- the result type is a type; this also delivers well-typedness of `C.args` -/
  result : env.HasType D.uvars ((C.fields.map (·.type)).reverse ++ D.params.reverse)
             (C.canonResult D j) (.sort D.lvl)
```

`env.IsType D.uvars [] (C.type D j)` is *derivable* from the above (`IsType.forallE`
chaining plus `IsDefEqCtx`-transport for the parameter binders), so it is not a field.

### 4.3 Types, large elimination, and the whole thing

```lean
structure VIndType.WF (env : VEnv) (D : VInductDecl) (T : VIndType) : Prop where
  indices : OnCtx (T.indices.reverse ++ D.params.reverse) (env.IsType D.uvars)
  isType  : env.IsType D.uvars [] T.type
  /-- F1/F4: only definitional equality is available here -/
  canon   : env.IsDefEqU D.uvars [] T.type (T.canonType D)

/-- Carneiro's `Γ;t:F ⊢ K LE`, in the form F9 delivers it. -/
def VInductDecl.LECond (D : VInductDecl) : Prop :=
  D.lvl.IsNeverZero ∨
  ∃ T, D.types = [T] ∧
    (T.ctors = [] ∨
     ∃ C, T.ctors = [C] ∧
       ∀ i F, C.fields[i]? = some F →
         F.lvl ≈ .zero ∨ VExpr.bvar (C.fields.length - 1 - i) ∈ C.args)

structure VInductDecl.WF (env : VEnv) (D : VInductDecl) : Prop where
  types_ne : D.types ≠ []
  params   : OnCtx D.params.reverse (env.IsType D.uvars)
  types    : ∀ T ∈ D.types, T.WF env D
  ctors    : ∀ env₁, env.addIndTypes D = some env₁ →
             ∀ j T, D.types[j]? = some T → ∀ C ∈ T.ctors, C.WF env₁ D j T
  isLE     : D.isLE = true → D.LECond
```

Notes.

* `LECond` is purely syntactic/level-theoretic — no `env`. In the one-constructor case,
  field `i` (declaration order) is `.bvar (nf-1-i)` in the context
  `fields.reverse ++ params.reverse`, and `C.args` lives there, so
  `.bvar (nf-1-i) ∈ C.args` is exactly F9's `type.getAppArgs.contains arg` (a field fvar
  can never be one of the `nparams` leading parameter arguments, which is why we only
  scan `args`).
* `F.lvl ≈ .zero` is implied by `Level.isAlwaysZero` — the direction refinement needs.
* Nothing about K-like reduction, structures, or eta appears here; see §6.
* `WF` says nothing about recursor types or ι-rules: their well-formedness is a
  **theorem** (§8), which is the entire content of `addInduct_WF`.

---

## 5. `VEnv.addInduct`

### 5.1 The motives

Motive `t` lives over `params ++ motives<t`, so `t` binders sit between it and the
parameters.

```lean
def VInductDecl.motiveType (D : VInductDecl) (t : Nat) : VExpr :=
  let T  := D.types.getD t default
  let ni := T.indices.length
  mkPi (liftTele t T.indices) <|
    .forallE (D.tyApp' t (ni + t) (bvars 0 ni)) (.sort D.elimLvl)

def VInductDecl.motives (D : VInductDecl) : List VExpr :=
  (List.range D.nm).map D.motiveType
```

### 5.2 The minor premises

Minor `q` (the `q`-th entry `(t, C)` of `ctorsAll`) lives over
`params ++ motives ++ minors<q`, so `off := D.nm + q` binders separate its fields from
the parameters.  Write `nf := C.fields.length`.

```lean
/-- The recursive fields of `C`, as `(declaration index, data)`, in declaration order. -/
def VIndCtor.recFields (C : VIndCtor) : List (Nat × VIndRecArg) :=
  C.fields.zipIdx.filterMap fun (F, i) => F.rec.map fun r => (i, r)

/-- The induction-hypothesis telescope of minor `q` (F14's `δ`), declaration order,
over `params ++ motives ++ minors<q ++ fields`. -/
def VInductDecl.ihTypes (D : VInductDecl) (q : Nat) (C : VIndCtor) : List VExpr :=
  let off := D.nm + q
  let nf  := C.fields.length
  C.recFields.zipIdx.map fun ((i, r), s) =>
    let d  := nf - i + s                      -- binders below `fields<i`: fields i..nf-1, ihs<s
    let nξ := r.binders.length
    mkPi (shiftTele off d i r.binders) <|
      (VExpr.bvar (nξ + s + nf + q + (D.nm - 1 - r.idx))).mkApp <|
        (r.args.zipIdx.map fun (a, _) => shift off d i a nξ) ++
        [(VExpr.bvar (nξ + s + (nf - 1 - i))).mkApp (bvars 0 nξ)]

def VInductDecl.minorType (D : VInductDecl) (q t : Nat) (C : VIndCtor) : VExpr :=
  let off := D.nm + q
  let nf  := C.fields.length
  let V   := D.ihTypes q C
  let nr  := V.length
  mkPi (liftTele off (C.fields.map (·.type)) ++ V) <|
    (VExpr.bvar (nr + nf + q + (D.nm - 1 - t))).mkApp <|
      C.args.map (shift off nr nf) ++ [D.ctorApp' C (nr + nf + off) (bvars nr nf)]

def VInductDecl.minors (D : VInductDecl) : List VExpr :=
  D.ctorsAll.zipIdx.map fun ((t, C), q) => D.minorType q t C
```

This is `mkRecInfos.loopCtors`/`loopU` (`Add.lean:379–393`) transcribed: `minorTy =
lctx.mkForall bu (lctx.mkForall v motiveApp)` with `motiveApp = motive_t itIndices
(c params bu)`.

### 5.3 The recursor type

```lean
def VInductDecl.recType (D : VInductDecl) (j : Nat) : VExpr :=
  let T  := D.types.getD j default
  let ni := T.indices.length
  mkPi (D.params ++ D.motives ++ D.minors ++ liftTele (D.nm + D.nmin) T.indices) <|
    .forallE (D.tyApp' j (ni + D.nmin + D.nm) (bvars 0 ni)) <|
      (VExpr.bvar (1 + ni + D.nmin + (D.nm - 1 - j))).mkApp (bvars 1 ni ++ [.bvar 0])
```

= F11 verbatim.

### 5.4 The ι-rules

The rule's binder context (F13) is `params ++ motives ++ minors ++ fields`, with
`off := D.nm + D.nmin`.

```lean
def VInductDecl.iotaCtx (D : VInductDecl) (C : VIndCtor) : List VExpr :=
  D.params ++ D.motives ++ D.minors ++ liftTele (D.nm + D.nmin) (C.fields.map (·.type))

/-- The IH *values* (F14's `v`), in `iotaCtx`. -/
def VInductDecl.ihValues (D : VInductDecl) (C : VIndCtor) : List VExpr :=
  let off := D.nm + D.nmin
  let nf  := C.fields.length
  C.recFields.map fun (i, r) =>
    let d  := nf - i
    let nξ := r.binders.length
    mkLams (shiftTele off d i r.binders) <|
      (VExpr.const (mkRecName (D.types.getD r.idx default).name)
          (VLevel.params D.recUvars)).mkApp <|
        bvars (nξ + nf + off) D.np ++ bvars (nξ + nf + D.nmin) D.nm ++
        bvars (nξ + nf) D.nmin ++
        r.args.map (fun a => shift off d i a nξ) ++
        [(VExpr.bvar (nξ + (nf - 1 - i))).mkApp (bvars 0 nξ)]

/-- The kernel's `RecursorRule.rhs` (F13). -/
def VInductDecl.iotaLam (D : VInductDecl) (q : Nat) (C : VIndCtor) : VExpr :=
  let nf := C.fields.length
  mkLams (D.iotaCtx C) <|
    (VExpr.bvar (nf + (D.nmin - 1 - q))).mkApp (bvars 0 nf ++ D.ihValues C)

/-- The left-hand side, un-abstracted. -/
def VInductDecl.iotaLhs (D : VInductDecl) (j : Nat) (C : VIndCtor) : VExpr :=
  let off := D.nm + D.nmin
  let nf  := C.fields.length
  (VExpr.const (mkRecName (D.types.getD j default).name)
      (VLevel.params D.recUvars)).mkApp <|
    bvars (nf + off) D.np ++ bvars (nf + D.nmin) D.nm ++ bvars nf D.nmin ++
    C.args.map (·.liftN off nf) ++
    [D.ctorApp' C (nf + off) (bvars 0 nf)]

def VInductDecl.iotaType (D : VInductDecl) (j : Nat) (C : VIndCtor) : VExpr :=
  let off := D.nm + D.nmin
  let nf  := C.fields.length
  (VExpr.bvar (nf + D.nmin + (D.nm - 1 - j))).mkApp <|
    C.args.map (·.liftN off nf) ++ [D.ctorApp' C (nf + off) (bvars 0 nf)]

def VInductDecl.iotaRule (D : VInductDecl) (j q : Nat) (C : VIndCtor) : VDefEq :=
  let Γ' := D.iotaCtx C
  { uvars := D.recUvars
    lhs   := mkLams Γ' (D.iotaLhs j C)
    rhs   := mkLams Γ' ((D.iotaLam q C).mkApp (bvars 0 Γ'.length))
    type  := mkPi Γ' (D.iotaType j C) }

def VInductDecl.iotaRules (D : VInductDecl) : List VDefEq :=
  D.ctorsAll.zipIdx.filterMap fun ((j, C), q) => some (D.iotaRule j q C)
```

**Why `rhs` is the η-expansion `λΓ'. Λ Γ'` rather than `Λ`'s body.** Two reasons, both
load-bearing:

1. It is *literally what the kernel computes* (F13): `reduceRecursor` builds
   `mkAppRange (rule.rhs …) …`, i.e. an unreduced β-redex chain `Λ a … b …`. Choosing
   the same reduct makes `reduceRecursor.WF` a syntactic match rather than a β-chase.
2. It makes `Params.extra_pat` hold **on the nose** (§7.4): the pattern's right-hand side
   is `Pattern.RHS.fixed Λ` applied to the matched argument paths, and after peeling the
   `|Γ'|` leading lambdas from `iotaRule.rhs` the body is *exactly* that term.

### 5.5 `addInduct` itself

```lean
def VEnv.addIndCtors (env : VEnv) (D : VInductDecl) : Option VEnv :=
  D.types.zipIdx.foldlM (fun env (T, j) =>
    T.ctors.foldlM (fun env C => env.addConst C.name ⟨D.uvars, C.type D j⟩) env) env

def VEnv.addIndRecs (env : VEnv) (D : VInductDecl) : Option VEnv :=
  D.types.zipIdx.foldlM (fun env (T, j) =>
    env.addConst (mkRecName T.name) ⟨D.recUvars, D.recType j⟩) env

def VEnv.addIndRules (env : VEnv) (D : VInductDecl) : VEnv :=
  D.iotaRules.foldl VEnv.addDefEq env

def VEnv.addInduct (env : VEnv) (D : VInductDecl) : Option VEnv := do
  let env ← env.addIndTypes D
  let env ← env.addIndCtors D
  let env ← env.addIndRecs  D
  return env.addIndRules D
```

Same shape as `VEnv.addQuot`, which is the point: `addQuot_WF` in
`Theory/Typing/QuotLemmas.lean` is the template for `addInduct_WF`, and
`HasObjects.bind_const` chains give the "the environment really contains these"
accessor lemmas.

`addConst` returns `none` on a duplicate name, so `addInduct = some _` already implies
that all of `D.allNames` are fresh **and pairwise distinct** — which is precisely the
global disjointness invariant the `Params` orthogonality axioms need (§7.5).

---

## 6. Things that do *not* need to be in the spec, and one that does

### 6.1 K-like reduction: derivable, nothing to add

F15 says K fires only for a single-type, `isAlwaysZero`-level, single-constructor block
whose constructor takes only parameters, and `toCtorWhenK` verifies
`isDefEq (typeof major) (typeof (c p))`. Then:

* `D.lvl ≈ .zero`, so `I p a : Sort D.lvl` and `.sortDF` + `.defeqDF` give
  `Γ ⊢ I p a : .sort .zero`;
* `major : I p a` and `c p : I p π` with `I p a ≡ I p π` (this is the `isDefEq` the
  kernel performed, so the *checker* hands it to us — no injectivity needed);
* `IsDefEq.proofIrrel` gives `major ≡ c p`;
* congruence + the ordinary ι-rule finishes.

So **K contributes no `VDefEq` and no side condition to `VInductDecl.WF`.** It becomes a
lemma consumed by `reduceRecursor.WF`. This is a genuine simplification over adding a
second family of rules; it also keeps `Params.Pat` free of a K pattern (which would have
been `rec … (anything)` and would have destroyed `pat_uniq`).

The abstract counterpart of K is strictly stronger than the checker's `isKTarget`: for
*any* subsingleton eliminator (single constructor, possibly with fields — `Acc`), every
major premise is definitionally a constructor application, with the fields reconstructed
by the recursor. That is lemma M3 in §7.6, and it is what the `¬pat_small` branch of the
Church–Rosser development needs. The checker only implements the 0-field case (F15), so
the abstract relation is *ahead of* the implementation here — sound, but it means
`reduceRecursor.WF` does not follow mechanically from the ParRed development.

### 6.2 Structures and `TrProj`

A *structure* is a block with one type, one constructor, and (for `expandEtaStruct`) no
recursive fields. Define, over an environment:

```lean
/-- `env` declares `S` as a single-constructor inductive with the given data. -/
structure VEnv.IsStructure (env : VEnv) (S : Name) (D : VInductDecl) (T : VIndType)
    (C : VIndCtor) : Prop where
  decl  : env.HasInduct D                     -- §8, lemma G3
  types : D.types = [T]
  name  : T.name = S
  ctors : T.ctors = [C]
```

`numParams = D.np`, field types `C.fields.map (·.type)`, `numIndices = T.indices.length`
— all read off directly, which is what requirement 4 asks for.

**`TrProj`.** `Verify/Typing/Expr.lean:67` currently declares

```lean
def TrProj : ∀ (Γ : List VExpr) (structName : Name) (idx : Nat) (e : VExpr), VExpr → Prop := sorry
```

It needs the environment and universe count (the structure's level arguments and
parameters have to be read off the *type of `e`*), so the signature changes to
`TrProj (env : VEnv) (U : Nat) (Γ) (S) (i) (e) (e'')`. `TrExprS` already has `env`/`Us`
in scope at the call site, so this is a local change.

Projections are *not* primitive in `VExpr`; encode them by the recursor, which is what
they are:

```lean
/-- `S.rec.{ℓ, ls} p (fun ι x => A) (fun f₀ … f_{n-1} => f_i) e`, the `i`-th projection. -/
def VInductDecl.projTerm (D : VInductDecl) (C : VIndCtor) (ls : List VLevel)
    (ps : List VExpr) (mot : VExpr) (i : Nat) (e : VExpr) : VExpr :=
  let nf := C.fields.length
  ((VExpr.const (mkRecName (D.types.getD 0 default).name) ls).mkApp
      (ps ++ [mot, mkLams (C.fields.map (·.type)) (.bvar (nf - 1 - i))])).app e

variable (env : VEnv) (U : Nat) in
inductive TrProj : List VExpr → Name → Nat → VExpr → VExpr → Prop
  | mk {D T C} :
    env.IsStructure S D T C →
    -- the level and parameter arguments read off the type of `e`
    env.HasType U Γ e ((VExpr.const S ls).mkApp (ps ++ ιs)) →
    ls.length = D.uvars → ps.length = D.np → ιs.length = T.indices.length →
    i < C.fields.length →
    -- the motive: `fun ι x => Aᵢ[ps, proj 0 x, …, proj (i-1) x]`, built by recursion on `i`
    ProjMotive env U Γ D T C ls ps i mot →
    -- F17's Prop side condition
    (¬ (D.lvl.inst ls).IsNeverZero → ProjIsProp env U Γ D C ls ps i) →
    TrProj Γ S i e (D.projTerm C (D.elimLvl.inst ls :: ls) ps mot i e)
```

with `ProjMotive` an auxiliary relation defined by recursion on `i` that builds
`fun (ι) (x : S ps ι) => (C.fields[i].type)[ps, TrProj … 0 x, …, TrProj … (i-1) x]`, and
`ProjIsProp` the "all dependent field domains and the projected domain are `Prop`"
condition of F17.

`TrProj` must be *functional* (`TrExprS.uniq` needs it): given `Γ, S, i, e` the output is
determined, because `IsStructure` pins `D` (only one inductive declaration can own the
name `S`; see the `HasInduct` uniqueness lemma G4 in §8), and `ls`/`ps`/`ιs` are
determined by unique typing. That last step needs `IsDefEq.uniq` + `const`-application
injectivity — i.e. `TrProj.uniq` is downstream of Church–Rosser. That is fine (it lives
in `Verify/`), but it is worth writing down: **`TrProj.uniq` is not provable before
`Params` is instantiated.**

The two easy consequences:

* `reduceProjCore.WF`: `proj S i (mk p f) ≡ f_i` follows from ι + β.
* `inferProj.WF`: the type of `projTerm … i e` is `mot ιs e`, which β-reduces to
  `A_i[…]`, i.e. exactly the kernel's `dom`.

### 6.3 Structure eta — the one genuinely missing rule

**Status: written.**  `Theory/Inductive/StructureEta.lean` carries the rule as
`VEnv.StructEta`, together with `VInductDecl'.etaExpansion` (its right-hand side) and the
two consequences the checker needs, `StructEta.unitLike` and `StructEta.congrSpine`.
`StructureExamples.lean` checks `etaExpansion` against Lean's own elaborator at `Prod`,
`Sigma`, `And` and `Subtype` — all two-field, two of them with a dependent second field.
Read that file, not this section, for the current statement; what follows is the design
rationale and the **two corrections** the original text needed.

`toCtorWhenStruct`/`tryEtaStructCore`/`isDefEqUnitLike` all rest on

  `e ≡ mk p (proj 0 e) … (proj (n-1) e)`   for `e : S p`, `S` a non-recursive
  single-constructor type with no indices.

This is surjective pairing. It is **not** derivable from ι, and it **cannot** be a
`VDefEq`: the equation's left-hand side is a variable, so no `Pattern` (which only
matches `const`-headed application spines) can match it, and `Params.extra_pat` would
fail. Nor can it be phrased with `mk` as the head: `Pattern.RHS` can only rebuild terms
from `fixed` closed constants and matched argument paths, and `e` is not among the
matched arguments.

#### Correction 1: **there is no `IsNeverZero` side condition**

This section used to propose

```lean
    (D.lvl.inst ls).IsNeverZero →                        -- F16 (L4L is stricter than C++ here)
```

taken from `toCtorWhenStruct`'s F16 guard.  **That condition is wrong for two of the rule's
three call sites.**  Checked gate-for-gate against both kernels
(`~/lean4/src/kernel/type_checker.cpp` `try_eta_struct_core` `:889`, `is_def_eq_unit_like`
`:1159`; `Lean4Lean/TypeChecker.lean:656` and `:849`): **neither `tryEtaStructCore` nor
`isDefEqUnitLike` tests the structure's universe at all.**  `tryEtaStructCore` tests
`isNonRecStructure`, which is `isRec = false ∧ ctors = [_] ∧ numIndices = 0`;
`isDefEqUnitLike` tests those plus `numFields = 0`.  Both therefore fire on `Prop`
structures — `And`, `True` — which an `IsNeverZero` rule would not cover.

Keeping the condition would not have been *unsound*; it would have made the rule useless at
two of its three sites.  The `Prop` case is independently free
(`VEnv.structEta_of_prop`: `IsDefEq.proofIrrel`, given that the η-expansion is well typed),
and at the checker level it is free without even the η-expansion —
`isDefEqUnitLike.WF_prop` (`Verify/TypeChecker/IsDefEq.lean`) relates the two inhabitants by
`proofIrrel` directly and is **proved**.  So the split is:

| | `Prop` case | non-`Prop` case |
|---|---|---|
| `isDefEqUnitLike` | `proofIrrel` — proved, `isDefEqUnitLike.WF_prop` | `StructEta.unitLike` |
| `tryEtaStructCore` | `proofIrrel`, once the loop's `TrProj`s are built | `StructEta.congrSpine` |

#### Correction 2: **a side condition is needed, but it is F17, not F16**

`IsDefEq` implies both sides are well typed, so a rule whose right-hand side is not well
typed is false, not merely useless.  For a small-eliminating block (`isLE = false`) the
projections in the η-expansion are recursor applications at elimination level
`(C.fields.getD k _).lvl`, legal only when that level is `≈ .zero`.  `VEnv.StructEta`
therefore carries

```lean
    D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero
```

which is `TrProj`'s recorded F17 clause **minus its "unused fields are exempt" guard**: eta
projects every field, so every field is in scope.  `Verify/Typing/ProjLevelWitness.lean`'s
`barDecl` — a two-field `Prop` structure whose field 0 has level `.succ .zero` and is unused —
is admissible for `TrProj` at `i = 1` and **not** admissible for structure eta, and that is
the difference this clause encodes.

#### The rule

```lean
def VEnv.StructEta (env : VEnv) : Prop :=
  ∀ {U Γ S D T C us ps e},
    env.IsStructure S D T C →                            -- includes C.recFields = []
    T.indices = [] →
    us.length = D.uvars → (∀ l ∈ us, l.WF U) → ps.length = D.np →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasType U Γ e ((VExpr.const S us).mkApp ps) →
    (D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    env.IsDefEq U Γ e (D.etaExpansion T C us ps e) ((VExpr.const S us).mkApp ps)
```

It is stated as a **property of an environment** rather than as a new `VEnv.IsDefEq`
constructor.  The content is identical — this is exactly the constructor's statement — and
the predicate form is what a consumer can use today, whereas adding the constructor is a
coordinated edit across `Theory/Typing/{Basic,Lemmas,Strong,UniqueTyping,ChurchRosser}.lean`
and `Verify/`.  When the constructor lands, `StructEta` becomes a one-line theorem rather
than being discarded.

Adding the constructor still needs, as before:

* two new `NormalEq` constructors `structEtaL`/`structEtaR`, mirroring `etaL`/`etaR`
  (`ChurchRosser.lean:104–111`);
* a `structEta` case in every induction over `IsDefEq`.  Because the conclusion has both
  sides at the *same* type, most cases are one-liners, as `eta`'s are.

The alternative — give `VExpr` a `proj` constructor and make projection + eta primitive — is
closer to `Lean.Expr` and would make `TrProj` trivial, but costs a new case in every `VExpr`
recursion in `Theory/` (≈4500 lines); still judged worse.

#### What the rule does *not* unblock

`tryEtaStructCore.WF` needs, besides `StructEta`, an `IsStructure` for the name the *kernel*
environment calls a structure.  `Verify/StructureBridge.lean` names that step
(`StructureBridge`).  It used to show — machine-checked — that the step does not follow from
`AddInduct`'s intended definition either, because `AddIndConsts`' shape predicates and
`TrConstant` constrained only a constant's name, level count and type.  **That is repaired**:
`IndShape`/`CtorShape` (`Verify/Environment/Basic.lean`) are now the shape predicates of both
`AddInductStages` and `AddInductStagesR`, and `AddInductStages.structure_fields` transports
every field of `IsStructure` except `types` and `decl`.

What blocks the bridge now is `VEnv.IsStructure.types` (`D.types = [T]`), which no shape
predicate can supply because it is **false** of what `isNonRecStructure` accepts: `isRec` is
computed block-wide, so each member of a mutual non-recursive block passes
`isNonRecStructure` while the block has more than one type
(`MutNonRec.indShapeOf_not_singleton`).  See `docs/handoff-inductive-add.md` §L.

---

## 7. The `Params` instantiation story

`Params` (`ChurchRosser.lean:12`) is the interface under which all of
`ChurchRosser.lean` (1386 lines) and `HeadReduction.lean` (696 lines) is proved, and
nothing in the repo instantiates it. Here is what it takes.

### 7.1 Finding: `extra_pat` is unsatisfiable as written

```lean
extra_pat : env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
  ∃ p r m1 m2, Pat p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧ … ∧
    df.rhs.instL ls = r.1.apply m1 m2
```

`VDefEq.WF env df` types `df.lhs` in the **empty context** (`Typing/Basic.lean:75`), so a
rule with parameters must be λ-wrapped — as `quotDefEq` already is
(`vdefeq(α r β f c a => …)` elaborates to `λ α r β f c a. Quot.lift …`). But
`Pattern.Matches` has only `const`/`var`/`app` constructors; it never matches a `lam`.
Hence today `extra_pat` holds only for δ-rules (`VDefVal.toDefEq`, whose `lhs` is a bare
`.const name (params …)`, matched by `SimplePattern.defn`). **This blocks quotients as
much as inductives.**

**Minimal change** (no change to `IsDefEq`, `VDefEq`, or `Pattern.Matches`):

```lean
  extra_pat : env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    ∃ (Δ : List VExpr) (L R : VExpr),
      df.lhs.instL ls = mkLams Δ L ∧ df.rhs.instL ls = mkLams Δ R ∧
      ∃ p r m1 m2, Pat p r ∧ p.Matches L m1 m2 ∧
        r.2.OK (IsDefEqU env univs (Δ.reverse ++ Γ)) m1 m2 ∧ R = r.1.apply m1 m2
```

with `Δ = []` recovering the current statement (so δ-rules are unaffected). The single
consumer is `IsDefEq.church_rosser`'s `extra` case (`ChurchRosser.lean:1383–1386`); the
new proof is

```
df.lhs.instL ls = mkLams Δ L  ≫  mkLams Δ (r.1.apply m1 m2) = mkLams Δ R = df.rhs.instL ls
```

by `|Δ|` nested `ParRed.lam` congruences (with `ParRed.rfl` on the domains) wrapping one
`ParRed.extra`. Still a single parallel step, so `mk h (.tail .rfl _) .rfl (.refl _)`
goes through unchanged.

**Which of the coordinator's two options this is, and what it does to `Theory/Quot.lean`.**
The coordinator framed the choice as "put `VDefEq` in applied form (rule variables as
pattern metavariables rather than lambdas)" vs "extend `Matches` to see through the
abstraction". This is the second, done at the `Params` boundary rather than inside
`Matches`: `Matches` keeps its current inductive shape (so `matches_lift'`,
`matches_instN`, `matches_inter`, `matches_determ` and every `ParRed`/`WHNF` lemma that
consumes them are untouched), and only the *statement of the obligation* changes.
Consequence: **`Theory/Quot.lean` needs no change at all.** `quotDefEq` stays exactly as
the `vdefeq(α r β f c a => …)` elaborator produces it; `extra_pat` for it takes
`Δ = [α, r, β, f, c, a]`, `L = Quot.lift α r β f c (Quot.mk r a)`,
`p = SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3`, and
`R = f a = r.1.apply m1 m2` with `r.1 = RHS.app (var f) (var a)`. That is the encoding
`SimplePattern.iota` was evidently written for, and it now fits.

**Alternative considered and rejected.** Give `VDefEq` a context field and let
`IsDefEq.extra` instantiate it with a substitution — the "applied form" option. It makes
`extra_pat` trivial (no lambda peeling), but it changes the single most load-bearing
definition in the repo: `IsDefEq.extra` acquires a substitution premise, and every
weakening, instantiation and `defeqDFC` lemma in `Lemmas.lean`/`Strong.lean` acquires a
substitution-composition side condition. It also forces `quotDefEq` and the `vdefeq`
elaborator (`Theory/Meta.lean:91–112`, which currently wraps both sides in `fun args* =>`)
to be rewritten, and with them `QuotLemmas.lean`. The λ-peeling route touches one class
field and one proof and leaves `Quot.lean` alone. **Recommendation: λ-peeling.**

### 7.2 Finding: `Pattern` must expose per-`const` universe levels

`Matches.app` (`Pattern.lean:81`) keeps only the head's level list:

```lean
| app : Matches f f' f1 g1 → Matches a a' f2 g2 → Matches (.app f a) (.app f' a') f1 (Sum.elim g1 g2)
```

so for `SimplePattern.iota r m c n` the constructor's levels `ls'` are invisible.
The ι-rule's right-hand side is `Λ.instL ls` (built at the *recursor's* levels, F13), and
`pat_wf` has to bridge `c.{ls'} b` to `c.{ls} b`, which needs `ls ≈ ls'`. That is not
stateable today. Note this bites `quotDefEq` too: `Quot.lift.{u,v}` vs `Quot.mk.{u}`, and
the lists have *different lengths*, so "make `.app` share `f1`" is not a fix.

Making the pattern stricter (requiring `ls' = ls` syntactically) is **unsound for
confluence**: `rec.{max u v} … (c.{max v u} …)` and `rec.{max u v} … (c.{max u v} …)` are
`NormalEq`-related by `constDF`, but only the second would be a redex, so the diamond
fails.

**Minimal change** to `Theory/Typing/Pattern.lean`:

```lean
/-- The `const` leaves of a pattern. -/
def Pattern.LPath : Pattern → Type
  | .const _ => Unit
  | .app f a => f.LPath ⊕ a.LPath
  | .var f   => f.LPath

inductive Pattern.Matches : (p : Pattern) → VExpr → (p.LPath → List VLevel) →
    (p.Path → VExpr) → Prop
  | const : Matches (.const c) (.const c ls) (fun _ => ls) nofun
  | var   : Matches f f' f1 g1 → Matches (.var f) (.app f' a') f1 (·.elim a' g1)
  | app   : Matches f f' f1 g1 → Matches a a' f2 g2 →
            Matches (.app f a) (.app f' a') (Sum.elim f1 f2) (Sum.elim g1 g2)

inductive Pattern.RHS (p : Pattern) where
  | fixed (c : VExpr) (lp : p.LPath) (_ : c.Closed)     -- instantiated at `m1 lp`
  | app (f a : RHS p)
  | var (e : p.Path)

inductive Pattern.Check (p : Pattern) where
  | true
  | defeq (x y : RHS p) (rest : Check p)
  | level (x : p.LPath) (i : Nat) (y : p.LPath) (j : Nat) (rest : Check p)
```

with `Check.OK`'s new clause `((m1 x).getD i .zero ≈ (m1 y).getD j .zero) ∧ rest.OK …`.
Everything else in `Pattern.lean` is a mechanical retype of `m1 : List VLevel` to
`m1 : p.LPath → List VLevel`:

* `Matches.uniq`, `matches_determ`: unchanged proofs, `m1` compared as functions.
* `matches_lift'`, `matches_liftN`, `matches_instN`: `m1` is untouched by lifting and
  instantiation, so unchanged.
* `matches_inter`: the `app`/`var` cases now have to transport an `LPath` along the
  `inter`; a small `LPath.ofInter` coercion is needed. This is the only place with real
  new content (~40 lines).
* `RHS.apply`, `RHS.lift'_apply`, `RHS.liftN_apply`, `RHS.instN_apply`, `Check.OK.map`,
  `Check.OK.weakN`, `Check.OK.instN`: retype only; the new `level` clause is trivially
  stable under weakening/instantiation (it mentions no terms).

Estimated cost: 150–250 lines of edits in `Pattern.lean`, plus retyping `m1` in ~30 call
sites across `ChurchRosser.lean`/`HeadReduction.lean`. Mechanical.

### 7.3 The rules and their side conditions

For `env` built by declarations, define

```lean
def IotaPat (D : VInductDecl) (j q : Nat) (C : VIndCtor) : Pattern :=
  (SimplePattern.iota (mkRecName (D.types.getD j default).name)
     (D.np + D.nm + D.nmin + (D.types.getD j default).indices.length)
     C.name (D.np + C.fields.length)).toPattern
```

so `Matches` on `rec.{ls} a₁…a_M (c.{ls'} b₁…b_N)` binds

* `a₁ … a_np` — parameters, `a_{np+1} … a_{np+nm}` — motives,
  `a_{np+nm+1} … a_{np+nm+nmin}` — minors, then `ni` index arguments;
* `b₁ … b_np` — the constructor's parameters, `b_{np+1} … b_{np+nf}` — its fields.

**Right-hand side** (`r.1`) = `RHS.fixed (D.iotaLam q C) recLeaf _` applied to
`var a₁ … var a_{np+nm+nmin}`, then `var b_{np+1} … var b_{np+nf}` — i.e. exactly F13's
reduct.

**Checks** (`r.2`), in order:

1. `level recLeaf (i+off) ctorLeaf i` for every `i < D.uvars`, where `off = 1` if
   `D.isLE` else `0`. (Bridges `ls'` to the recursor's copy of the block's levels.)
2. `defeq (var b_i) (var a_i)` for `i ≤ D.np`. (The constructor's parameter arguments
   agree with the recursor's.)
3. `defeq (var a_{np+nm+nmin+t}) (RHS for π_t)` for `t ≤ ni`, where the second side is
   `RHS.fixed (mkLams (D.params ++ C.fields.map (·.type)) (C.args[t])) recLeaf _`
   applied to `var a₁ … var a_np, var b_{np+1} … var b_{np+nf}`. (The recursor's index
   arguments agree with the ones the constructor determines.)

Check 3 is the general trick that makes `Pattern.RHS` — which can only build application
spines out of closed constants and matched arguments — expressive enough for arbitrary
index terms: **η-expand the term into a closed λ applied to the matched arguments.**

**`pat_wf` then goes through with no injectivity.** Given
`Γ ⊢ rec.{ls} a (c.{ls'} b) : A` and checks 1–3:

* by 1, `constDF` gives `c.{ls'} ≡ c.{ls-restricted}`; by 2, congruence replaces `b_{≤np}`
  with `a_{≤np}`; by 3, congruence replaces the index arguments with `π[a,b]`;
* `IsDefEq.extra` on `D.iotaRule j q C` at `ls`, followed by `appDF` with
  `a₁ … a_{np+nm+nmin}, b_{np+1} … b_{np+nf}` and `|Γ'|` `beta` steps, yields
  `rec.{ls} a_P a_M a_E π[a,b] (c.{ls} a_P b_Φ) ≡ Λ.instL ls a_P a_M a_E b_Φ`;
* chain.

Contrast: without the checks, each of the three bridges needs
`I p ι ≡ I p' ι' → ls ≈ ls' ∧ p ≡ p' ∧ ι ≡ ι'`, i.e. **rigid-head application
injectivity**, which is downstream of Church–Rosser, which is downstream of `Params`.
**The `Check` mechanism is what breaks that circle**, and this design would not work
without it.

Precision about what *is* available inside a `Params` instance, since it matters twice
more in §7.6: `ChurchRosser.lean` imports `UniqueTyping`, which imports `Injectivity`.
So `IsDefEqU.sort_inv`, `IsDefEqU.forallE_inv`, `IsDefEqU.sort_forallE_inv` and
`IsDefEq.uniq`/`uniqU` **may be used when discharging `Params`'s fields** — they are
`sorry`-backed and are the injectivity stream's problem, but they are not circular with
`Params`. What is *not* available is anything proved from `Params`: Church–Rosser,
`NormalEq`, head reduction, and hence rigid-head application injectivity.

### 7.4 `extra_pat` for the ι-rules

With §7.1's shape and `Δ = D.iotaCtx C`:

* `df.lhs.instL ls = mkLams Δ' (D.iotaLhs j C).instL ls` — and `iotaLhs` is literally a
  pattern instance, with `m2` sending every path to a `bvar`, `m1 recLeaf = ls`,
  `m1 ctorLeaf = D.selfLvls.map (·.inst ls)`.
* Check 1 becomes `ls.getD (i+off) ≈ (D.selfLvls.map (·.inst ls)).getD i` = reflexivity.
* Check 2 becomes `bvar k ≡ bvar k` (needs a type witness: available from the
  well-typedness of `df.lhs`, i.e. from `Ordered.defEqWF`).
* Check 3 becomes `π_t ≡ (λ P Φ. π_t) P Φ`, i.e. `|D.params| + nf` β-steps.
* `R = r.1.apply m1 m2` **holds definitionally** because `iotaRule.rhs`'s body was
  *chosen* to be `Λ` applied to the binders (§5.4).

### 7.5 The orthogonality axioms

Verified case-by-case against `Pattern.inter` (`Pattern.lean:54`). Let

```lean
Pat p r := (∃ df, env.defeqs df ∧ IsDeltaRule df p r) ∨ (∃ df, env.defeqs df ∧ IsIotaRule df p r)
```

read off `env.defeqs`, and let `N_def`, `N_ind`, `N_ctor`, `N_rec` be the sets of names
carrying δ-rules / declared as inductive types / constructors / recursors.

* `pat_simple` — by construction (`SimplePattern.defn` / `.iota`). ✓
* `pat_app_l` — the left spine of an ι-pattern is `.varN (.const r) m`, which contains no
  `.app` node. ✓ **This is exactly why `SimplePattern.iota` uses `varN`.**
* `pat_app_l_uniq` — reduces to: for a fixed recursor name `r`, all ι-patterns with head
  `r` have the *same* major-premise position `m`. True, because
  `m = np + nm + nmin + ni_j` depends only on `r` (and *this is why the indices must
  appear in the ι-rule's LHS at all*, even though F13 discards them). Different `j` give
  different recursor names. ✓
* `pat_app_uniq` — reduces to `r ≠ c'` for a recursor name `r` and a constructor name
  `c'` (the two spine heads); then `inter` bottoms out at `.const r` vs `.const c'` or at
  `.const` vs `.var`, both `none`. ✓
* `pat_uniq` — needs: (i) `.const c'` never overlaps an ι-pattern's proper sub-patterns
  (`inter` of `const` with `app`/`var` is `none`, and a var-prefix `varN (.const r) k`
  with `k ≤ m` never inters with the full `varN (.const r) m` because the chain lengths
  differ); (ii) two ι-patterns overlap only if `(r,m,c,n)` coincide, and then the rules
  must coincide; (iii) two δ-patterns overlap only if the names coincide, and then the
  rules must coincide. ✓ given

  **(D)** `N_def`, `N_ind`, `N_ctor`, `N_rec` are pairwise disjoint, each name carries at
  most one rule, and each recursor name determines its `(np, nm, nmin, ni)`.

  (D) follows from `addConst` failing on duplicates, but it is *not currently expressible*:
  `VEnv` has only `constants` and `defeqs`, with no record of which kind of object a name
  is. See §8, item I1.

### 7.6 The two additional axioms: major-premise rigidity and small elimination

The `ChurchRosser` stream reports that `NormalEq.parRed`'s `appDF` × `extra` case needs
two further `Params` fields. Both are facts about the *major premise* of an ι-redex, i.e.
about the right spine `p₂ = .varN (.const c) n` of `SimplePattern.iota`. Here is what an
`addInduct` environment does and does not deliver.

Preliminary, needed by both. For an ι-pattern, `n = D.np + C.fields.length` is *exactly*
the constructor's arity, because `C.type D j = mkPi (C.params ++ C.fields.map (·.type))
(C.canonResult D j)` has exactly that many binders (§3, and it is not accidental: F2
guarantees the stored type is that pi-telescope on the nose). Hence:

> **Lemma M1 (major typing).** If `p₂.Matches e₂ m1₂ m2₂` for the ι-pattern of
> `(D, j, C)` and `Γ ⊢ e₂ : T₂`, then `T₂ ≡ (C.canonResult D j)` instantiated at the
> matched levels and arguments, i.e. `T₂ ≡ I_j.{ls'} b₁…b_np π[b]`.
>
> Proof: `n` iterated `HasType.app_inv`, `IsDefEq.uniq` and `IsDefEqU.forallE_inv` — all
> available (§7.3). Difficulty: medium (~200 lines); it is the standard "saturated
> application of a constant has the constant's result type" argument, and it is worth
> proving once for a general `mkPi`/`mkApp` pair (lemma B7 below) rather than for
> constructors specifically.

#### `pat_major_not_pi` — satisfied, modulo one new rigidity lemma

```lean
pat_major_not_pi : Pat p r → Subpattern (.app p₁ p₂) p → p₂.Matches e m1 m2 →
  HasType env univs Γ e T → ¬ IsDefEqU env univs Γ T (.forallE A B)
```

By M1, `T ≡ I_j.{ls'} p π`, an application of an *inductive type constant*. What
`addInduct` supplies is exactly the missing side condition:

> **Lemma M2 (inductive heads are rule-free).** In an environment built by declarations,
> if `I_j` is one of `D.blockNames` for some declared `D`, then no `df ∈ env.defeqs` has
> a `Pattern` whose head constant is `I_j`.
>
> Proof: the `VEnv.Sig` invariant of §7.7. Every defeq is a δ-rule of a `def`, an ι-rule
> of a `rec`, or `quotDefEq`; `addConst`'s freshness makes `N_ind`, `N_def`, `N_rec`,
> `N_ctor` pairwise disjoint. Difficulty: easy given `Sig` (I1).

The remaining step is a genuine *rigidity* statement of exactly the class of
`IsDefEqU.sort_forallE_inv`:

```lean
theorem IsDefEqU.const_forallE_inv (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hrigid : RuleFreeHead env c) :
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp args) (.forallE A B)
```

It cannot be proved from `Params` (circular) and it cannot be proved by the `Check`
trick (there is no rule firing here to attach a side condition to). It belongs to the
**injectivity work stream**, and it fits there naturally: `Experimental/ShapeLogRel.lean`
already has `Shape.ctor' (c : Name) (l : List (Shape n))` as a shape constructor distinct
from the sort and function shapes (line 817), which is precisely the head-shape
classification `const_forallE_inv` needs. Recommendation: add `const_forallE_inv` to
`Theory/Typing/Injectivity.lean` alongside the existing three, and pick it up in the same
`SExpr`-bridge that delivers `sort_forallE_inv`.

Note this axiom is *also* required by the quotient rule (`Quot.mk r a : Quot α r`, and
`Quot` is a primitive constant with no rules), so it is not inductive-specific and should
not be paid for by this design.

**Verdict: the spec records enough. `addInduct` gives M1 + M2; one new injectivity-class
lemma closes it.**

#### `pat_major_prop` — false as proposed; here is the corrected split

```lean
pat_major_prop : … HasType Γ T₂ (.sort .zero) → HasType Γ T (.sort .zero)
```

For an ι-rule of `I_j.rec`, `T₂ = I_j p ι` and `T = M_j ι z` where the motive is
`M_j : ∀ ι, I_j p ι → Sort (D.elimLvl.inst ls)`. So the conclusion asks for
`D.elimLvl.inst ls ≈ .zero`. Splitting on `D.isLE`:

* **`isLE = false`** — `D.elimLvl = .zero` by definition (§2.3), so `T : Sort .zero`
  outright. **Holds, one line.** This is Carneiro's "it is a small eliminator".
* **`isLE = true`** — `D.elimLvl = .param 0` and `ls.head` is arbitrary. `Eq` and `Acc`
  are the standard witnesses: `Eq α a b : Prop` but `Eq.rec C h a e : C b e : Sort v`.
  **The axiom is false.**

So the axiom must be stated conditionally. `addInduct` can supply the guard, because
`isLE` is recorded in the declaration and `VEnv.Sig` maps the recursor name to its
declaration:

```lean
  /-- A rule whose eliminator is small: its motive lands in `Prop`. -/
  pat_small : (p : Pattern) → Prop
  pat_major_prop : Pat p r → pat_small p → Subpattern (.app p₁ p₂) p →
    p₂.Matches e₂ m1₂ m2₂ → HasType env univs Γ e₂ T₂ → HasType env univs Γ T₂ (.sort .zero) →
    p.Matches e m1 m2 → HasType env univs Γ e T → HasType env univs Γ T (.sort .zero)
```

with `pat_small (IotaPat D j q C) := D.isLE = false` (and `pat_small` false for
`quotDefEq`, whose `Quot.lift` is a large eliminator, and vacuously true/irrelevant for
δ-rules, which have no major premise). Proof for the ι case: by M1 and the recursor's
type (`recType_isType`, lemma D6), `T ≡ M_j ι z` and `Γ ⊢ M_j ι z : .sort .zero` because
`D.elimLvl.inst ls = .zero`. **Difficulty: easy given D6.**

#### What replaces it in the large-eliminating case

The `¬pat_small` case is exactly the situation Carneiro analyses in `typesys.tex:6–48`:
the `Acc`/`Eq` "creative step". The fact that saves it is not that the redex is a proof
but that the major premise's *type is a subsingleton*, so a stuck major can be rewritten
into a constructor application and the stuck side becomes a redex too. This is what
`LECond` (§4.3) was designed to deliver, and it is stateable and provable from
`addInduct`:

> **Lemma M3 (canonicity for subsingleton eliminators).** Let `D.isLE = true` and
> `D.lvl.inst ls ≈ .zero`. By `LECond` (the first disjunct `IsNeverZero` is excluded by
> the hypothesis, using `VLevel.IsNeverZero`'s definition), `D.types = [T]` and
> `T.ctors` is `[]` or `[C]`.
> * `T.ctors = []`: there is no ι-rule for this block, so no redex; nothing to prove.
> * `T.ctors = [C]`: for every `Γ ⊢ h : I.{ls} p ι` there is a field vector `φ` with
>   `Γ ⊢ h ≡ C.{ls} p φ : I.{ls} p ι` and `Γ ⊢ ι_t ≡ args_t[p, φ]`.
>
> Construction of `φ`, by `LECond`'s clause on field `k`:
> * `F.lvl ≈ .zero` (a proof field): the field's type `A_k` is a `Prop`, so **any**
>   inhabitant will do and the two candidates are `≡` by `proofIrrel`. An inhabitant is
>   produced by `I.rec` with the small motive `fun ι x => A_k` (well-typed because
>   `A_k : Prop`, so the motive lands in `Prop`, which every recursor allows), the single
>   minor `fun Φ V => Φ_k`, and major `h`. When `A_k` depends on earlier fields, build
>   the fields left to right, substituting the ones already built.
> * `.bvar (nf-1-k) ∈ C.args` (an index-determined field): take `φ_k := ι_t` for the
>   position `t` where it occurs. This is where the syntactic form of `LECond` pays off:
>   the field *is* one of the index arguments, so no construction is needed.
> * A recursive field is covered by the first clause when the block's level is `0`: its
>   type `∀ξ. I p π` is a `Prop` (`imax _ 0 ≈ 0`), so it is a proof field. This is
>   exactly Carneiro's `inv_x : Acc x → ∀ y, y < x → Acc y` (`typesys.tex:11`), built by
>   `Acc.rec`.
>
> `h ≡ C p φ` then follows from `proofIrrel` on `I.{ls} p ι : Sort 0`, and the index
> equations from `uniq` + M1. **Difficulty: hard (~400 lines), but it is content the
> declaration already contains** — no new field in `VInductDecl` is needed.

How M3 should be exposed to `Params` is the coordinator's call, since I do not have the
`NormalEq.parRed` proof context. Two shapes that both follow from M3:

```lean
  /-- Large-eliminating `Prop` blocks: every major premise is defeq to one that matches. -/
  pat_major_canonical : Pat p r → ¬pat_small p → Subpattern (.app p₁ p₂) p →
    p₂.Matches e₂ m1₂ m2₂ → HasType env univs Γ e₂ T₂ → HasType env univs Γ T₂ (.sort .zero) →
    ∀ h, HasType env univs Γ h T₂ →
      ∃ e₂' m1' m2', p₂.Matches e₂' m1' m2' ∧ IsDefEqU env univs Γ h e₂'
```

("the stuck side can be turned into a redex"), or the weaker

```lean
  pat_major_subsingleton : … → ∀ h h', HasType Γ h T₂ → HasType Γ h' T₂ →
    ∃ e₂' m1' m2', p₂.Matches e₂' m1' m2' ∧ IsDefEqU Γ h e₂' ∧ IsDefEqU Γ h' e₂'
```

Two warnings about this corner, both worth confirming before the shape is fixed:

1. **`toCtorWhenK` in the checker is strictly weaker than M3.** The kernel only performs
   the K-expansion when `isKTarget` holds — single type, `isAlwaysZero` level, single
   constructor **with no fields** (F15). `Acc` fails that (its constructor has fields),
   so `Acc.rec C f x h` really is a whnf normal form for the checker while
   `Acc.rec C f x (Acc.intro x g)` reduces. If `ParRed` is given a `pat_major_canonical`
   step, the abstract reduction relation becomes strictly stronger than the checker's,
   which is sound (the checker only has to be *below* `≡`) but means
   `reduceRecursor.WF` cannot be read off the ParRed development mechanically.
2. **This is precisely where Carneiro says the theory is undecidable** (`typesys.tex:19–48`).
   Any statement of confluence that is strong enough to close this case must be a
   statement about `≡`, not about a terminating rewrite system. If `NormalEq.parRed`'s
   `proofIrrel` case is being asked to produce a *common reduct*, it may be the statement
   rather than the axiom that needs adjusting — e.g. by allowing `NormalEq` a
   proof-irrelevance closure at the major-premise position.

**Verdict: `pat_major_prop` needs the `pat_small` guard; with it, `addInduct` establishes
it in one line. The large-eliminating case needs M3 instead, which `LECond` makes
provable but which is a substantial lemma and interacts with a known incompleteness of
the theory.**

### 7.7 What `Params` still needs from the environment: `VEnv.Sig`

To define `Pat` and prove (D), the `Params` instance must be built by induction over
`VEnv.WF' ds env`, carrying a *signature invariant*:

```lean
inductive ObjKind where
  | «def» (df : VDefEq)                     -- δ-rule
  | ind (D : VInductDecl) (j : Nat)
  | ctor (D : VInductDecl) (j q : Nat) (C : VIndCtor)
  | «rec» (D : VInductDecl) (j : Nat)
  | prim                                    -- axioms, opaques, Quot.*

structure VEnv.Sig (env : VEnv) where
  kind    : Name → Option ObjKind
  /-- every constant has a kind, matching its type -/
  sound   : env.constants n = some ci → ∃ k, kind n = some k ∧ KindMatches env n k ci
  /-- every defeq is either a δ-rule of a `def`, an ι-rule of a `rec`, or the quot rule -/
  defeqs  : env.defeqs df → IsDeltaOf env kind df ∨ IsIotaOf env kind df ∨ df = quotDefEq
  /-- names are used at most once, and the block a ctor/rec belongs to is the one the
  corresponding `ind` entry names -/
  coherent : …

theorem VEnv.WF.sig : env.WF → Nonempty env.Sig
```

This is the single biggest *unanticipated* prerequisite of the `Params` instance:
roughly 600–1200 lines, mostly bookkeeping over `VEnv.WF'`. It is however completely
independent of the inductive spec's content, and it is also what
`Verify/`'s `IsStructure` (§6.2) and `TrProj.uniq` want.

---

## 8. `addInduct_WF`: proof sketch and dependency-ordered lemma list

`Theory/Typing/InductiveLemmas.lean`:

```lean
theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct env decl = some env') : Ordered env'
```

Structure, in four stages mirroring §5.5, following `addQuot_WF`'s `with_addConst`
pattern:

1. `Ordered env₁` from `addIndTypes`: needs `VConstant.WF env (⟨D.uvars, T.type⟩)`, i.e.
   `T.WF.isType`, plus monotonicity as earlier types accumulate. **Easy.**
2. `Ordered env₂` from `addIndCtors`: needs `IsType env₁ D.uvars [] (C.type D j)`.
   Derived from `VIndCtor.WF` by `IsType.forallE` chaining over `C.params ++ fields`,
   with `IsDefEqCtx`-transport (`IsDefEq.defeqDFC`) to move from the block's parameter
   context to the constructor's. **Medium** (~200 lines).
3. `Ordered env₃` from `addIndRecs`: needs
   `IsType env₂ D.recUvars [] (D.recType j)`. **Hard, ~600–900 lines.** Sub-steps:
   * `params` and `T.indices` are `IsType` in `env₂` (monotonicity from `env`);
   * `motiveType_isType`: needs `Γ ⊢ I_t.{selfLvls} p ι : Sort D.lvl`, which comes from
     `HasType.const` at the recorded `T.type`, then `defeqDF` along `T.WF.canon`, then
     `|D.np| + ni` applications;
   * `minorType_isType`: same, plus the IH telescope, plus
     `Γ ⊢ c.{selfLvls} p Φ : I_t p args` from `VIndCtor.WF.result` and `addConst_self`;
   * `recType_isType`: `IsType.forallE` chaining.
4. `Ordered env'` from `addIndRules`: needs `VDefEq.WF env₃ (D.iotaRule j q C)`, i.e.
   both sides typed at `mkPi Γ' (D.iotaType j C)` in `[]`. **Hardest, ~800–1200 lines.**
   * LHS: apply `rec_j`'s type to `P, M, E, args, c P Φ` — each application step needs a
     `B.inst a = B'` computation (lemma B4 below);
   * RHS: `Λ : mkPi Γ' (iotaType)` needs `E_q Φ V : M_t args (c P Φ)`, which needs each
     `V_i : ∀ξ. M_{r.idx} π (Φ_i x)`, which needs `Φ_i x : I_{r.idx} p π` from the
     recursive field's `IsDefEqU` in `VIndField.WF.pos`, then `rec_{r.idx}` applied.
     Then η-expand.

### Lemma list, in dependency order

| id | statement | difficulty | est. |
|---|---|---|---|
| **A. telescope arithmetic** (`Theory/VExpr.lean`) | | | |
| A1 | `mkPi`/`mkLams`/`mkApp`/`bvars`/`liftTele`/`shift` defs + `append`/`length` simp set | trivial | 80 |
| A2 | `liftN` / `instN` / `instL` commute with `mkPi`, `mkLams`, `mkApp` | easy, tedious | 200 |
| A3 | `(mkPi As B).inst a k = mkPi (As.inst …) (B.inst a (k + |As|))` and friends | easy, tedious | 150 |
| A4 | `shift`/`shiftTele` composition and `liftN'_comm` normalisation | medium (arith) | 200 |
| A5 | `ClosedN (mkPi As B) k ↔ …`, `Closed (iotaLam …)` | easy | 80 |
| **B. telescope typing** (`Theory/Typing/Lemmas.lean`) | | | |
| B1 | `OnCtx (As.reverse ++ Γ)` introduction/elimination; `OnCtx.append` | easy | 60 |
| B2 | `IsType.mkPi : OnCtx (As.reverse ++ Γ) … → IsType (As.reverse ++ Γ) B → IsType Γ (mkPi As B)` | easy | 60 |
| B3 | `HasType.mkLams` | easy | 40 |
| B4 | **key**: `Γ₀ ⊢ f : mkPi As B` → `As.reverse ++ Γ₀ ⊢ (f.liftN \|As\|) .mkApp (bvars 0 \|As\|) : B`. Induction using `instN_bvar0` (`VExpr.lean:502`). | **medium** — this is the workhorse | 150 |
| B5 | `HasType.mkApp` with an explicit list of instantiations | medium | 120 |
| B6 | weakening of a whole telescope: `Ctx.LiftN` for `liftTele` | medium | 120 |
| B7 | **saturated application**: `Γ ⊢ f : mkPi As B` (with `\|as\| = \|As\|`) → `Γ ⊢ f.mkApp as : B` instantiated by `as`; and its inverse (`Γ ⊢ f.mkApp as : T` → `T ≡ B[as]`) via `forallE_inv` + `uniq`. Consumed by M1. | medium | 250 |
| **C. staged environments** | | | |
| C1 | `addIndTypes_le`, `addIndCtors_le`, `addIndRecs_le`, `addIndRules_le` | trivial | 40 |
| C2 | `addIndTypes_ordered` etc. (generalise `addConsts_ordered` from `List VDefVal` to `List (Name × VConstant)`) | easy | 80 |
| C3 | `addInduct_constants_*`: the block's constants are present with the stated types (via `HasObjects.bind_const`) | easy | 120 |
| C4 | `addInduct_defeqs`: every `D.iotaRules` member is in `env'.defeqs` | easy | 40 |
| **D. recursor well-formedness** | | | |
| D1 | `tyApp_hasType`: `Γ ⊢ I_t.{ls} p ι : .sort (D.lvl.inst ls)` | medium | 150 |
| D2 | `ctorApp_hasType`: `Γ ⊢ c.{ls} p Φ : I_t p args` | medium | 200 |
| D3 | `motiveType_isType` | medium | 150 |
| D4 | `ihTypes_isType` | hard (arith) | 250 |
| D5 | `minorType_isType` | hard | 300 |
| D6 | `recType_isType` | medium given D3–D5 | 150 |
| **E. ι-rule well-formedness** | | | |
| E1 | `recApp_hasType`: the recursor applied to `P M E ι z` has type `M_j ι z` | hard (arith) | 300 |
| E2 | `ihValues_hasType` | hard | 300 |
| E3 | `iotaLam_hasType` : `[] ⊢ iotaLam : mkPi Γ' (iotaType)` | hard | 250 |
| E4 | `iotaLhs_hasType` | hard | 250 |
| E5 | `iotaRule_WF : VDefEq.WF env₃ (D.iotaRule j q C)` | easy given E3/E4 | 60 |
| **F.** | `addInduct_WF` | easy given C–E | 80 |
| **G. accessors, for `Verify/`** | | | |
| G1 | `VEnv.HasInduct env D` (all constants + defeqs present), and `addInduct_hasInduct` | easy | 100 |
| G2 | `HasInduct.mono` | trivial | 20 |
| G3 | `IsStructure` and its accessors | easy | 80 |
| G4 | `HasInduct` uniqueness: a name belongs to at most one block (needs `VEnv.Sig`) | medium | 150 |
| **H. `Pattern.lean` generalisation** (§7.2) | | | |
| H1 | `LPath`, retyped `Matches`, `RHS.fixed` with an `LPath`, `Check.level` | easy | 120 |
| H2 | retype `uniq`/`determ`/`lift'`/`instN`/`OK.map`/`weakN`/`instN` | easy, tedious | 150 |
| H3 | `matches_inter` with `LPath` transport | medium | 100 |
| H4 | retype ~30 call sites in `ChurchRosser`/`HeadReduction` | easy, tedious | 100 |
| **I. `Params` instance** | | | |
| I1 | `VEnv.Sig` + `VEnv.WF.sig` (§7.7) | **hard, unanticipated** | 600–1200 |
| I2 | `IsDeltaRule` / `IsIotaRule` relations and `Pat` | easy | 100 |
| I3 | `pat_simple` | trivial | 20 |
| I4 | `pat_app_l` | easy | 40 |
| I5 | `pat_app_l_uniq`, `pat_app_uniq` | medium (given I1) | 200 |
| I6 | `pat_uniq` | medium (given I1) | 250 |
| I7 | `extra_pat` for δ-rules and `quotDefEq` | easy | 100 |
| I8 | `extra_pat` for ι-rules (§7.4) | medium | 250 |
| I9 | `pat_wf` for ι-rules (§7.3) | **hard** | 400 |
| I10 | `Params.extra_pat` restatement + fix `church_rosser`'s `extra` case (§7.1) | medium | 80 |
| I11 | M1 (major typing), from B7 | medium | 200 |
| I12 | M2 (inductive heads are rule-free), from I1 | easy | 80 |
| I13 | `IsDefEqU.const_forallE_inv` — **disjointness only**; now stated in `Injectivity.lean`. See I13a/I13b: this row does *not* cover what five consumers outside this design need | **research** | ? |
| I13a | `IsDefEqU.const_app_inv` — **injectivity**, same head, needing **two** side conditions (`RuleFreeHead` *and* the application being a type); stated in `Injectivity.lean`, witnesses in `Theory/Typing/ConstInvWitness.lean` | **research** | ? |
| I13b | **rigidity** — a term defeq to a const application reduces to one. Needed by `TrProj.weak'_inv`; deliberately not stated in `Injectivity.lean` because its faithful form mentions weak-head reduction | **research** | ? |
| I14 | `pat_major_not_pi` from M1 + M2 + I13 | easy | 60 |
| I15 | `pat_small` for ι- and δ-patterns; `pat_major_prop` in the small case (§7.6) | easy given D6 | 100 |
| I16 | M3 (canonicity for subsingleton eliminators) and `pat_major_canonical` (§7.6) | **hard** | 400 |
| **J. structure eta** (§6.3) | | | |
| J1 | `IsDefEq.structEta` + the case in every `IsDefEq` induction | medium, broad | 400 |
| J2 | `NormalEq.structEtaL/R` + `ChurchRosser` cases | hard | 400 |
| **K. `Verify/` side** (§9) | | | |
| K1 | `TrProj` definition, `weak'`, `instN`, `instL`, `wf`, `uniq`, `defeqDFC` | medium | 500 |
| K2 | `AddInduct` constructors + `to_addInduct` | easy | 150 |
| K3 | `addInductive.WF` (the big refinement) | **hardest** | 2000+ |
| K4 | `reduceRecursor.WF` (ι + K) | medium given I9 | 400 |
| K5 | `reduceProjCore.WF`, `inferProj.WF` | medium | 400 |
| K6 | `tryEtaStructCore.WF`, `isDefEqUnitLike.WF` | medium given J1 | 300 |

Rough total for the `Theory/` half (A–J): 8–10k lines. `Verify/` (K): another 4k.

**Things that look hard and are worth pricing before starting.**

* **I1 (`VEnv.Sig`)** is the surprise. Nothing in `Theory/` currently records object
  kinds, and `Params` cannot be instantiated without it.
* **I9 (`pat_wf`)** is where the design's `Check` idea earns its keep; if the `Check`
  route were abandoned, I9 becomes unprovable before Church–Rosser.
* **I13** is the only item in the whole list that this design cannot see a route to. It
  is not inductive-specific (the quotient rule needs it too) and it should be routed to
  the injectivity stream.

  **Corrected after `docs/research-const-inv.md`.** Three things were being called I13, and
  only the first is what this row states:

  * **I13 (A) disjointness** — `const-app ≢ Π`. What `pat_major_not_pi` (I14) consumes, and
    the only one this design needs.
  * **I13a (B) injectivity** — what `reduceRecursor.WF`'s quotient branch, its `Quot.ind`
    arm, `TrProj.uniq` and `TrProj.defeqDFC` need. **Requires a second side condition this
    row never had**: the application must be a type. Without it `proofIrrel` identifies any
    two applications landing in a proposition, with no reduction and no rule in the
    environment — so `RuleFreeHead` does not repair it. Machine-checked as `w2` in
    `Theory/Typing/ConstInvWitness.lean`.
  * **I13b (C) rigidity** — what `TrProj.weak'_inv` needs. Not the same statement as either.

  The recommendation below to pick this up in the `SExpr` bridge is **withdrawn**: the shape
  lattice's `indTy` carries a `Bool` and no arguments (`ShapeLogRel.lean:360`), so the model
  cannot distinguish `Quot α r` from `Quot α' r'`. `Shape.ctor'` is fine-grained but applies
  to *constructor* applications, not type formers. Church–Rosser is the route, and it is no
  longer circular now that `forallE_inv` arrives independently — see
  `docs/research-const-inv.md` §4–5.
* **I16** touches the one place where Lean's theory is genuinely non-confluent as a
  rewrite system (`typesys.tex:19–48`); expect the *statement* to move, not just the
  proof.
* **D4/D5/E1–E4**: nothing conceptually hard, but the de Bruijn arithmetic dominates.
  Invest in A2–A4 and B4–B6 as a *library* first; the ratio of arithmetic lemmas to
  content lemmas is about 3:1, and doing it ad hoc will triple the cost. The existing
  `type_tac` (`Theory/Typing/Meta.lean:37`) handles closed, concrete types; it will not
  handle these, but a telescope-aware successor built on B4/B5 would.
* **J2**: adding a `NormalEq` constructor means revisiting the diamond argument in
  `ChurchRosser.lean`; the existing `etaL/etaR` cases are the template but they are the
  fiddliest part of that file.

---

## 9. The `Verify/` side

### 9.1 `AddInduct`

`Verify/Environment/Basic.lean:106` currently has no constructors. It should get exactly
one, packaging the translation of the block:

```lean
structure TrIndBlock (safety : DefinitionSafety) (env env' : VEnv) (D : VInductDecl)
    (m₁ m₂ : ConstMap) : Prop where
  fresh  : ∀ n ∈ D.allNames, m₁.find? n = none
  nodup  : D.allNames.Nodup
  /-- the map is extended by exactly the block's declarations -/
  map    : m₂ = insertBlock m₁ D             -- a concrete `ConstMap` function
  types  : ∀ j T, D.types[j]? = some T → ∃ iv,
    m₂.find? T.name = some (.inductInfo iv) ∧
    TrConstant safety env (.inductInfo iv) ⟨D.uvars, T.type⟩ ∧
    iv.numParams = D.np ∧ iv.numIndices = T.indices.length ∧
    iv.ctors = T.ctors.map (·.name) ∧ iv.all = D.types.map (·.name) ∧ iv.numNested = 0
  ctors  : ∀ j T C q, D.types[j]? = some T → T.ctors[?] = some C → ∃ cv,
    m₂.find? C.name = some (.ctorInfo cv) ∧
    TrConstant safety env₁ (.ctorInfo cv) ⟨D.uvars, C.type D j⟩ ∧
    cv.induct = T.name ∧ cv.numParams = D.np ∧ cv.numFields = C.fields.length ∧ cv.cidx = _
  recs   : ∀ j T, D.types[j]? = some T → ∃ rv,
    m₂.find? (mkRecName T.name) = some (.recInfo rv) ∧
    TrConstant safety env₂ (.recInfo rv) ⟨D.recUvars, D.recType j⟩ ∧
    rv.numParams = D.np ∧ rv.numIndices = T.indices.length ∧
    rv.numMotives = D.nm ∧ rv.numMinors = D.nmin ∧
    rv.k = decide (KCond D) ∧
    List.Forall₂ (fun (rule : RecursorRule) (qC : Nat × VIndCtor) =>
        rule.ctor = qC.2.name ∧ rule.nfields = qC.2.fields.length ∧
        TrExprS env₂ rv.levelParams [] rule.rhs (D.iotaLam qC.1 qC.2))
      rv.rules (relevant slice of D.ctorsAll)

inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (D : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop
  | mk : TrIndBlock safety env₁ env₂ D m₁ m₂ → env₁.addInduct D = some env₂ → AddInduct …
```

`to_addInduct` is then the second projection instead of `nomatch`. Once this has a
constructor, `TrEnv'.no_inductInfo` disappears and `checkEqType.WF`/`addQuot.WF`
(`Verify/Environment.lean:114,134`) stop being vacuous — they will need real proofs,
which is the intended consequence.

### 9.2 What `Lean4Lean/Inductive/Add.lean` must be shown to satisfy

```lean
theorem addInductive.WF {ves : VEnvs} (wf : ves.WF env) (lparams nparams types isUnsafe allow) :
    (Environment.addInductive env lparams nparams types isUnsafe allow fuel).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
```

with the interesting case producing, for each safety level, a `D : VInductDecl` and an
`AddInduct`. The obligations, mapped to the code:

| kernel function | obligation |
|---|---|
| `checkInductiveTypes` | its `stats` yields `D.params`, `T.indices`, `D.lvl`; the whnf chain gives `T.WF.canon` (from `whnf.WF`'s `IsDefEqU` + `forallEDF` chaining), and the `isDefEq dom (getType param)` calls give `VIndType`'s parameter defeqs |
| `checkConstructors` | `VIndCtor.WF`: `params_eq` from the `isDefEq` calls; `fields` from `ensureType`/`checkPositivity`/`isRecArg`; `args_len`/`args_fresh`/`result` from `isValidIndAppIdx` |
| `checkPositivity`, `isRecArg` | `VIndField.WF.pos` — these two must be shown to *agree* on the telescope they walk (they whnf the same terms), and the classification `F.rec := if (isRecArg dom).isSome then …` |
| `isLargeEliminator` | `D.isLE = true → D.LECond` (only this direction) |
| `getElimLevel` | `D.elimLvl`, `D.recUvars`; `getRecLevelParams` must produce `u :: lparams` with `u ∉ lparams` (the `loop` at `Add.lean:284` guarantees freshness) |
| `mkRecInfos`, `mkRecRules` | `TrExprS` of the produced `type`/`rhs` against `D.recType j` / `D.iotaLam q C`. This is the bulk of K3: it is a statement that two independently-written de Bruijn constructions coincide, one via `LocalContext.mkForall` over fvars and one via `mkPi` over indices. A `TrExprS`-for-`mkForall` bridge lemma (relating `lctx.mkForall xs e` to `mkPi` under `VLCtx` translation) is the key reusable piece, and `Verify/LocalContext.lean` already has most of the machinery |
| `declareInductiveTypes`, `declareConstructors` | the `ConstMap` bookkeeping in `TrIndBlock.map` |

Three implementation-side prerequisites, all currently `partial` (they are on
`Guard.lean`'s allowlist, `Verify/Guard.lean:87–105`): every `AddInductive.*.loop` must
be given a fuel or well-founded measure before it can be reasoned about. Shrinking that
allowlist is listed as progress in `CLAUDE.md`, so this is aligned.

### 9.3 Nested inductives — the spec *does* have to know

`ElimNestedInductive` runs first and produces a plain block, so `AddInductive.run`'s
output is covered by §5. But `Environment.addInductive` does not stop there
(`Add.lean:747–776`): when `numNested ≠ 0` it *rebuilds* the environment from `env`,
adding `restoreNested`-rewritten types for every constructor and recursor and
`restoreNested`-rewritten `rhs` for every rule, plus the auxiliary recursors under
renamed names (`mkAuxRecNameMap`). The constants that end up in the final environment
have types mentioning `List (Tree α)`, whereas the auxiliary block declared
`_nested.List_1 α`; those two constants are **not** definitionally equal, so the final
environment is not `addInduct env D` for any `D` in the sense of §5. Requirement 4's
question therefore answers **yes**.

Recommended generalisation (scope it as a follow-on, not part of Phase B):

* Let `VIndType` optionally be a **companion**: instead of declaring a fresh constant, it
  names an already-declared inductive `J` together with a parameter instantiation
  `A(params)` (which may mention the block's own types). Its "constructors" are `J`'s
  existing constructors with `A` substituted; only a *new recursor* and its ι-rules are
  added.
* `tyApp` for a companion becomes `J.{ls} A(params) ι` instead of `.const I_j ownLvls …`.
* Positivity generalises to: a field is either block-free, or `∀ξ. H_k params π` where
  `H_k` ranges over the block's types *and companions*.
* Then the restored block is exactly a companion block, `restoreNested` is the map from
  the auxiliary block to it, and `mkAuxRecNameMap` supplies the companion recursor names.
* Model side: the simultaneous least fixed point of the combined operator on
  `(T, X)` has `X = J(T*)` by Bekič's rule, which is what justifies identifying the
  companion with `J` applied to the finished `T*`.

Nothing in the *non-nested* design of §2–§5 has to change to accommodate this later; the
generalisation is orthogonal (it replaces `.const I_j ownLvls` by a general head term).

---

## 10. Model adequacy (requirement 7)

The spec is stated so that the intended ZFC construction reads off directly. For a fixed
valuation of the universe parameters, in `V_κ` with `κ` inaccessible:

* Interpret the parameter telescope as an iterated dependent product; fix `p`.
* The operator: for a family `X = (X_0,…,X_{nm-1})` with `X_t ⊆ ⟦Idx_t⟧ → V_κ`, put

  `Φ(X)_t(ι) = { (q, φ) : (t,C) is the q-th ctor, φ ∈ ⟦fields_C⟧_X, ⟦args_C⟧(φ) = ι }`

  where `⟦fields_C⟧_X` interprets a non-recursive field by its (X-independent, by
  `pos.none`) type and a recursive field `⟨ξ,i,π⟩` by `Π x ∈ ⟦ξ⟧. X_i(⟦π⟧)`.
* Monotone in `X` because recursive fields occur only in the *positive* position
  `Π x. X_i(…)` — that is exactly what `VIndField.WF.pos` says, and it is the *only*
  reason the spec insists on the `∀ξ. I p π` shape rather than merely "no negative
  occurrence".
* F8 (a later field's type may mention an earlier *recursive* field) is fine: the
  interpretation is a dependent sum indexed by the earlier fields, so a larger `X`
  only enlarges the index set. Carneiro's grammar forbids this case, so this is one
  place where the model has to go beyond `typesys.tex`.
* Least fixed point by transfinite iteration; closure at some `α < κ` needs `κ`
  inaccessible and the field types to lie in `V_κ` — which is what the level condition
  `imax ℓ' ℓ ≤ ℓ` buys (when `ℓ ≠ 0`, every field type lives at level `≤ ℓ`).
* `ℓ = 0` (`Prop`): interpret as `{∅}`/`∅`; the level condition degenerates to `True`,
  consistent with the kernel's `isAlwaysZero` escape.
* Recursor: by ∈-rank recursion on the fixed point. Total because every element is
  `(q, φ)` with the recursive components of `φ` of strictly smaller rank.
* ι-rule: holds by construction of the recursion. Because the reduct is the *unreduced*
  redex `Λ a b` (§5.4), validating the equation requires β as well, which the model has.
* Large elimination: when `ℓ` is never zero, no restriction. When `LECond`'s second
  disjunct holds, the fixed point is a subsingleton at every index — proved by ∈-rank
  induction: two elements `(0, φ)`, `(0, φ')` at the same index have equal proof fields
  (the interpretation of a `Prop` is a subsingleton), equal index-determined fields
  (because they appear in `args`, which are equal), and recursive fields equal by the
  induction hypothesis. This is exactly the shape of Carneiro's argument
  (`axioms.tex:162`) and it survives the extra generality of F8.
* Structure eta (§6.3): valid because the interpretation of a single-constructor,
  index-free, non-recursive type is literally the dependent product of the field
  interpretations, whose elements are determined by their projections. **This is where
  the encoding choice matters**: `(q, φ)` must be a *tuple* (so surjective pairing holds
  on the nose), not an arbitrary tagged set.

Nothing in §2–§6 obstructs any of this. The two places where the model is asked to do
more than `typesys.tex` are F8 and the `imax ℓ' ℓ ≤ ℓ` (rather than `ℓ' ≤ ℓ`) level rule
— both flagged above.

---

## 11. Open questions and places I had to guess

Sharply, in decreasing order of how much they could cost.

1. **Sign-off needed on changing `VInductDecl`.** §2. Every alternative I could find
   either makes `addInduct` non-functional (a relation `VEnv.AddInduct env D env'`,
   which then duplicates the decomposition data between `WF` and `AddInduct`) or makes
   the spec *incomplete* w.r.t. the kernel by forbidding whnf in the type spine (F1).
   The relational alternative is viable and slightly less disruptive to
   `Theory/Consistency.lean`; I chose the functional one because `VDecl.WF.induct`,
   `addInduct_WF`, `addQuot_WF`'s template and `HasObjects` all assume a function.
   **Guess:** the functional route is better. Not certain.

1b. **`pat_major_prop` needs a `pat_small` guard, and I could not verify what the
   large-eliminating case really needs** (§7.6). The guarded version is true and cheap;
   the unguarded one is refuted by `Eq.rec`. For the `¬pat_small` case I propose M3 +
   `pat_major_canonical`, but I do not have the `NormalEq.parRed` proof context, so the
   *shape* of the axiom is a guess. Specifically: if the stuck case needs a **common
   reduct** rather than a defeq, no axiom about inductive declarations can supply it —
   that is Carneiro's `Acc` counterexample to transitivity of algorithmic equality, and
   the fix has to be in the statement of `NormalEq`/`parRed` (e.g. a proof-irrelevance
   closure at the major-premise position). Worth a round-trip with the ChurchRosser
   stream before I16 is scheduled.

1c. **`pat_major_not_pi` bottoms out in a statement nobody can prove yet** (§7.6, I13).
   The inductive spec supplies M1 and M2, but `IsDefEqU.const_forallE_inv` is new. I am
   confident it is true and that `ShapeLogRel`'s `Shape.ctor'` is the right vehicle, but
   I did not read those 6100 lines, so "the SExpr track delivers it" is an inference from
   a definition name, not a verified claim.

2. **Sign-off needed on the two `Params`/`Pattern` changes** (§7.1, §7.2). I am
   confident these are necessary (the argument that `extra_pat` is unsatisfiable today
   is a two-line proof), but the *minimality* claim is a judgement call, and `Pattern.lean`
   was clearly written with a design in mind that I may be misreading. Specifically:
   *was the intent that `VDefEq` should not be closed?* If `VDefEq` was always meant to
   grow a context, §7.1 should be replaced by that.

3. **Structure eta needs a new `IsDefEq` constructor** (§6.3). This is outside the
   nominal scope of "specify inductives" and it touches `Theory/Typing/Basic.lean`,
   which everything depends on. It could be deferred by leaving
   `tryEtaStructCore.WF`/`isDefEqUnitLike.WF` open, but they are on the critical path to
   `kernel_sound`. **Guess:** do it as a separate change *before* the inductive spec
   lands, so the `IsDefEq` churn is not entangled with the new content.

4. **`VEnv.Sig`** (§7.7) is an unanticipated prerequisite of `Params` of roughly the size
   of `Verify/Level.lean`. I may be missing a cheaper way to define `Pat` — e.g. making
   `Params.Pat` an *input* (a field the instance chooses freely, with the orthogonality
   axioms proved by induction on `VEnv.WF'` on the fly, without a standalone `Sig`
   structure). Worth 30 minutes of thought before committing to `Sig`.

5. **Is the ι-`Check`'s parameter clause (check 2 of §7.3) needed?** I included
   `b_i ≡ a_i` because the λ-equation instantiates the constructor's parameters with the
   recursor's. It is discharged by reflexivity in `extra_pat`, so it is cheap, but if
   `pat_wf` can be arranged to instantiate the equation at `b_i` instead (using the
   recursor's parameters only through the motives/minors), the clause could be dropped.
   I did not check this carefully.

6. **`VIndField.lvl` is recorded, not derived**, because `IsDefEqU.sort_inv` is a
   `sorry`. Consequence: `VInductDecl` is not a quotient of the "real" data — two decls
   differing only in the recorded levels are both `WF` and produce the *same*
   environment. Harmless, but it means `AddInduct` must existentially quantify `D`
   rather than compute it, and `TrProj.uniq` must not depend on `D` being unique in that
   respect. I believe it does not (it only needs `IsStructure`'s `np` and field types,
   which are not level-dependent). Not verified in detail.

7. **`D.lvl` is shared across the block** (F4 gives only `isEquiv`). I put the `≈` slack
   into `VIndType.WF.canon` (via `sortDF`). This is fine for the types, but I did not
   check `VIndField.WF.level`: the level condition is stated against `D.lvl`, whereas
   the kernel checks it against `stats.resultLevel`, which is the *first* type's level.
   Since they are `≈`, and `imax _ · ≤ ·` respects `≈`, this should be fine — but the
   `≈`-congruence of `VLevel.LE` needs a lemma that I did not find in `VLevel.lean`
   (`le_antisymm_iff` is there; a `LE.congr` is not).

8. **`getElimLevel`'s freshness** (`Add.lean:279`, currently `partial`). The spec assumes
   the elimination universe is a genuinely *new* parameter placed at index 0. The
   implementation searches for a fresh name `u`, `u_1`, … . If that loop could fail to
   terminate or could collide, `D.selfLvls` would be wrong. Needs to be de-`partial`ed
   and proved terminating anyway (Guard allowlist).

9. **Order of `addInduct`'s `addConst` calls.** I used types → constructors → recursors,
   matching the kernel. Since `addConst` is order-insensitive except for failure, any
   order gives the same `env'` when it succeeds; but `addIndCtors`' well-formedness is
   stated in `env₁`, so the staging is load-bearing for `WF`, not just cosmetic. If a
   later refactor reorders, `VInductDecl.WF.ctors` must move with it.

10. **`iotaRules`'s `type` field.** `VDefEq.type` is used by `IsDefEq.extra` to give the
    equation a type. I set it to `mkPi Γ' (D.iotaType j C)`, the common type of both
    λ-abstractions. I did *not* check whether `HeadReduction`/`ChurchRosser` ever need
    the type of a defeq to be a *sort*-level statement about the reduct; if they do, the
    `iotaType` may need to be paired with a level witness.

11. **`Theory/Consistency.lean`'s three literals** must be rewritten in the new shape.
    Worked example for `Eq` (`uvars := 1`, `params := [.sort (.param 0), .bvar 0]`,
    `lvl := .zero`, one type with `indices := [.bvar 1]`, one constructor with
    `params := [.sort (.param 0), .bvar 0]`, `fields := []`, `args := [.bvar 0]`,
    `isLE := true`): the derived `VIndCtor.type` is
    `∀ (α : Sort u) (a : α), Eq.{u} α a a` and `recType 0` is
    `∀ (α : Sort u) (a : α) (motive : ∀ b, Eq α a b → Sort v), motive a (Eq.refl α a) →
     ∀ b (h : Eq α a b), motive b h` — the real `Eq.rec`, argument order included. I
    checked this one by hand; `Iff` and `Nonempty` should be checked the same way (they
    exercise the field cases, which `Eq` does not) before anything is built on top.

12. **Fuel.** `addInduct` and `WF` are fuel-free; the implementation's
    `FuelConfig.inductiveFuel` bounds every spine walk. Fuel exhaustion is a rejection,
    so the refinement direction is safe; but `addInductive.WF` will have to thread "if we
    got an answer, the fuel sufficed" through every loop. That is the same pattern as
    `whnf`'s existing fuel handling, so it should not be new work, but I did not check
    that `AddInductive`'s loops expose the same interface.
