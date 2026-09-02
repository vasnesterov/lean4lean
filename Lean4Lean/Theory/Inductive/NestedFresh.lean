import Lean4Lean.Theory.Inductive.NestedBuild
import Lean4Lean.Theory.SetModel.Consts

/-!
# A producer for `VInductDecl'.Built.fields_noK`

`VInductDecl'.Built.fields_noK` (`Theory/Inductive/NestedBuild.lean`) is ruling 116d's residual:
for every companion member `j`, every constructor `C₀` of the *source* block `J`, and every field
`F₀` of it, the substituted field type

```
VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args k
```

mentions no companion name.  It has been recorded for eight rounds as having "no producer but
`decide` at a concrete block" (ledger row 117c).  That record rested on a repo-wide grep of
`NoConsts`, and **the grep was looking for the wrong predicate**: the fact it needed is stated
in this repo about `VExpr.ConstsIn` (`Theory/SetModel/Consts.lean`), not about
`VExpr.NoConsts` — `VEnv.ConstsClosed` / `VEnv.Ordered.constsInC` say every declared
constant's type mentions only declared constants.  That is exactly the missing half.

This file closes the gap, and measures what is left:

* §1 bridges `NoConsts` and `ConstsIn`, and adds the two structural lemmas the bridge needs
  (`instL`-invariance and `mkPi` binder projection).
* §2 is the producer at a single occurrence: from `VNestedOcc.Occurs env`, `env.ConstsClosed`,
  freshness of `K` in `env`, and cleanliness of the **spine** `N.args`, the whole quantified
  clause follows.  Everything that quantifies over `J`'s constructors and fields is discharged.
* §3 assembles `VInductDecl'.BuiltFresh` from it.
* §4 discharges the freshness premise from the step's own staging success, so it costs a caller
  nothing it does not already have (the same argument as `VIndRestore.csubst_freshIn`).
* §5 is the sharpness result, and it is the answer to "could the spine premise be dropped too?":
  **no.**  `VNestedOcc.Occurs` constrains `N.args` through `args_len` and nothing else
  (`occurs_args_congr`), and there is a concrete occurrence — the repo's own `listOcc`, with its
  spine replaced by a companion constant of the right length — that satisfies `Occurs env₁` and
  refutes `fields_noK`.  So no producer from `Occurs` plus environment facts alone can exist;
  a spine hypothesis is *necessary*, and §2 shows it is *sufficient*.
-/

namespace Lean4Lean

open VExpr (mkPi)

namespace VExpr

/-! ## §1 `NoConsts` is `ConstsIn`, and two structural lemmas

`NoConsts S` and `ConstsIn (· ∉ S)` are the same recursion.  Stating the identity is what lets
the inductive corner reuse `Theory/SetModel/Consts.lean`'s environment invariant; keeping the
two predicates apart is what hid it for eight rounds. -/

/-- `NoConsts` is `ConstsIn` at the complement of `S`. -/
theorem noConsts_iff_constsIn {S : List Lean.Name} :
    ∀ {e : VExpr}, NoConsts S e ↔ e.ConstsIn (· ∉ S)
  | .bvar _ | .sort _ => iff_of_true trivial trivial
  | .const .. => .rfl
  | .app .. | .lam .. | .forallE .. =>
    and_congr noConsts_iff_constsIn noConsts_iff_constsIn

/-- `NoConsts` ignores level arguments, so it survives `instL` in both directions. -/
theorem noConsts_instL {S : List Lean.Name} {ls : List VLevel} {e : VExpr} :
    NoConsts S (e.instL ls) ↔ NoConsts S e := by
  rw [noConsts_iff_constsIn, noConsts_iff_constsIn]; exact ConstsIn.instL

/-- A pi telescope's binders inherit `NoConsts` from the telescope.  Unlike
`noConsts_splitPis` this reads the binders off the *list*, which is the form
`VIndCtor.type` presents them in. -/
theorem noConsts_mkPi_binders {S : List Lean.Name} :
    ∀ {as : List VExpr} {b : VExpr}, NoConsts S (mkPi as b) → ∀ a ∈ as, NoConsts S a
  | [], _, _ => nofun
  | _ :: as, b, h => by
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact noConsts_mkPi_binders (as := as) (b := b) h.2 c hc

end VExpr

/-! ## §2 The producer, at one occurrence

The clause quantifies over `J`'s constructors and, inside each, over its fields.  All of that
is discharged here from **one** environment fact: `J`'s constructors are declared constants of
`env` (`Occurs.ctor_const`), and in a constant-closed environment a declared constant's type
mentions only declared constants (`VEnv.ConstsClosed`).  A companion name is not declared —
that is what `hK` says — so the whole stored constructor type is `NoConsts K`, and its field
binders with it.

What is *not* discharged is `hargs`: the nested spine.  §5 shows that premise is not removable. -/

namespace VNestedOcc
variable {N : VNestedOcc} {env : VEnv} {K : List Lean.Name}

/-- **`J`'s stored constructor types are companion-free.**  The single environment step. -/
theorem ctorType_noConsts (hcc : env.ConstsClosed) (ho : N.Occurs env)
    (hK : ∀ n ∈ K, ¬ env.contains n) {C₀ : VIndCtor} (hC₀ : C₀ ∈ N.src.ctors) :
    VExpr.NoConsts K (C₀.type N.decl N.idx) :=
  VExpr.noConsts_iff_constsIn.2 <|
    (hcc.1 (ho.ctor_const C₀ hC₀)).mono fun n hn hnK => hK n hnK hn

/-- **`Built.fields_noK`'s body, at one occurrence, as a theorem.**

The three premises are, in order: the environment invariant every well-formed environment
satisfies (`VEnv.Ordered.constsClosed`), the occurrence's own `Occurs` record, the freshness of
the companion names (§4: free from the step's staging success), and cleanliness of the nested
spine (§5: irreducibly a hypothesis, but one about `N.decl.np` expressions, decidable by
`VExpr.decidableNoConsts`, rather than about all of `J`'s fields). -/
theorem fields_noK_of_occurs (hcc : env.ConstsClosed) (ho : N.Occurs env)
    (hK : ∀ n ∈ K, ¬ env.contains n) (hargs : ∀ a ∈ N.args, VExpr.NoConsts K a)
    {C₀ : VIndCtor} (hC₀ : C₀ ∈ N.src.ctors) {k : Nat} {F₀ : VIndField}
    (hF₀ : C₀.fields[k]? = some F₀) :
    VExpr.NoConsts K (VExpr.instAll (F₀.type.instL N.lvls) N.args k) := by
  refine VExpr.noConsts_instAll _ _ (VExpr.noConsts_instL.2 ?_) hargs
  refine VExpr.noConsts_mkPi_binders (ctorType_noConsts hcc ho hK hC₀) _ ?_
  exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_of_getElem? hF₀))

end VNestedOcc

/-! ## §3 `BuiltFresh`, assembled

`VInductDecl'.Built.occurs` is already one of `Built`'s clauses, so a caller building a `Built`
has `hocc` in hand by construction; §4 gives `hK`; only `hargs` is new. -/

/-- **`VInductDecl'.BuiltFresh`, from the occurrence records plus freshness.** -/
theorem VInductDecl'.builtFresh_of_occurs {D : VInductDecl'} {K : List Lean.Name} {env : VEnv}
    {occ : Nat → VNestedOcc} (hcc : env.ConstsClosed) (hnd : D.blockNames.Nodup)
    (hocc : ∀ j T, D.types[j]? = some T → T.name ∈ K → (occ j).Occurs env)
    (hK : ∀ n ∈ K, ¬ env.contains n)
    (hargs : ∀ j T, D.types[j]? = some T → T.name ∈ K →
      ∀ a ∈ (occ j).args, VExpr.NoConsts K a) :
    D.BuiltFresh K occ where
  nodup := hnd
  fields_noK j T hT hKT _C₀ hC₀ _k _F₀ hF₀ :=
    VNestedOcc.fields_noK_of_occurs hcc (hocc j T hT hKT) hK (hargs j T hT hKT) hC₀ hF₀

/-! ## §4 The freshness premise costs nothing

The same argument as `VIndRestore.csubst_freshIn` (`Theory/Inductive/NestedRules.lean` §8.1):
`addIndTypes` is an `addConstList`, `addConst` fails on a duplicate, so every member name of `D`
— the companion names among them — was absent from `env`.  So `hK` is available wherever the
step's first staging success is, which is everywhere `AddNested` is used. -/

/-- A name the block declares is not one the environment already had. -/
theorem VInductDecl'.not_contains_of_mem_blockNames {env env₁ : VEnv} {D : VInductDecl'}
    (h : env.addIndTypes D = some env₁) {n : Lean.Name} (hn : n ∈ D.blockNames) :
    ¬ env.contains n := by
  intro hc
  have hfresh := (VEnv.addConstList_fresh h).1 n (D.typeConsts_names ▸ hn)
  obtain ⟨_, hci⟩ := hc
  rw [hci] at hfresh; exact absurd hfresh nofun

/-- `hK`, discharged: the companion names are among the block's member names (which is what
`Built`'s clauses assume when they read `D.types[j]? = some T` with `T.name ∈ K`), and the block
declared them. -/
theorem VInductDecl'.fresh_of_addIndTypes {env env₁ : VEnv} {D : VInductDecl'}
    {K : List Lean.Name} (h : env.addIndTypes D = some env₁)
    (hKB : ∀ n ∈ K, n ∈ D.blockNames) : ∀ n ∈ K, ¬ env.contains n :=
  fun n hn => VInductDecl'.not_contains_of_mem_blockNames h (hKB n hn)

/-! ## §5 The spine premise is necessary: no producer from `Occurs` alone

`VNestedOcc.Occurs` mentions `N.args` in exactly one clause, `args_len`, and that clause
constrains only its *length*.  `occurs_args_congr` is that observation as a theorem: the spine
may be replaced by any other of the same length and `Occurs env` still holds.

`fields_noK`, by contrast, is not invariant under that replacement — the substituted field type
*is* the spine wherever `J` has a field whose type is one of its own parameters.  §5.2 exhibits
the pair: the repo's own `listOcc`, whose `fields_noK` is a theorem (`ntreeAux_built`), and the
same occurrence with the spine `[NTree α]` replaced by the companion constant `_nested.List_1`,
whose `fields_noK` is **false** — because `List.cons`'s first field type is the bare parameter
`.bvar 0`, so the substituted type is the spine entry verbatim.

Both occurrences satisfy `Occurs env₁` for the same `env₁`, at the same `K`, with the same
`decl`, `idx`, `lvls`, `auxName` and `ctorName`.  So **no** theorem whose hypotheses are
`Occurs env`, together with any facts whatsoever about `env` and `K` — freshness,
constant-closedness, `Ordered`, `WF` — can prove `fields_noK`: such a theorem would apply to
both members of the pair and prove a false statement.  A premise that reads `N.args` is
unavoidable, and §2 shows the weakest such premise (`∀ a ∈ N.args, NoConsts K a`) suffices.

This is the machine-checked form of "ruling 116d's cost is permanent": it cannot be reduced
below the spine, and it *can* be reduced to the spine. -/

namespace VNestedOcc

/-- **`Occurs` cannot see the spine.**  Only `args_len` mentions `N.args`, and only its length. -/
theorem occurs_args_congr {N : VNestedOcc} {env : VEnv} {as : List VExpr}
    (ho : N.Occurs env) (hlen : as.length = N.decl.np) :
    ({N with args := as} : VNestedOcc).Occurs env where
  hist := ho.hist
  idx_lt := ho.idx_lt
  lvls_len := ho.lvls_len
  args_len := hlen
  ty_const := ho.ty_const
  ctor_params := ho.ctor_params
  ctor_const := ho.ctor_const

end VNestedOcc

namespace InductiveDeclExamples

/-- `listOcc` with the nested spine `[NTree α]` replaced by the companion constant itself.
The length is unchanged, so `Occurs` cannot tell the two apart. -/
def listOccBadSpine : VNestedOcc :=
  { listOcc with args := [.const `_nested.List_1 [.param 0]] }

theorem listOccBadSpine_args_len : listOccBadSpine.args.length = listOccBadSpine.decl.np := rfl

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

/-- The bad-spine occurrence is a genuine occurrence: same `Occurs env₁`. -/
theorem listOccBadSpine_occurs : listOccBadSpine.Occurs env₁ :=
  VNestedOcc.occurs_args_congr (listOcc_occurs h) rfl

end

/-- …and its `fields_noK` is **false**, at `List.cons`'s first field, whose stored type is the
bare parameter `.bvar 0`.  No environment appears in the statement, which is the point. -/
theorem listOccBadSpine_not_fields_noK :
    ¬ VExpr.NoConsts ntreeK (VExpr.instAll
        ((listCons.fields.getD 0 default).type.instL listOccBadSpine.lvls)
        listOccBadSpine.args 0) := by
  decide

/-- **The separating pair.**  Same `decl`, `idx`, `lvls`, `auxName`, `ctorName`; same `Occurs
env₁`; same `K`.  `fields_noK` holds of one and fails of the other, so it is not a consequence of
`Occurs` plus environment facts. -/
theorem fields_noK_needs_spine {env₁ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁) :
    listOccBadSpine.decl = listOcc.decl ∧ listOccBadSpine.idx = listOcc.idx ∧
    listOccBadSpine.lvls = listOcc.lvls ∧ listOccBadSpine.auxName = listOcc.auxName ∧
    listOccBadSpine.args.length = listOcc.args.length ∧
    listOcc.Occurs env₁ ∧ listOccBadSpine.Occurs env₁ ∧
    (∀ C₀ ∈ listOcc.src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
      VExpr.NoConsts ntreeK (VExpr.instAll (F₀.type.instL listOcc.lvls) listOcc.args k)) ∧
    ¬ (∀ C₀ ∈ listOccBadSpine.src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
      VExpr.NoConsts ntreeK
        (VExpr.instAll (F₀.type.instL listOccBadSpine.lvls) listOccBadSpine.args k)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, listOcc_occurs h, listOccBadSpine_occurs h, ?_, ?_⟩
  · exact fun C₀ hC₀ k F₀ hF₀ =>
      (ntreeAux_built h).fields_noK 1 _ rfl (by decide) C₀ hC₀ k F₀ hF₀
  · intro hbad
    exact listOccBadSpine_not_fields_noK
      (hbad listCons (by rw [show listOccBadSpine.src.ctors = [listNil, listCons] from rfl]; simp)
        0 _ rfl)

end InductiveDeclExamples

/-! ## Axiom audit, by namespace -/

#print axioms Lean4Lean.VExpr.noConsts_iff_constsIn
#print axioms Lean4Lean.VExpr.noConsts_instL
#print axioms Lean4Lean.VExpr.noConsts_mkPi_binders
#print axioms Lean4Lean.VNestedOcc.ctorType_noConsts
#print axioms Lean4Lean.VNestedOcc.fields_noK_of_occurs
#print axioms Lean4Lean.VInductDecl'.builtFresh_of_occurs
#print axioms Lean4Lean.VInductDecl'.not_contains_of_mem_blockNames
#print axioms Lean4Lean.VInductDecl'.fresh_of_addIndTypes
#print axioms Lean4Lean.VNestedOcc.occurs_args_congr
#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_occurs
#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_not_fields_noK
#print axioms Lean4Lean.InductiveDeclExamples.fields_noK_needs_spine

/-! ## §6 The three "things that changed", measured against the counterexample

### §6.1 F7's new residual clause does not reach `fields_noK`

`VInductDecl'.ResidualClean k e = ∀ j rest, D.uniformOcc? k e = some (j, rest) → ∀ a ∈ rest,
D.NoBlock a` (`Theory/Inductive/Decl.lean`).  It is conditional on `uniformOcc?` firing, and
`uniformOcc?` needs a spine whose leading `D.np` arguments are the parameter run.  The
counterexample's substituted type is a **bare** companion constant — zero arguments — so the
trigger does not fire and the clause is **vacuously true of the very expression that refutes
`fields_noK`**.  Machine-checked below.  So the `some`-branch tightening, real as it is, provides
no part of `fields_noK`.

### §6.2 placeholder — see §6.3 below (a `decide` refutation of my first attempt)
-/

namespace InductiveDeclExamples

/-- **F7's residual clause is satisfied by the counterexample.**  `uniformOcc?` does not fire on
a bare companion constant, so `ResidualClean` says nothing there. -/
theorem ntreeAux_residualClean_badSpine :
    ntreeAux.ResidualClean 0 (VExpr.instAll
        ((listCons.fields.getD 0 default).type.instL listOccBadSpine.lvls)
        listOccBadSpine.args 0) :=
  VInductDecl'.residualClean_of_uniformOcc_none (by decide)

/-- **`decide` refuted the obvious strengthening.**  I claimed the consumer's conclusion
(`field_typeR`'s equation) also fails at `listOccBadSpine`.  It does **not**: `restore` rewrites
only at a *firing* `uniformOcc?`, and a bare companion constant with no parameter run is not one,
so the restoration is the identity there anyway. -/
theorem listOccBadSpine_field_typeR_holds :
    (listOccBadSpine.field ntreeAux.header ntreeRestore 0
        (listCons.fields.getD 0 default)).typeR ntreeAux ntreeRestore 0
      = VExpr.instAll ((listCons.fields.getD 0 default).type.instL listOccBadSpine.lvls)
          listOccBadSpine.args 0 := by
  decide

end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_residualClean_badSpine
#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_field_typeR_holds

/-! ### §6.3 The `OwnHeads` weakening does not dodge the spine either

`restore_noK` is now a corollary of `restore_ownHeads` via `ownHeads_of_noConsts`, so the obvious
weakening of `fields_noK` is to replace `NoConsts K` by `D.OwnHeads K k` — the heads-only test.
The bad-spine witness **refutes that too**: its substituted type is a bare companion constant,
and `OwnHeads`' only applicable constructor there is `const`, which asks for exactly the
`NoConsts` fact that fails.  So the test is not what is wrong; the spine is. -/

namespace InductiveDeclExamples

theorem listOccBadSpine_not_ownHeads :
    ¬ ntreeAux.OwnHeads ntreeK 0 (VExpr.instAll
        ((listCons.fields.getD 0 default).type.instL listOccBadSpine.lvls)
        listOccBadSpine.args 0) := by
  intro h
  cases h with
  | own hu =>
    rw [show ntreeAux.uniformOcc? 0 (VExpr.instAll
      ((listCons.fields.getD 0 default).type.instL listOccBadSpine.lvls)
      listOccBadSpine.args 0) = none from by decide] at hu
    exact absurd hu nofun
  | const hn => exact hn (by decide)

end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_not_ownHeads
