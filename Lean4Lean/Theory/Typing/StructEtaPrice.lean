import Lean4Lean.Verify.TypeChecker.EtaUnitRefute
import Lean4Lean.Theory.SetModel.UnitOracleLarge

/-!
# Pricing the fourteenth constructor

`Verify/TypeChecker/EtaResidual.lean` reduces both eta holes
(`Verify/TypeChecker/IsDefEq.lean:558`, `:1054`) to the single hypothesis `c.venv.StructEtaG`,
and `Verify/TypeChecker/EtaUnitRefute.lean` **refutes** deriving that from environment
well-formedness: `MutField.unitEnv` has a proved `VEnv.WF` and satisfies neither `UnitEta` nor
`StructEtaG`.  So structure eta has to become a fourteenth constructor of `VEnv.IsDefEq`
(`Theory/Typing/Basic.lean`, currently thirteen).

**This file is the price, not the change.**  Nothing here edits `IsDefEq`, or any existing file.
It states the constructor in a private copy of the relation, fires it at two real structures,
and — the part that matters — measures what breaks.

## 1. The induction-site count, measured 2026-09-03, 17:01–17:25 UTC

Not grepped: computed.  A scratch script walked the built population (421 modules) and, for
every declaration in `Lean4Lean`, asked whether its **proof term** applies an eliminator of the
relation (`.rec`, `.recOn`, `.casesOn`, `.brecOn`, `.below.*`, `.ndrec`, `.induct`).  The
compiler-generated eliminators of the inductive's own module are netted out; what is left is
hand-written induction and `cases`.

| relation | hand-written eliminator sites | must gain the constructor? |
|---|---|---|
| `VEnv.IsDefEq` | **22** | yes — this is the change |
| `VEnv.IsDefEqStrong` (`Strong.lean`) | **31** | yes — `IsDefEq.strong'` converts |
| `VEnv.NormalEq` (`ChurchRosser.lean`) | **31** | yes — `church_rosser`'s target |
| `VEnv.ParRed` (`ChurchRosser.lean`) | **26** | yes — `NormalEq`'s engine |
| `VEnv.ParRedK` (`KEta.lean`) | **23** | yes — `ParRed.toK` |
| `VEnv.IsDefEqE` (`Enlarged.lean`) | **3** | yes — `IsDefEq.toE` converts |
| `VEnv.IsDefEqRaw` (`RawDefEq.lean`) | **0** | yes — `IsDefEq.raw` converts, nothing inducts |
| `VEnv.ParRedS` | 0 | no — it is a closure `def`, not an inductive |
| **total** | **136** | |

`IsDefEq`'s own 22, by module: `Typing/Lemmas` 9 (`weakN`, `instN`, `instL`, `mono`, `closedN'`,
`levelWF`, `isType'`, `forallE_inv'`, `sort_inv'`), `Typing/Strong` 2 (`strong'`, `mono_uvars`),
`Typing/ConstSubst` 2 (`substC`, `noCSubst'`), and one each in `Typing/{Strengthen,
StrengthenNarrow,RawDefEq,CycleConv,ChurchRosser,ConstSubstNested,ConstVar}` and
`SetModel/Consts` (`constsIn`).  `SetModel/SoundInduction`'s `soundAbove` is on the
`IsDefEqStrong` line, not this one — the model induction runs on the strong relation.

**Which of the 136 are real work.**  The new rule's left-hand side is a *bare variable* `e`,
so **no case can be discharged by `nofun` or by a head-shape `simp`** — the split that would
normally let an inversion lemma drop a case does not exist here.  Concretely:

* **~40 congruence/stability sites** (`weakN`, `instN`, `instL`, `mono`, `mono_uvars`,
  `closedN'`, `levelWF`, `isType'`, and their `Strong`/`E`/`Raw` counterparts) need the
  η-expansion to commute with the operation.  `VInductDecl'.etaExpansion_instL` and
  `projAll_instL` exist; `projTerm_instN` exists; ~~`projTerm_weakN`, `projTermG_weakN`,
  `etaExpansion_weakN`, `etaExpansionG_weakN` and `etaExpansionG_instL` do not~~.

  **CORRECTED 2026-09-04, and the method is the lesson.**  That list came from a *name* search for
  the suffix `_weakN` — and **this tree does not spell syntactic weakening that way**.  `weakN` here
  is a *judgement*-level suffix (`VEnv.HasType.weakN`); syntactic weakening of a `VExpr` is
  `VExpr.liftN`, generalised by `VExpr.lift'`.  Searched by *shape* instead
  (`scripts/shape.lean`, population 444, heads resolved), **two of the five already existed**:
  `VInductDecl'.projTerm_lift'` (`Theory/Inductive/Structure.lean`) and
  `VInductDecl'.projTermG_lift'` (`Verify/Typing/ProjGenLift.lean`, already fired).  The other
  three were genuinely absent and are now proved in `Theory/Typing/CommutationLemmas.lean`, under
  both the tree's `_lift'`/`_liftN` names and `_weakN` aliases so that a future name search
  resolves.

  **And the site arithmetic above does not follow.**  The ~40 congruence sites span **eight** lemma
  families; these five serve **two** of them, which is **8 sites** (5 `weakN` + 3 `instL`,
  measured — `ParRed.instL`, `ParRedK.instL` and the `E`/`Raw` counterparts do not exist).  The
  remaining ~30 need commutation lemmas that are *not* among the five.  "Five missing lemmas is the
  floor" stands; "the ~40 sites need these five" does not.  Note also that
  `VInductDecl'.etaExpansion_instL`, cited here as existing, has **0 direct and 0 transitive
  users** — so this paragraph forecasts demand for a constructor that does not exist yet rather
  than counting live demand.
* **~20 inversion sites** (`forallE_inv'`, `sort_inv'`, `Injectivity`'s five,
  `Shape`/`Spine`/`Sort*`'s twelve) currently dismiss `extra` and friends by head shape.  The
  new case arrives with an arbitrary `e` on the left and a `const`-headed spine on the right, so
  each needs a *typing* argument — "no term is simultaneously a sort and an inhabitant of a
  structure" — instead of a shape argument.  That is the `SortUniq`/`UnivDiscrim` machinery,
  and it is where the existing injectivity holes live.
* **1 site is the model** (`SetModel/soundAbove`), §8 below.
* **1 site is the wall** (`church_rosser`): the rule is not a rewrite, and §6 shows it is not
  merely hard but **incompatible with the no-confusion lemma that chain exists to prove**.

## 2. What this file adds

* `IsDefEqSE` (§3) — the fourteen-constructor relation, so the constructor is *stated* rather
  than described.  `IsDefEq.toSE` embeds the thirteen, one line each: that is the machine-checked
  form of "each induction gains exactly one case".
* `VEnv.StructEtaGSE` and `structEtaGSE` (§4) — the constructor is **strong enough**: it gives
  `StructEtaG`'s statement over the new relation *by construction*, so
  `TypeChecker.Inner.etaHoles_of_structEtaG` applies verbatim once the swap is made.
* Two firings (§5): at `MutField.unitEnv`'s zero-field member with an **axiom** inhabitant, and
  at `MutField.declEnv`'s positive-field member.  Both are real structures in `Type` inside a
  two-type mutual block, so the rule is not vacuous and not zero-field-only.
* `eta_and_constNoConf_incompatible` (§6) — **the price, and it is route-independent**: *no*
  relation whatever can satisfy structure eta at `unitEnv` and const-head no-confusion at the
  same time.  Instantiated at `IsDefEqSE`, this says `VEnv.IsDefEq.constApp_inv`
  (`Verify/Typing/ConstSpine.lean:248`, 187 transitive users) is **false** for the extended
  relation, not merely unproved.  §6 also records that this is a fact about *Lean*, not about
  this design: `structure A where` / `axiom foo : A` / `example : foo = A.mk := rfl` typechecks
  in Lean 4, so const-head no-confusion is false in the real kernel and the existing
  `constApp_inv` is a lemma about a relation strictly weaker than real definitional equality.
* `eq_singleton_of_recProp` (§8) — the set-model verdict, machine-checked: the model **does**
  validate zero-field surjective pairing, and it is *forced* rather than chosen, by the
  membership obligation `InductOracleOK` already puts on the **recursor**.  This contradicts
  `SetModel/UnitEtaPairing.lean`'s claim that "a model satisfying `InductOracleOK` may interpret
  a zero-field structure as a two-element set and refute eta outright"; §6 says exactly which
  step that claim misses.

## 3. A cost nobody has named: the constructor cannot be written where `IsDefEq` lives

`Theory/Typing/Basic.lean` imports `Theory/VEnv` and nothing else.  The η-expansion needs
`VInductDecl'.etaExpansionG`, hence `projTermG` (`Verify/Typing/ProjGen.lean`), hence
`VInductDecl'` (`Theory/Inductive/Decl.lean`) — and `Decl.lean` imports `Theory/Typing/Lemmas`,
which imports `Basic`.  **Writing the constructor into `Basic.lean` is a dependency cycle.**

It is breakable, and the shape of the break is the third cost line: `VInductDecl'`, `projCore`,
`projArgs`, `projTerm`, `projTermG` and `etaExpansion(G)` are *purely syntactic* — `Telescope.lean`
imports only `Theory/VExpr` — so `Decl.lean` and `Structure.lean` split into a syntax half
(below `Basic.lean`) and a `WF` half (above it), and `ProjGen.lean`'s `projTermG` definition moves
with them.  That is a three-file split plus an import re-layer, before a single proof case is
written.  §7's alternative avoids it.
-/

namespace Lean4Lean

open VExpr

/-! ## 3. The fourteen-constructor relation

`VEnv.IsDefEq`'s thirteen constructors verbatim (`Theory/Typing/Basic.lean:18`), plus
`structEta`.  Kept in a private copy so that the real relation is untouched.

**Three deliberate choices in `structEta`, each of which is a claim about the right shape.**

1. **The typing premises are in the *new* relation**, not the old one: `hpsA` is `HasArgsSE`
   and `he` is `IsDefEqSE Γ e e ((const S us).mkApp ps)`.  `VEnv.StructEtaG` states them in
   the thirteen-constructor relation because it has to — it is a predicate *about* that
   relation — but a constructor whose premises could not use the rule itself would not be
   closed under its own conclusion, and the bridge from `TrExprS` supplies typing in whatever
   relation `venv` carries.  This is `beta`/`eta`/`proofIrrel`'s convention.
2. **`IsStructureG` stays as it is.**  It is environment data (`env.constants`, a `VEnv.WF'`
   history), not a typing judgement, so it does not move with the relation.
3. **`recFields = []` is kept** and `IsStructureG`'s `types` narrowing is not reinstated —
   exactly `VEnv.StructEtaG`'s choice, for exactly its reasons (`EtaStructG.lean`: the checker's
   gate `isNonRecStructure` does read `isRec`, so the bridge can supply `recFields = []` at
   every site, and dropping it is not known to keep the right-hand side typeable).

The F17 clause `D.isLE = true ∨ ∀ k < n, (fields.getD k).lvl.inst us ≈ .zero` is not optional:
`IsDefEq` implies both sides are well typed, so without it the rule is *false* rather than
useless at a small-eliminating structure with a large field
(`Verify/Typing/ProjLevelWitness.lean`'s `barDecl`). -/

namespace VEnv

variable (env : VEnv) (uvars : Nat)

mutual

/-- **`VEnv.IsDefEq` with structure eta as a fourteenth constructor.** -/
inductive IsDefEqSE : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → IsDefEqSE Γ (.bvar i) (.bvar i) A
  | symm : IsDefEqSE Γ e e' A → IsDefEqSE Γ e' e A
  | trans : IsDefEqSE Γ e₁ e₂ A → IsDefEqSE Γ e₂ e₃ A → IsDefEqSE Γ e₁ e₃ A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    IsDefEqSE Γ (.sort l) (.sort l') (.sort (.succ l))
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    IsDefEqSE Γ (.const c ls) (.const c ls') (ci.type.instL ls)
  | appDF :
    IsDefEqSE Γ f f' (.forallE A B) →
    IsDefEqSE Γ a a' A →
    IsDefEqSE Γ (.app f a) (.app f' a') (B.inst a)
  | lamDF :
    IsDefEqSE Γ A A' (.sort u) →
    IsDefEqSE (A::Γ) body body' B →
    IsDefEqSE Γ (.lam A body) (.lam A' body') (.forallE A B)
  | forallEDF :
    IsDefEqSE Γ A A' (.sort u) →
    IsDefEqSE (A::Γ) body body' (.sort v) →
    IsDefEqSE Γ (.forallE A body) (.forallE A' body') (.sort (.imax u v))
  | defeqDF : IsDefEqSE Γ A B (.sort u) → IsDefEqSE Γ e1 e2 A → IsDefEqSE Γ e1 e2 B
  | beta :
    IsDefEqSE (A::Γ) e e B → IsDefEqSE Γ e' e' A →
    IsDefEqSE Γ (.app (.lam A e) e') (e.inst e') (B.inst e')
  | eta :
    IsDefEqSE Γ e e (.forallE A B) →
    IsDefEqSE Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B)
  | proofIrrel :
    IsDefEqSE Γ p p (.sort .zero) → IsDefEqSE Γ h h p → IsDefEqSE Γ h' h' p →
    IsDefEqSE Γ h h' p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    IsDefEqSE Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)
  /-- **Structure eta (surjective pairing).**  `VEnv.StructEtaG`'s clauses, as a rule. -/
  | structEta {S : Lean.Name} {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor}
      {us : List VLevel} {ps : List VExpr} {e : VExpr} :
    env.IsStructureG S D j T C →
    T.indices = [] →
    C.recFields = [] →
    us.length = D.uvars → (∀ l ∈ us, l.WF uvars) →
    ps.length = D.np →
    HasArgsSE Γ (D.params.map (VExpr.instL us)) ps →
    IsDefEqSE Γ e e ((VExpr.const S us).mkApp ps) →
    (D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    IsDefEqSE Γ e (D.etaExpansionG T C us ps j e) ((VExpr.const S us).mkApp ps)

/-- `VEnv.HasArgs` over the extended relation; `structEta`'s parameter-spine premise. -/
inductive HasArgsSE : List VExpr → List VExpr → List VExpr → Prop where
  | nil : HasArgsSE Γ [] []
  | cons :
    IsDefEqSE Γ a a A → HasArgsSE Γ (VExpr.instTele a As) as →
    HasArgsSE Γ (A :: As) (a :: as)

end

/-! ## 4. The thirteen embed, and the new rule is strong enough

`toSE` is the machine-checked form of "each induction gains exactly one case": thirteen
one-line cases, no side conditions, no reshuffling.  Every one of the 136 sites in §1 that is a
*congruence* induction has this shape — the work there is not the thirteen old cases, it is the
fourteenth. -/

variable {env : VEnv} {uvars : Nat}

mutual

/-- **The thirteen constructors embed, one line each.** -/
theorem IsDefEq.toSE {Γ : List VExpr} {e₁ e₂ A : VExpr}
    (H : env.IsDefEq uvars Γ e₁ e₂ A) : env.IsDefEqSE uvars Γ e₁ e₂ A := by
  induction H with
  | bvar h => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF _ _ ih₁ ih₂ => exact .appDF ih₁ ih₂
  | lamDF _ _ ih₁ ih₂ => exact .lamDF ih₁ ih₂
  | forallEDF _ _ ih₁ ih₂ => exact .forallEDF ih₁ ih₂
  | defeqDF _ _ ih₁ ih₂ => exact .defeqDF ih₁ ih₂
  | beta _ _ ih₁ ih₂ => exact .beta ih₁ ih₂
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih₁ ih₂ ih₃ => exact .proofIrrel ih₁ ih₂ ih₃
  | extra h1 h2 h3 => exact .extra h1 h2 h3

/-- The parameter spine, likewise. -/
theorem HasArgs.toSE {Γ As as : List VExpr}
    (H : env.HasArgs uvars Γ As as) : env.HasArgsSE uvars Γ As as := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.toSE ih

end

/-- **`VEnv.StructEtaG` with only the conclusion's relation swapped.**

Premises verbatim from `VEnv.StructEtaG` (`Verify/TypeChecker/EtaStructG.lean`) — stated in the
*thirteen*-constructor relation, because that is the form
`TypeChecker.Inner.etaHoles_of_structEtaG` consumes.  So `structEtaGSE` below is exactly the
statement "the fourteenth constructor discharges the residual of both eta holes". -/
def StructEtaGSE (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat} {T : VIndType}
    {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e : VExpr},
    env.IsStructureG S D j T C →
    T.indices = [] →
    C.recFields = [] →
    us.length = D.uvars → (∀ l ∈ us, l.WF U) →
    ps.length = D.np →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasType U Γ e ((VExpr.const S us).mkApp ps) →
    (D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    env.IsDefEqSE U Γ e (D.etaExpansionG T C us ps j e) ((VExpr.const S us).mkApp ps)

/-- **The constructor is strong enough: it gives the rule, at every environment, with no side
condition left over.**

This is the whole point of the shape audit in §3.  Had the constructor's premises been stated
in the new relation *without* `toSE` available, or had `IsStructureG` needed to move with the
relation, this would not be one line. -/
theorem structEtaGSE (env : VEnv) : env.StructEtaGSE :=
  fun hS hidx hrec hus husWF hps hpsA he hF17 =>
    .structEta hS hidx hrec hus husWF hps hpsA.toSE he.toSE hF17

end VEnv

/-! ## 5. Anti-vacuity: the rule fires at two real structures

`docs/vacuity-ledger.md` §0's discipline applied to a *pricing* round: a rule true only where no
structure exists is not a rule.  Both witnesses below are members of `MutField.decl`, a two-type
mutual block in `Type` whose narrow `VEnv.IsStructure` is refuted
(`MutField.decl_not_isStructure`), so the *narrow* rule `VEnv.StructEta` cannot even be stated
at either. -/

namespace MutField

/-- **Firing 1 — the zero-field member, at an `axiom` inhabitant.**  `foo` is an axiom of type
`A` (`EtaUnitClose.lean`'s `fooC`), so the two sides are syntactically distinct closed constants
with distinct heads.  This is the instance §6's price theorem runs on, and it is the reason the
price is unavoidable rather than an artefact. -/
theorem structEtaSE_foo :
    unitEnv.IsDefEqSE 0 [] (.const `MutField.foo []) (.const `MutField.A.mk [])
      (.const `MutField.A []) := by
  have h := VEnv.structEtaGSE unitEnv (U := 0) (Γ := []) (us := []) (ps := [])
    unitEnv_IsStructureG_0 rfl rfl rfl nofun rfl .nil unitEnv_foo_hasType
    (.inr (by simp [aCtor]))
  rwa [decl.etaExpansionG_of_no_fields aTy aCtor [] rfl] at h

/-- **Firing 2 — the positive-field member.**  `x ≡ B.mk x.f` for `x : B`, `B` the member of the
same block that *has* a field, from `declEnv_structEtaG_premises`.  So the rule is not
zero-field-only: one constructor serves both arities of one block. -/
theorem structEtaSE_B :
    declEnv.IsDefEqSE 0 bCtx (.bvar 0)
      (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0))
      ((VExpr.const `MutField.B []).mkApp []) :=
  VEnv.structEtaGSE declEnv (U := 0) (us := []) (ps := [])
    declEnv_IsStructureG rfl rfl rfl nofun rfl .nil (.bvar (.zero ..))
    (.inr bCtor_field_prop)

end MutField

/-! ## 6. The price, and it is route-independent

The two firings above are not decoration: firing 1 is the **counterexample to const-head
no-confusion**, and it is a counterexample against *any* relation satisfying structure eta, not
only against `IsDefEqSE`.

`eta_and_constNoConf_incompatible` takes `R` to be an arbitrary binary relation on `VExpr`.  No
constructor, no closure property, no typing — the only inputs are the one eta instance and the
no-confusion statement.  So the conclusion is not "this design pays a price"; it is **"every
design that yields structure eta pays this price"**, and the payment is exactly the lemma the
whole Church–Rosser chain exists to prove.

**This is a fact about Lean, not about the design.**  In Lean 4,

```
structure A where
axiom foo : A
example : foo = A.mk := rfl      -- typechecks
```

typechecks, as does `example (q : P Nat Bool) : q = P.mk q.fst q.snd := rfl` at a two-field
structure in `Type`.  So const-head no-confusion is false in the *real* kernel, and
`VEnv.IsDefEq.constApp_inv` (`Verify/Typing/ConstSpine.lean:248`) is a true lemma about a
relation **strictly weaker than real definitional equality**.  Anything that used it to justify
checker behaviour was leaning on that gap.  Measured this round with `scripts/users.lean`:
`IsDefEq.constApp_inv` 4 direct / **187 transitive** users; `constApp_inv_of_patWF` 3 / 169;
`constApp_inv_of_wf` 2 / 157; `IsDefEq.church_rosser` 9 / **212**.  `DescendConstSpineK.lean:16`
names the chain it sits on: `addAxiom.WF ← … ← constApp_inv_of_patWF ← IsDefEq.constApp_inv ←
IsDefEq.church_rosser`. -/

/-- **No relation satisfies both structure eta and const-head no-confusion.**

`R` is arbitrary.  `hEta` is the one instance `MutField.structEtaSE_foo` supplies (and which any
structure-eta rule supplies, since `MutField.unitEnv_IsStructureG_0` and
`MutField.unitEnv_foo_hasType` discharge every premise of every version of the rule in this
tree).  `hNC` is `VEnv.constNoConf_of_notIsProof`'s conclusion with `IsDefEqU` replaced by `R`.
The two are contradictory. -/
theorem eta_and_constNoConf_incompatible (R : VExpr → VExpr → Prop)
    (hEta : R ((VExpr.const `MutField.foo []).mkApp []) ((VExpr.const `MutField.A.mk []).mkApp []))
    (hNC : ∀ {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
      MutField.unitEnv.RuleFreeHead c → MutField.unitEnv.RuleFreeHead c' →
      ¬ MutField.unitEnv.IsProof 0 [] ((VExpr.const c ls).mkApp as) →
      R ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as') → c = c') :
    False :=
  absurd (hNC (MutField.unitEnv_ruleFreeHead (by decide) (by decide))
      (MutField.unitEnv_ruleFreeHead (by decide) (by decide))
      MutField.unitEnv_not_isProof_foo hEta)
    (by decide)

/-- **Instantiated: const-head no-confusion is FALSE for the fourteen-constructor relation.**

Not "unproved" — refuted, at an environment with a machine-checked `VEnv.WF`
(`MutField.unitEnv_wf`).  So the repair does not merely add 136 induction cases: it *deletes*
`VEnv.IsDefEq.constApp_inv` as stated, together with `constApp_inv_of_patWF`,
`constApp_inv_of_wf` and `VEnv.constNoConf_of_notIsProof`, and every one of the 187 transitive
users has to be re-derived from a *weaker* no-confusion lemma carrying a side condition that
excludes structure constructors (or excludes unit-like types).  That side condition does not
exist anywhere in the tree today. -/
theorem constNoConf_false_for_IsDefEqSE :
    ¬ ∀ {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
      MutField.unitEnv.RuleFreeHead c → MutField.unitEnv.RuleFreeHead c' →
      ¬ MutField.unitEnv.IsProof 0 [] ((VExpr.const c ls).mkApp as) →
      (∃ A, MutField.unitEnv.IsDefEqSE 0 [] ((VExpr.const c ls).mkApp as)
        ((VExpr.const c' ls').mkApp as') A) → c = c' := fun H =>
  eta_and_constNoConf_incompatible
    (fun e₁ e₂ => ∃ A, MutField.unitEnv.IsDefEqSE 0 [] e₁ e₂ A)
    ⟨_, MutField.structEtaSE_foo⟩ (fun h1 h2 h3 h4 => H h1 h2 h3 h4)

/-! ## 7. The alternative that needs **no** new constructor, priced

`docs/design-inductive.md` §6.3 records that structure eta "cannot be added as a `VDefEq`,
because `Pattern.Matches` only matches `const`-headed spines and the rule's left-hand side is a
variable".  **The premise is right and the conclusion does not follow.**  The rule's left-hand
side is a variable only if you insist on stating the rule *pointwise*.  State it between the two
closed functions instead —

```
    (fun ps… x => x)  ≡  (fun ps… x => S.mk ps (proj₀ x) … )   :  ∀ ps…, S ps → S ps
```

— and both sides are closed `VExpr`s, so the pair is a perfectly ordinary `VDefEq` and the
existing `extra` constructor carries it.  Every pointwise instance comes back by `appDF` and
`beta`, which are already there.

`structEta_of_extra` below is that derivation, machine-checked at the zero-parameter zero-field
case (which is `isDefEqUnitLike`'s hole exactly): from `env.defeqs (etaDfZ S mk)` and the term's
type, `e ≡ S.mk : S` **using only the thirteen constructors**.  `extra`, `appDF`, two `beta`s, a
`symm` and two `trans`.

### Price comparison


| | 14th constructor (§3) | closed `VDefEq` (§7) |
|---|---|---|
| induction cases added | **136** (§1), ~20 of them needing typing arguments | **0** |
| missing commutation lemmas | 5 (`projTermG_weakN`, …) | **0** — `extra`'s `instL` case already exists |
| file split / import re-layer | 3 files (§3 end) | **0** |
| `church_rosser` | new `NormalEq`/`ParRed` rule, no rewrite orientation | `extra` case, already written |
| `constApp_inv` (187 users) | **refuted** (§6) | **refuted** (§6) — route-independent |
| `PatWF` / `PatFreeHead` | unchanged | must admit a `lam`-headed rule, or exempt these rules |
| new work in `addInduct'` | none | `D.etaRules : List VDefEq` + `VDefEq.WF` for each |
| right-hand side typeable | needed | needed (same `StructureClosed` chain) |

**The `VDefEq` route is cheaper on every line except two**, and those two are where its work
concentrates: `VEnv.PatWF` currently expects every rule in `env.defeqs` to be a `Pattern`, and a
`lam`-headed rule is not one.  That is a *localised* statement change (one predicate, plus
`patWF_of_wf`) against §1's 136 sites, and it is forced in the other route too — §6 shows
`PatFreeHead`-based no-confusion has to give either way.  `addInduct'` gaining an `etaRules` fold
mirrors the `iotaRules` fold it already performs, and `VDefEq.WF` for the eta rule is the same
projection-typing obligation the constructor's F17 clause encodes.

**What this section does not settle.**  The telescoped form (parameters, positive fields) is not written
here: `structEta_of_extra` is the zero-parameter zero-field instance.  The general schema is the
same three moves per binder (`appDF` down the parameter spine, then `beta` on both sides), and
`Theory/Inductive/Telescope.lean`'s `instAllTele`/`instTele` lemmas are what it would run on; the
`beta` chain over a telescope is the one piece of real work, and `VEnv.HasArgsDF`
(`StructureClosed.lean:500`) is the shape it wants.  Estimated at one file.  That is the number
to compare against 136. -/

/-- The zero-parameter zero-field structure-eta rule, as a `VDefEq`: `(fun x => x) ≡ (fun x => mk)`
at `S → S`.  Both sides closed, so `VEnv.IsDefEq.extra` carries it. -/
def etaDfZ (S mk : Lean.Name) : VDefEq where
  uvars := 0
  lhs := .lam (.const S []) (.bvar 0)
  rhs := .lam (.const S []) (.const mk [])
  type := .forallE (.const S []) (.const S [])

/-- **Structure eta from the *existing* thirteen constructors**, given the rule as environment
data.  No fourteenth constructor, no induction case anywhere.

`extra` fires at the closed pair, `appDF` applies both sides to `e`, and the two `beta`s collapse
the redexes to `e` and to `S.mk`.  This is the whole content of the table's "induction cases
added: 0" row. -/
theorem structEta_of_extra {env : VEnv} {U : Nat} {Γ : List VExpr} {S mk : Lean.Name} {e : VExpr}
    (hdf : env.defeqs (etaDfZ S mk))
    (hmk : env.constants mk = some ⟨0, .const S []⟩)
    (he : env.HasType U Γ e (.const S [])) :
    env.IsDefEq U Γ e (.const mk []) (.const S []) := by
  have hx : env.IsDefEq U Γ (.lam (.const S []) (.bvar 0))
      (.lam (.const S []) (.const mk [])) (.forallE (.const S []) (.const S [])) := by
    have h := VEnv.IsDefEq.extra (env := env) (uvars := U) (Γ := Γ) (ls := []) hdf nofun rfl
    simpa [etaDfZ, VExpr.instL] using h
  have h1 : env.IsDefEq U Γ (.app (.lam (.const S []) (.bvar 0)) e)
      (.app (.lam (.const S []) (.const mk [])) e) (.const S []) := by
    simpa [VExpr.inst] using hx.appDF he
  have h2 : env.IsDefEq U Γ (.app (.lam (.const S []) (.bvar 0)) e) e (.const S []) := by
    have h := VEnv.IsDefEq.beta (env := env) (uvars := U) (Γ := Γ) (A := .const S [])
      (e := .bvar 0) (B := .const S []) (.bvar (.zero ..)) he
    simpa [VExpr.inst] using h
  have h3 : env.IsDefEq U Γ (.app (.lam (.const S []) (.const mk [])) e)
      (.const mk []) (.const S []) := by
    have hc : env.IsDefEq U (.const S [] :: Γ) (.const mk []) (.const mk []) (.const S []) := by
      simpa [VExpr.instL] using
        VEnv.IsDefEq.constDF (env := env) (uvars := U) (Γ := .const S [] :: Γ)
          (ls := []) (ls' := []) hmk nofun nofun rfl .nil
    have h := VEnv.IsDefEq.beta (env := env) (uvars := U) (Γ := Γ) (A := .const S [])
      (e := .const mk []) (B := .const S []) hc he
    simpa [VExpr.inst] using h
  exact h2.symm.trans (h1.trans h3)

/-- **Anti-vacuity for §7**: the hypothesis is satisfiable and the derivation lands.  At
`MutField.unitEnv` with the rule added, the *thirteen*-constructor relation already proves
`foo ≡ A.mk` — the very instance §6 shows no-confusion cannot survive.

Note what this does and does not certify.  It certifies that the thirteen constructors suffice
*given the rule*.  It does **not** certify that the rule may be added to a well-formed
environment: `VEnv.addDefEq` is total and answers to no `VDecl.WF`, so making the rule legitimate
means extending `addInduct'` with an `etaRules` fold and proving `VDefEq.WF` for each — the
table's last-but-two row, and the alternative's real cost. -/
theorem MutField.structEta_of_extra_fires :
    (MutField.unitEnv.addDefEq (etaDfZ `MutField.A `MutField.A.mk)).IsDefEq 0 []
      (.const `MutField.foo []) (.const `MutField.A.mk []) (.const `MutField.A []) := by
  have hle : MutField.unitEnv ≤ MutField.unitEnv.addDefEq (etaDfZ `MutField.A `MutField.A.mk) :=
    ⟨id, Or.inr⟩
  exact structEta_of_extra (Or.inl rfl) (hle.constants MutField.unitEnv_Amk)
    (by simpa using (MutField.unitEnv_foo_hasType).mono hle)

/-! ## 8. The set model: verdict, with evidence

**Verdict: the set model *does* validate structure eta, and it is forced rather than chosen.**
`SetModel/UnitEtaPairing.lean`'s stated residual —

> `OracleOK` constrains a type former's denotation by **membership only**, so a model satisfying
> `InductOracleOK` may interpret a zero-field structure as a two-element set and refute eta
> outright

— **is wrong**, and the step it misses is named exactly: `InductOracleOK.consts` quantifies over
`D.allConsts`, and `allConsts` contains the **recursor** (`SetModel/EqOracle.lean`'s
`eq_allConsts` computes it: `[Eq, Eq.refl, Eq.rec]`).  The recursor's own `OracleOK.type` field
asks `o (S.rec) us ∈ interp (D.recType j).instL us`, and `recType` ends in `∀ x : S ps, motive … x`
after quantifying `motive` over the **full** set-theoretic function space — `interp`'s `forallE`
clause is `mkForallType`, `{f ∈ (⋃…)^(Gρ) ; …}`, not a definable-families subset
(`Theory/SetModel/Interp.lean:186`).  So the motive may be the *characteristic family of the
constructor*, and then an inhabitant of the recursor type exists only if every element of the
type former's denotation is the constructor's value.  That is surjective pairing, and it is a
consequence of an obligation the model already carries — no new one.

`eq_singleton_of_recProp` below is that argument, machine-checked, at zero fields: the
set-theoretic core with no `interp`, no `VInductDecl'`, no `Above`.  Read it together with
`SetModel/UnitOracleLarge.lean`, which is the same fact from the other side: its oracle sends
`Unit1 ↦ {•}` — a singleton — and closes `InductOracleOK` there, and its
`pt_not_mem_interpL_recType_of_ne` is this file's contradiction step at a domain that happens to
be a singleton already.

**What is still owed, precisely.**  Two steps, and both are bookkeeping rather than mathematics:

1. *The unfolding.*  `interp (D.recType j)` must be peeled to the shape `eq_singleton_of_recProp`
   consumes.  `SetModel/UnitOracleLarge.lean` performs exactly this peel at `unitDeclLE`
   (`interpL_motTyU`, six `mkLam_mem_mkForallType_of_dom` layers); at a general block it is
   `recType`'s telescope instead of two binders.  `mkForallType_const_eq_pow` below is the one
   general lemma that peel was missing — `mkForallType_singleton_const` only covers a singleton
   domain, which is the case being *proved* and so cannot be assumed.
2. *The `PropSplit` side condition.*  `interp (.app f a)` collapses to `pt` when
   `L.IsProof M Γ f`.  The argument needs the motive not to be classified as a proof, which
   `PropSplit`'s agreement with typing gives (a motive has type `S ps → Sort u`, not a
   proposition) but which no lemma in the tree states in that form.

**At positive fields** the same argument gives the full rule rather than the singleton: take the
family `m x = ⟦x = mk ps (proj₀ x) … ⟧` and the recursor's type forces it inhabited everywhere,
which is `SetModel/Inductive.lean`'s `mem_Ind_iff` ("no junk") read through the oracle instead of
through the fixpoint.  The model's carrier is *built* from Kuratowski tuples precisely so this
holds on the nose (`Inductive.lean:241`), and `mem_Ind₃_fibre_iff_of_zero_field` is the zero-field
half already proved.  So the model is not the obstacle; **the obstacle is §6.** -/

namespace SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **`mkForallType` with a constant codomain over a *non-empty* domain is the function space.**

The general form of `UnitAudit.mkForallType_singleton_const`, whose `G ρ = {a}` hypothesis cannot
be used here: a singleton domain is the *conclusion* of `eq_singleton_of_recProp`, so assuming it
would beg the question.  Non-emptiness is all that is needed, and the constructor supplies it. -/
theorem mkForallType_const_eq_pow {G : V → V} {hG : ℒₛₑₜ-function₁[V] G}
    {F : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {ρ Y a : V}
    (ha : a ∈ G ρ) (hF0 : ∀ v ∈ G ρ, F ρ v = Y) :
    mkForallType G hG F hF ρ = (Y ^ G ρ : V) := by
  have hFU : mkFamUnion G hG F hF ρ = Y := by
    rw [mem_ext_iff]; intro y
    rw [mem_mkFamUnion_iff]
    exact ⟨fun ⟨v, hv, hy⟩ ↦ (hF0 v hv) ▸ hy, fun hy ↦ ⟨a, ha, (hF0 a ha) ▸ hy⟩⟩
  rw [mem_ext_iff]; intro f
  rw [mem_mkForallType_iff, hFU]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun v hv y hy ↦ ?_⟩⟩
  rw [hF0 v hv]
  exact (mem_of_mem_functions h hy).2

/-- The body of the characteristic family: `{•}` at `mkv`, `∅` elsewhere.  Written with `sep`
rather than an `if` because `definability` does not see through `ite`. -/
noncomputable def charBody (mkv : V) : V → V → V := fun _ v ↦ {_z ∈ ({pt} : V) ; v = mkv}

theorem charBody_definable (mkv : V) : ℒₛₑₜ-function₂[V] (charBody mkv) := by
  suffices ℒₛₑₜ-relation₃[V] (fun T _ v ↦ T = charBody mkv ∅ v) by exact this
  have e : ∀ T ρ v : V, T = charBody mkv ρ v ↔ ∀ z, z ∈ T ↔ (z ∈ ({pt} : V) ∧ v = mkv) := by
    intro T ρ v; rw [mem_ext_iff]; simp [charBody, mem_sep_iff]
  simp only [e]; definability

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem constDom_definable (Sv : V) : ℒₛₑₜ-function₁[V] (fun _ : V ↦ Sv) := by definability

/-- **The characteristic family of `{mkv}` over `Sv`, as an element of `UProp ^ Sv`.**  This is
the motive the recursor's type obligation cannot survive unless `Sv = {mkv}`.  It is a legal
motive because `interp`'s `forallE` clause is the *full* function space. -/
noncomputable def charFam (Sv mkv : V) : V :=
  mkLam (fun _ ↦ Sv) (constDom_definable Sv) (charBody mkv) (charBody_definable mkv) ∅

theorem charFam_value {Sv mkv v : V} (hv : v ∈ Sv) :
    (charFam Sv mkv) ‘ v = {_z ∈ ({pt} : V) ; v = mkv} :=
  mkLam_value (G := fun _ ↦ Sv) hv

theorem charFam_mem_pow {Sv mkv : V} : charFam Sv mkv ∈ ((UProp : V) ^ Sv : V) := by
  refine mem_function.intro (fun p hp ↦ ?_) (fun v hv ↦ ?_)
  · obtain ⟨v, hv, rfl⟩ := mem_mkLam_iff.mp hp
    exact kpair_mem_iff.mpr ⟨hv, mem_UProp_iff.mpr sep_subset⟩
  · exact ⟨charBody mkv ∅ v, mem_mkLam_iff.mpr ⟨v, hv, rfl⟩, fun y hy ↦ by
      obtain ⟨v', hv', he⟩ := mem_mkLam_iff.mp hy
      obtain ⟨rfl, rfl⟩ := kpair_inj he; rfl⟩

/-- **Zero-field surjective pairing is *forced* in the set model.**

`H` is what `OracleOK.type` says at the recursor of a zero-field, index-free, one-constructor
block, with `interp`'s binders peeled: for every motive `m` in the motive space, every inhabitant
of `m mk`, and every `x` in the type former's denotation, the recursor's value lands in `m x`.
(At `elimLvl = .zero` the whole `recType` is propositional and the value is `•` itself, which is
the shape written here; at a large eliminator the value is a function and `pt` is replaced by
"some element of", with the same proof.)

The conclusion is that the denotation is the *singleton* `{mk}` — so any two inhabitants are
equal in the model, which is exactly what `isDefEqUnitLike` reports and what
`VEnv.UnitEta.unitLike` states in the spec.

**No `Above`, no `κ`, no chain of inaccessibles**: the argument is finite and uses only
Replacement and Power. -/
theorem eq_singleton_of_recProp {Sv mkv : V} (hmk : mkv ∈ Sv)
    (H : ∀ m ∈ ((UProp : V) ^ Sv : V), pt ∈ m ‘ mkv → ∀ x ∈ Sv, pt ∈ m ‘ x) :
    Sv = ({mkv} : V) := by
  rw [mem_ext_iff]
  intro x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (mem_singleton_iff.mp hx) ▸ hmk⟩
  have h1 : pt ∈ (charFam Sv mkv) ‘ mkv := by
    rw [charFam_value hmk]; exact mem_sep_iff.mpr ⟨by simp, rfl⟩
  have h2 := H _ charFam_mem_pow h1 x hx
  rw [charFam_value hx] at h2
  exact mem_singleton_iff.mpr (mem_sep_iff.mp h2).2

/-- **The bound the other way: the hypothesis is not vacuous and not trivially true.**  Drop the
`pt ∈ m ‘ mkv` premise and `H` becomes false at every `Sv` with an element (take `m` to be the
characteristic family of a *different* point); keep it and `H` is satisfied at `Sv = {mkv}`
itself.  So `eq_singleton_of_recProp` is a real implication at a satisfiable hypothesis. -/
theorem recProp_at_singleton {mkv : V} :
    ∀ m ∈ ((UProp : V) ^ ({mkv} : V) : V), pt ∈ m ‘ mkv → ∀ x ∈ ({mkv} : V), pt ∈ m ‘ x :=
  fun _ _ h _x hx => (mem_singleton_iff.mp hx) ▸ h

end SetModel

end Lean4Lean

/-! ## 9. Axiom bar

Nothing here introduces an axiom.

**CORRECTED 2026-09-03 — this paragraph was wrong on both counts, and both were measured.**  It
claimed `structEtaSE_foo` and `eta_and_constNoConf_incompatible` both inherit `sorryAx` through
the same four census holes.  In fact:

* `MutField.structEtaSE_foo` (cone 4217) is **hole-free** — its cone does not reach `sorryAx` at
  all, so the eta instance this file's argument rests on costs nothing;
* `eta_and_constNoConf_incompatible` (cone 5237) reaches **exactly one** hole,
  `VEnv.IsDefEqU.forallE_inv_stratified` — **not four**.

That matters for how the headline may be stated: the incompatibility is conditional on **one**
open statement, not on a four-hole cluster.  It also means "route-independent" (true of its
quantification over `R`) must not be read as "independent of the thirteen"; it is not.

**Also corrected**: §6's remark that the surviving side condition does not exist in the tree.  It
does — it is `VEnv.ConstNoConf`'s existing `IsType` guard, and `Theory/Typing/NoConfRepair.lean`
shows that guard survives eta while `¬ IsProof` does not.  The two conditions §6 offers instead
(exempt structure-constructor heads; restrict to zero-field or subsingleton structures) are both
**refuted** there, hole-free: `guard_rejects_an_axiom` (cone 382) shows *any* guard on head names
must reject an axiom inhabitant, because transitivity produces a violating pair from which the
constructor is absent.  The **model** section, the **alternative** section, the embedding and both firings are
hole-free: `after ⊆ before` on every line. -/

#print axioms Lean4Lean.VEnv.IsDefEq.toSE
#print axioms Lean4Lean.VEnv.HasArgs.toSE
#print axioms Lean4Lean.VEnv.structEtaGSE
#print axioms Lean4Lean.MutField.structEtaSE_foo
#print axioms Lean4Lean.MutField.structEtaSE_B
#print axioms Lean4Lean.eta_and_constNoConf_incompatible
#print axioms Lean4Lean.constNoConf_false_for_IsDefEqSE
#print axioms Lean4Lean.structEta_of_extra
#print axioms Lean4Lean.MutField.structEta_of_extra_fires
#print axioms Lean4Lean.SetModel.mkForallType_const_eq_pow
#print axioms Lean4Lean.SetModel.charFam_mem_pow
#print axioms Lean4Lean.SetModel.eq_singleton_of_recProp
#print axioms Lean4Lean.SetModel.recProp_at_singleton
