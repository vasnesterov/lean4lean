# The companion member: what refuses it, what it costs, and what must fire

Stream deliverable for the open item at the end of `Lean4Lean/Theory/Inductive/Nested.lean`:

> **1. `addInduct'` still refuses a companion member, and that is a theorem of this file.**

Everything new is in **`Lean4Lean/Theory/Inductive/Companion.lean`** (new file, 579 lines,
**no `sorry`**, every theorem on `[propext, Classical.choice, Quot.sound]` or a subset —
several on `[propext, Quot.sound]` only, and `fooComp_not_complete` on `[propext]` alone).
No frozen file was touched. No existing file was edited. `lake build Lean4Lean.Theory`
is green with the file in place.

---

## 0. Bottom line

| question | answer |
|---|---|
| Where does `addInduct'` refuse? | `VEnv.addIndTypes`, its **first** stage — one `addConst` on the companion's own name. Machine-located by `VEnv.addIndTypes_eq_none_of_declared`. |
| Deliberate gate, unfinished case, or artefact? | **Artefact**, and load-bearing purely by accident. Proof: `fooComp_WF` — a companion block that lies about `Foo` satisfies `VInductDecl'.WF` over the environment that declared `Foo`, *because* the refusal makes `WF.ctors` vacuous. |
| Is the theorem proved? | Yes. `VEnv.addInductC` + `addInductC_eq_addInduct'` (conservativity) + `fooComp_admitted` (the block `addInduct'` returns `none` on is admitted). |
| Is it the statement that unblocks, or a weaker neighbour? | It **is** the one that unblocks the *refusal*. It is **not** enough for nested: the companion's *head* (`VInductDecl'.tyApp`) is untouched. See §5. |
| The guard? | **Three**, all currently absent: G1 re-staging, G2a type agreement, G2 constructor completeness. |
| Machine-checked negative? | Yes — `fooComp_inconsistent`: admitting the companion without G2 yields an environment that types an inhabitant of `∀ p : Prop, p`. |
| Safety-gate relay from `Verify/SafeFragment.lean` §3 | **Confirmed accurate**, and stronger than relayed: the gate is already *implemented* in `AddIndConsts`, just not wired in. See §4. |

---

## 1. The refusal, located (measured)

`Lean4Lean/Theory/Inductive/Decl.lean:655`:

```lean
def VEnv.addInduct' (env : VEnv) (D : VInductDecl') : Option VEnv := do
  let env ← env.addIndTypes D
  let env ← env.addIndCtors D
  let env ← env.addIndRecs D
  return env.addIndRules D
```

with (`Decl.lean:214,233,237`)

```lean
def VInductDecl'.typeConsts (D : VInductDecl') : List (Name × VConstant) :=
  D.types.map fun T => (T.name, ⟨D.uvars, T.type⟩)

def VEnv.addConstList (env : VEnv) (cs : List (Name × VConstant)) : Option VEnv :=
  cs.foldlM (fun env c => env.addConst c.1 c.2) env

def VEnv.addIndTypes (env : VEnv) (D : VInductDecl') : Option VEnv :=
  env.addConstList D.typeConsts
```

`typeConsts` covers **every** member of `D.types`, and `VEnv.addConst` is `none` on a
taken name. So the refusal is a single `addConst` in the *first* stage. Machine-checked:

* `VEnv.addIndTypes_eq_none_of_declared` — `T ∈ D.types` and `env.constants T.name = some ci`
  imply `env.addIndTypes D = none`.
* `VEnv.addInduct'_eq_none_of_declared` — the same for `addInduct'`
  (`Nested.lean`'s `addInduct'_no_companion` in positive form).
* At the concrete witness: `fooComp_addIndTypes_none`, `fooComp_addInduct'_none`.

### Which of the three it is: **artefact**

`addConst`'s duplicate test is a *freshness* test. It knows nothing about companions, it is
not documented anywhere as guarding against one, and `Decl.lean`'s own comment on
`addInduct'` names it for the opposite purpose — supplying "the global disjointness
invariant the `Params` orthogonality axioms need".

But it is load-bearing by accident, and this is the finding of the round:

```lean
theorem fooComp_WF : fooCompDecl.WF env₁         -- machine-checked, [propext, Quot.sound]
```

`fooCompDecl` is the block `[⟨`Foo, Prop, indices := [], ctors := []⟩]` — a companion for
`Foo` that claims **`Foo` has no constructors**, over the environment `env₁` in which
`fooDecl` really did declare `Foo` with `Foo.mk`. It satisfies `VInductDecl'.WF`. The
`ctors` field is discharged by `absurd`:

```lean
  ctors := by
    intro env₂ he
    rw [fooComp_addIndTypes_none h] at he
    exact absurd he nofun
```

`VInductDecl'.WF.ctors` is stated over `env.addIndTypes D = some env₁`, and a companion
makes that hypothesis unsatisfiable. **The whole constructor half of `WF` is vacuous at
exactly the blocks a companion clause wants to admit.** So the refusal is the only thing
standing between the spec and a false eliminator — which is why removing it without
replacement is unsound, and why the two `Nested.lean` theorems really are "the guard that
will fire".

---

## 2. The theorem, stated and proved

### The generalisation

`Companion.lean` §Part 2. A companion set is a list `K : List Name` of the block's own type
names that are *already declared*, plus a recursor renaming `rn : Name → Name` (the nested
path's `mkAuxRecNameMap`, which re-adds auxiliary recursors as
`(mkRecName mainName).appendIndexAfter i`).

```lean
def VInductDecl'.typeConstsC (D) (K) := D.typeConsts.filterMap fun c => if c.1 ∈ K then none else some c
def VInductDecl'.ctorConstsC (D) (K) := …  -- drops the constructors of companion members
def VInductDecl'.recConstsC  (D) (rn) := D.types.zipIdx.map fun (T, j) =>
                                           (rn (Lean.mkRecName T.name), ⟨D.recUvars, D.recType j⟩)
def VEnv.addIndTypesC (env) (D) (K)     := env.addConstList (D.typeConstsC K)
def VEnv.addInductC   (env) (D) (K) (rn) := (env.addConstList (D.allConstsC K rn)).map (·.addIndRules D)
```

**Why `K : List Name` and not a field on `VIndType`.** A field changes `VInductDecl'`,
which is read by `Inductive/Lemmas.lean` (191 KB), `StructureClosed.lean` (90 KB),
`DeclExamples.lean` (91 KB) and every `Verify/` and `SetModel/` consumer — files this
stream does not own. `K` is an isomorphic external encoding (a block's type names are
`Nodup` whenever the block is added at all, `VEnv.WF'.induct_allNames_nodup`), costs
nothing, and the eventual `Decl.lean` edit can carry the flag internally.

### The theorems (all proved, all in `Companion.lean`)

| name | content |
|---|---|
| `VEnv.addInductC_eq_addInduct'` | **conservativity**: `env.addInductC D [] id = env.addInduct' D` |
| `VEnv.addInductC_le` | monotone |
| `VEnv.addInductC_eq_some_iff` | succeeds iff the names it introduces are fresh and `Nodup` |
| `VEnv.addInductC_constants`, `…_constants_of_not_mem` | what it puts in the map, and what it leaves alone |
| `VEnv.addInductC_new_name` | `addInduct'_new_name`, generalised — still no name outside `allNamesC` |
| `VEnv.addInductC_type_fresh` | `addInduct'_type_fresh` for **non-companion** members |
| `VEnv.addInductC_types`, `…_recs` | the declared constants are present, at their stored types |
| `VEnv.addInductC_types_disjoint` | `Nested.lean`'s disjointness, generalised to non-companion members |

Conservativity is the load-bearing one: nothing proved about `addInduct'` in
`Lemmas.lean`, `StructureClosed.lean`, `PatternRules.lean` or `Nested.lean` is disturbed,
because at `K = []`, `rn = id` the two are the same function.

`addInductC_types_disjoint` restricted to non-companion members is not a weakness of the
proof: a companion's whole purpose is to name a type another block declared, so "at most
one block declares `J`" survives *only* if a companion is not counted as declaring it.
Exit 4's uniqueness handle (`VEnv.WF'.iota_type_uniq`) uses exactly that form.

### And it really unblocks

```lean
theorem fooComp_addInduct'_none : env₁.addInduct' fooCompDecl = none
theorem fooComp_admitted : ∃ env₂, env₁.addInductC fooCompDecl [`Foo] fooCompRec = some env₂
```

Same block, same environment: `addInduct'` refuses, `addInductC` admits. The companion
declares exactly one constant, `Foo.rec_1` (machine-checked as `fooComp_allConstsC`) —
no type constant, no constructor constants, no ι-rules.

### Plainly: is this the statement that unblocks, or a weaker neighbour?

**It is the statement that unblocks the refusal.** It is *not* by itself the statement that
delivers nested inductives; see §5. Two further honest qualifications:

1. `addInductC` lives in `Companion.lean`, alongside `addInduct'` rather than replacing it.
   Making it *the* rule means editing **files this stream does not own**:
   `Theory/VDecl.lean` (`VDecl.induct` carries only `VInductDecl'`; a companion block needs
   `(D, K, rn)`) and `Theory/Typing/Env.lean` (`VDecl.WF.induct` demands
   `env.addInduct' decl = some env'`). Those are named, not done.
2. `VInductDecl'.WF` is untouched, which is deliberate: changing it is guard G1 and it is
   *the* thing that must not be done without G2 (§3).

---

## 3. The guard: three checks, none of them present

### G1 — re-staging (`VInductDecl'.WF.ctors`)

`WF.ctors` is stated over `env.addIndTypes D = some env₁`. Under `addInductC` that
hypothesis is still false for a companion block while the extension succeeds, so the clause
becomes **genuinely** vacuous rather than harmlessly vacuous. The fix is to move it onto
`VEnv.addIndTypesC` (defined in `Companion.lean` for this purpose).
`fooComp_WF` is the machine-checked proof that the move is mandatory.

### G2a — type agreement (`CompanionSound.type_agree`)

No clause of `VIndType.WF` mentions `env.constants T.name`. `isType` says the *claimed*
type is a type; `canon` relates it to the block's own `params`/`indices`/`lvl`. Both are
satisfied by a companion reporting the wrong sort:

```lean
theorem fooComp'_WF        : fooCompDecl'.WF env₁                        -- Foo : Type, claimed
theorem fooComp'_not_sound : ¬ fooCompDecl'.CompanionSound env₁ [`Foo]   -- and Foo : Prop, really
```

G1 does not imply G2a — `fooCompDecl'` also passes the re-staged clause vacuously.

### G2 — constructor completeness (`CompanionComplete`) — **the one with the negative**

```lean
structure VInductDecl'.CompanionComplete (ds : List VDecl) (D : VInductDecl') (K : List Name) : Prop where
  ctors_complete : ∀ j T, D.types[j]? = some T → T.name ∈ K →
    ∃ D₀ j₀ T₀, VDecl.induct D₀ ∈ ds ∧ D₀.types[j₀]? = some T₀ ∧ T₀.name = T.name ∧
      T.ctors.map (·.name) = T₀.ctors.map (·.name)
```

Note the shape: it quotes the **history**, not the constants map. Two blocks sharing a type
name agree on `⟨uvars, type⟩` and on nothing else — in particular not on `ctors` — so
`env.constants` cannot express completeness. That is exactly why exit 4 routes through the
ι-rules.

It is a well-defined *check* and not an existential a liar could satisfy by picking a
different block:

```lean
theorem VEnv.WF'.companion_target_uniq :          -- proved
  VEnv.WF' ds env → VDecl.induct D₀ ∈ ds → VDecl.induct D₁ ∈ ds →
  D₀.types[j₀]? = some T₀ → D₁.types[j₁]? = some T₁ → T₀.name = T₁.name →
  D₀ = D₁ ∧ j₀ = j₁ ∧ T₀ = T₁
```

(assembled from `Nested.lean`'s `WF'.induct_eq_of_type_name` and `types_eq_of_name_eq`).

**G2 is independent of G1 and G2a**: `ctors = []` satisfies every `∀ C ∈ T.ctors, …` clause
vacuously, so no amount of re-staging catches it.

### The unsoundness G2 lets through — machine-checked

`fooCompDecl` passes `VInductDecl'.WF` (`fooComp_WF`) and `CompanionSound`
(`fooComp_sound`); the only thing wrong with it is `CompanionComplete`
(`fooComp_not_complete`). Its recursor type is (pinned by `rfl`, `fooCompDecl_recType_eq`)

```
∀ (C : Foo → Prop) (m : Foo), C m
```

— an eliminator with **no minor premises** over a type that `Foo.mk` inhabits. So:

```lean
def fooBad : VExpr :=                                    -- Foo.rec_1 (fun _ => ∀ p:Prop, p)
  .app (.app (.const `Foo.rec_1 []) (.lam (.const `Foo []) falseProp))   --            (Foo.mk (∀ p:Prop, p))
    (.app (.const `Foo.mk []) falseProp)

theorem fooComp_inconsistent {env₂ : VEnv}
    (h  : VEnv.empty.addInduct' fooDecl = some env₁)
    (h2 : env₁.addInductC fooCompDecl [`Foo] fooCompRec = some env₂) :
    ¬ env₂.Consistent
```

`VEnv.Consistent` is `Theory/Consistency.lean`'s "no closed term of type `∀ p : Prop, p`".
This is `Theory/MutualDefUnsound.lean`'s shape — a step satisfying every stated condition
and producing `falseProp` — relocated from `unsafeDef` to the companion. The base
environment is honest: `fooDecl_WF` (`DeclExamples.lean`) is a real `VInductDecl'.WF`
witness and `VEnv.empty.addInduct' fooDecl = some env₁` is `rfl`.

### The guard is not only necessary, it is *available* — where an ι-rule exists

```lean
theorem VEnv.WF'.ctors_ne_nil_of_iotaRule :        -- proved
  VEnv.WF' ds env → env.defeqs (D.iotaRule j q C) → D.types[j]? = some T →
  VDecl.induct D₀ ∈ ds → D₀.types[j₀]? = some T₀ → T₀.name = T.name → T₀.ctors ≠ []
```

i.e. exit 4 (`VEnv.WF.iota_type_uniq`, `Nested.lean`) supplies the "not fewer" direction of
G2 for every `J` that has a constructor. Applied to the witness: `fooComp_caught`.

**Its limit is exactly `Nested.lean`'s zero-constructor case.** A `J` with genuinely no
constructors contributes no ι-rule (`VInductDecl'.iotaRules_eq_nil`), so nothing fires and
the certificate must come from `recType` telescope inversion instead — the lemma exits 3 and
4 converge on. `Void1`/`T1` is the reachable witness for that, already recorded.

**A second direction G2 needs and exit 4 does not give.** `ctors_ne_nil_of_iotaRule` bounds
the companion's list from *below*. An **over**-claim — listing a constant that is not a
constructor of `J` — is not excluded by `CompanionSound.ctor_agree` either (it only asks
that the name be present at the derived type). An over-claim adds a minor premise *and an
ι-rule*, and a spurious ι-rule whose left-hand side is defeq to a real one equates two
distinct minors. The clean repair is to make G2 a **definition** rather than a check: let
the companion's `ctors` field *be* `T₀.ctors` with the instantiation substituted, so both
directions hold by construction. Recommended; not done.

---

## 4. Interaction with safety — the relay is accurate, and understated

The relayed claim ("`TrEnv'.induct` is expected to be gated to safe blocks, because
positivity is skipped when `isUnsafe`, so `VIndField.WF.pos` has no witness and
`TrEnv'.ignore` takes those declarations") checks out on all three legs, **read off
source**:

* `Lean4Lean/Inductive/Add.lean:381` — `if !isUnsafe then checkPositivity stats dom n i`,
  inside `checkConstructors`'s binder loop. Positivity really is skipped.
* `Lean4Lean/Theory/Inductive/Decl.lean` (R10 handover, and the field table row for
  `fields[i].recArg`) says exactly this, in those words, and gives it as the reason
  `TrIndDecl` is stated for safe blocks only.
* `Lean4Lean/Verify/SafeFragment.lean:52–57` says it too, attributing it to `Decl.lean`.

**Understated in one respect, which matters for this work.** The gate is not merely
"expected": it is already *written*. `Verify/Environment/Basic.lean`'s `AddIndConsts.cons`
carries `TrConstant .safe env ci ci'`, and the section header proves the consequence
(`.safe` is the top of `DefinitionSafety`, so by antisymmetry `ci.safety = .safe`). What is
missing is only the wiring: `AddInduct` still has no constructors, deliberately, because
flipping it breaks `Aligned.addInduct`, `TrEnv'.of_value`, `TrEnv'.no_inductInfo`,
`checkEqType.WF`, `addQuot.WF` and `inductiveReduceRec_eq_none` in one coordinated commit.

**Does the companion work have to respect the same gate? Yes, and it needs one clause more.**
`AddIndConsts` folds over `D.typeConsts`, `D.ctorConsts`, `D.recConsts` and demands
`m.find? n = none` *and* `env.addConst n ci' = some env₁` for every entry — so the
refinement side carries the identical refusal, and the folds must be re-pointed at
`typeConstsC` / `ctorConstsC` / `recConstsC`. Once they are:

* the `.safe` gate is checked on **every declared constant**, and a companion declares only
  its recursor;
* so the companion's target `J` and `J`'s constructors — which are *not* declared by this
  step — pass through the gate **unexamined**.

Call it **G3**. A safe block nesting through an unsafe `J` would be modelled at `.safe`
with an `unsafe` constant inside its recursor's type. In practice the checker rejects a
safe declaration mentioning an unsafe constant (`Lean4Lean/TypeChecker.lean:125-131`,
`~/lean4/src/kernel/type_checker.cpp:109-117`, and `MutualDefUnsound.lean` records the
empirical verification in every syntactic position), so G3 should be *discharged*, not
assumed — but the abstract theory models no safety tag, so the premise has to be written
down somewhere. It belongs next to `CompanionSound` on the refinement side.

---

## 5. Nested specifically — how far this goes, and what is missing

`addInductC` is the **declaration discipline** half of `docs/design-inductive.md` §9.3:
which constants a companion block declares, and under which names. That half is now done,
conservative, and it matches the implementation exactly — `fooCompRec` renames the
companion's recursor to `Foo.rec_1`, which is the shape `mkAuxRecNameMap` produces
(`Inductive/Add.lean`; `Nested.lean`'s `addInduct'_new_name` is the theorem that no
un-generalised block can introduce such a name).

**What it does *not* cover, and this is the substantive remainder: the companion's head.**
§9.3's second bullet:

> `tyApp` for a companion becomes `J.{ls} A(params) ι` instead of `.const I_j ownLvls …`.

`Decl.lean:163` has

```lean
def tyApp (j k : Nat) (args : List VExpr) : VExpr :=
  (VExpr.const (D.types.getD j default).name D.ownLvls).mkApp (bvars k D.np ++ args)
```

— the parameter block is `bvars k D.np`, a contiguous run of de Bruijn variables. For the
motivating nested example the companion for `List` must be headed `List (Tree α)`, i.e. a
*stored* instantiation `A = [Tree α]`, not the block's parameter run. So `addInductC`
alone models `_nested.List_1 α` being **skipped**, but not `_nested.List_1 α` being
**replaced by** `List (Tree α)`. Concretely:

* covered today: a companion whose parameters are exactly the block's parameters in order
  (which is what my witness is, and what a companion for a *closed* `J` looks like);
* not covered: any real `restoreNested` output, because the substitution is the point.

**The down payment already exists.** `Nested.lean`'s offset-algebra section establishes
that generalising the head does not invalidate the de Bruijn arithmetic: lifting is
`VExpr.liftN'_liftN'` and instantiation is `VExpr.instAll_liftN_of_le` (proved there), with
side condition `cut ≤ k` which every existing offset lemma already supplies
(`hni : ni ≤ K₀` in `tyApp'_instAll'`, `hij : i + j ≤ k` in `shift_atRec_tyApp`). So the
head generalisation is a rewrite of each `bvars` step into its `liftN`-of-a-stored-telescope
counterpart, under a hypothesis the caller already has — not a new theory.

**Three further nested-specific items.**

1. **Universe count.** `typeConstsC`/`ctorConstsC` drop the companion's entries, so nothing
   forces `J`'s declared `uvars` to equal `D.uvars`; `CompanionSound` demands it
   (`env.constants T.name = some ⟨D.uvars, T.type⟩`). `ElimNestedInductive` does copy the
   universe parameters, so this should be discharged, not weakened.
2. **Zero-constructor companions are reachable and are exactly where the certificate
   vanishes.** `Void1 α`/`T1` (both kernels accept; `_nested.Void1_1.ctors = []`), recorded
   in `Nested.lean`. My unsoundness witness is *itself* a zero-minor recursor, so it shows
   what the missing certificate buys: G2's residual case is not cosmetic.
3. **`BindersIndep` under the companion's substitution** — `Nested.lean`'s third open item,
   untouched here. `wDecl_WF` (`DeclExamples.lean`) remains the standing witness that the
   clause is satisfiable at the configuration where both fields of the companion
   constructor become recursive.

---

## 6. Ledger: machine-checked vs read off source

### Proved (machine-checked, no `sorry`, standard axioms)

`Lean4Lean/Theory/Inductive/Companion.lean`:

* refusal located — `VEnv.addIndTypes_eq_none_of_declared`, `VEnv.addInduct'_eq_none_of_declared`
* generalisation — `VEnv.addIndTypesC`, `VEnv.addInductC`, `VInductDecl'.{typeConstsC,ctorConstsC,recConstsC,allConstsC,allNamesC}`
* conservativity — `VEnv.addInductC_eq_addInduct'` (and the four `simp` lemmas behind it)
* structure preserved — `addInductC_le`, `addInductC_eq_some_iff`, `addInductC_constants`,
  `addInductC_constants_of_not_mem`, `addInductC_new_name`, `addInductC_type_fresh`,
  `addInductC_types`, `addInductC_recs`, `addInductC_types_disjoint`
* the guards, stated — `VInductDecl'.CompanionSound`, `VInductDecl'.CompanionComplete`
* the guards, made well-defined — `VEnv.WF'.companion_target_uniq`
* exit 4 discharging G2's lower bound — `VEnv.WF'.ctors_ne_nil_of_iotaRule`, `fooComp_caught`
* **the refusal is not a gate** — `fooComp_WF` (G1 missing), `fooComp'_WF` + `fooComp'_not_sound` (G2a missing)
* **the unblocking** — `fooComp_addInduct'_none` vs `fooComp_admitted`
* **the negative** — `fooComp_sound`, `fooComp_not_complete`, `fooComp_inconsistent`
* shape pins by `rfl` — `fooCompDecl_recType_eq`, `fooDecl_recType_eq`, `fooCompDecl_iotaRules`,
  `fooComp_allConstsC`

### Read off source, **not** machine-checked

* `Lean4Lean/Inductive/Add.lean:381` skips `checkPositivity` when `isUnsafe` (§4).
* `AddInduct` has no constructors; `AddIndConsts` carries `TrConstant .safe` (§4).
* `mkAuxRecNameMap` re-adds auxiliary recursors as `(mkRecName mainName).appendIndexAfter i`
  (`Inductive/Add.lean`); `fooCompRec` mirrors it but is not derived from it.
* `ElimNestedInductive` copies the universe parameters (§5 item 1).
* The `Tree`/`List` companion head must be `List (Tree α)` (§5) — read off
  `design-inductive.md` §9.3 and `Add.lean:747–776`, not formalised.

### Not attempted

* Any edit to `Theory/VDecl.lean` or `Theory/Typing/Env.lean` (not owned).
* Any edit to `Decl.lean`'s `addInduct'`, `VIndType`, or `VInductDecl'.WF`.
* The head generalisation itself (§5).
* Whether `env₁` is consistent — that is `leanTTConsistent`, open. `fooComp_inconsistent`
  is stated the same way `MutualDefUnsound.lean`'s `selfRef_inconsistent` is: the *result*
  is inconsistent, full stop.

---

## 7. What to pick up first

1. **Make G2 structural, not a check.** Give the companion member its constructor list *by
   construction* from the declaring block (`T₀.ctors` substituted) rather than storing and
   checking one. It closes both directions of G2 at once and removes the over-claim hazard
   §3 names. This is `soundness-ledger.md`'s exit-3 "cheaper repair" (`List VIndCtor` on
   `VIndType`, no mutual block) meeting exit 4 — and with `companion_target_uniq` and
   `ctors_ne_nil_of_iotaRule` proved, the *justification* that it is well defined is done.
2. **The `recType` telescope inversion.** Exits 3 and 4 converge on it, and it is the only
   route to a certificate at the zero-constructor companion. `mkPi_inj_of_arity`,
   `mkApp_inj_of_arity` (`Theory/Inductive/Telescope.lean`) derive the length hypothesis
   rather than assuming it, so the primitives are present.
3. **The head generalisation** (§5), with `VExpr.instAll_liftN_of_le` as the entry point.
   Do *not* start here: without item 1 it produces a spec that admits `fooCompDecl`.
4. **Then, and only then, the `Decl.lean` / `VDecl.lean` / `Env.lean` flip**, in one commit
   with G1's re-staging. `fooComp_WF` is the regression test: it must *stop* being provable
   once `WF.ctors` moves onto `addIndTypesC` and G2 lands.

Ordering rule that falls out of §3: **G1 must never land without G2.** Re-staging `WF.ctors`
onto `addIndTypesC` while `addInductC` is live and G2 is absent is precisely the
configuration `fooComp_inconsistent` refutes.
