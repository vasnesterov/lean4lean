# The companion, repaired: G1–G3 discharged, G4 found, and what nested still needs

Successor to `docs/handoff-nested-companion.md`.  That document ends with an ordering rule
("G1 must never land without G2") and a recommendation ("make G2 structural, not a check").
This round did the repair, re-ran the unsoundness witness against it, and found a fourth
guard the earlier ledger did not have.

Everything new is in **`Lean4Lean/Theory/Inductive/CompanionResolve.lean`** (new file, ~780
lines, **no `sorry`**, every theorem on `[propext, Quot.sound]` or a subset — only
`fooComp_admitted_repaired` also uses `Classical.choice`, and `VIndCtor.type_congr` /
`key_iotaRule_ne_renamed` are on `[propext]` alone).  No existing file was edited.  No frozen
file was touched.  `lake build Lean4Lean.Theory.Inductive.CompanionResolve` is green.

---

## 0. Bottom line

| question | answer |
|---|---|
| Is G2 now structural? | **Yes.** `VInductDecl'.resolveC` *replaces* every companion member by the history's own record; `resolveC_complete` proves `CompanionComplete` unconditionally. |
| Is the predecessor's reasoning for a definition correct? | **Partly, and it understated the case.** Corrected in §2. |
| Does the repair kill the unsoundness witness? | **Yes, machine-checked.** `fooComp_killed`: the false eliminator's constant equation — the *sole* premise `fooComp_inconsistent` takes from the companion — is refuted for every environment the repaired step produces. |
| Is the repair vacuous? | **No.** `fooComp_admitted_repaired`: the repaired step succeeds on the very block, declaring `Foo.rec_1` at the *honest* recursor type. |
| Is the ordering rule now a theorem? | **Yes.** `fooComp_WFC`: the witness satisfies the **re-staged** predicate (G1) too, in *every* environment. G1 alone changes nothing. |
| G2a? | **Discharged**, modulo one explicitly stated residue (`CompanionShape`) — `resolveC_sound`. |
| G3? | **Reduced to a property of the history** — `resolveC_target_safe`. No new check at the companion. |
| Anything new? | **G4**: `addInductC` renames the recursor *constant* but not the recursor inside `iotaRules`. `key_iotaRule_ne_renamed`. Not addressed by G1–G3, not fixed by resolution. |
| The zero-constructor companion? | **Discharged for the companion** (`resolveC_zero_ctors`) — emptiness is inherited, not asserted, so no ι-certificate is needed. |
| Nested head? | Down payment cashed (`tyAppH` + conservativity + three offset lemmas). The construction rewrite itself is *not* done. §6. |

---

## 1. What the repair is

```lean
def VDecl.findIndType : List VDecl → Name → Option (VInductDecl' × Nat × VIndType)
def VInductDecl'.resolveType (ds) (K) (T) : Option VIndType :=
  if T.name ∈ K then (VDecl.findIndType ds T.name).map (·.2.2) else some T
def VInductDecl'.resolveC (D) (ds) (K) : Option VInductDecl' :=
  (resolveTypes ds K D.types).map fun ts => { D with types := ts }

def VEnv.AddCompanion (ds) (env) (D) (K) (rn) (env') : Prop :=
  ∃ D', D.resolveC ds K = some D' ∧ D'.WFC env K ∧ env.addInductC D' K rn = some env'
```

**Resolve first, extend second**, and both halves quantify over the same `D'`.  A companion
member is not validated against the declaring block — it *is* the declaring block's member,
`VIndType` record and all: name, stored type, indices, constructors.  There is no field left
for a caller to lie in, and resolution *fails* (`none`) if the history declares no such type.

Conservativity is proved at both levels: `resolveC_nil : D.resolveC ds [] = some D` and
`AddCompanion_nil : AddCompanion ds env D [] id env' ↔ D.WF env ∧ env.addInduct' D = some env'`.
The second is exactly `VDecl.WF.induct`'s premise pair, so the repair adds no obligation to
and removes none from any existing declaration.

---

## 2. Correcting the predecessor's justification

The handoff argued for a definition on these grounds: exit 4
(`VEnv.WF'.ctors_ne_nil_of_iotaRule`) supplies G2's *lower* bound wherever an ι-rule exists
but no upper bound; an over-claim "merely adds a spurious ι-rule"; a definition has no gap.
Verified against the actual statements, two of those three are wrong or misleading.

* **The "lower bound" is far weaker than G2.**  `ctors_ne_nil_of_iotaRule` concludes
  `T₀.ctors ≠ []` — a statement about the **declaring** block, not about the companion's
  list.  It does not exclude a companion that drops one of `J`'s two constructors; it catches
  `fooCompDecl` only because that witness claims `[]`.  Calling it "G2's lower bound" reads
  more into it than it says.
* **The upper bound is the dangerous direction, not the lesser one.**  An over-claimed
  constructor adds a minor premise *and* an ι-rule whose left-hand side is the `iotaLhs` of a
  constructor name the environment already binds, i.e. one that can be `IsDefEq`-related to
  the genuine rule for that constructor — equating two distinct minors.  "Merely adds a
  spurious ι-rule" is the understatement.
* **The decisive reason is faithfulness, not provability.**  `restoreNested` does not *check*
  the auxiliary block's constructors against `List`'s; it **copies** them, with the parameter
  instantiation substituted.  A definition is therefore the faithful model of the
  implementation and a check is the unfaithful one, independently of which is easier to
  prove.  That is the argument this file is built on.

The conclusion — make it a definition — survives.  The reasoning offered for it did not, and
the recommendation should be read as landing for a different reason than the one given.

---

## 3. The witness, re-run (machine-checked)

`fooComp_inconsistent` (`Theory/Inductive/Companion.lean`) takes exactly **one** thing from
the companion:

```lean
hrec : env₂.constants `Foo.rec_1 = some ⟨0, fooCompDecl.recType 0⟩
```

which it feeds to `.constDF` to type `∀ (C : Foo → Prop) (m : Foo), C m`.  Everything else in
that proof (`hFoo`, `hmk`) comes from the honest `env₁` through `addInductC_le`, and survives
the repair untouched.  So killing `hrec` kills the witness, and that is what is proved:

| theorem | content |
|---|---|
| `fooComp_resolveC` | `fooCompDecl.resolveC [.induct fooDecl] [`Foo] = some fooDecl` — **by `rfl`**.  The lying block is not rejected; it is overwritten by the truth. |
| `fooComp_allConstsC_resolved` | the resolved block declares exactly `[(`Foo.rec_1, ⟨0, fooDecl.recType 0⟩)]` — the honest recursor type, with its minor premise |
| `fooDecl_recType_ne_comp` | `fooDecl.recType 0 ≠ fooCompDecl.recType 0` |
| **`fooComp_killed`** | for **every** `env₁, env₂` with `AddCompanion [.induct fooDecl] env₁ fooCompDecl [`Foo] fooCompRec env₂`: `env₂.constants `Foo.rec_1 = some ⟨0, fooDecl.recType 0⟩` **and** `≠ some ⟨0, fooCompDecl.recType 0⟩` |
| `fooComp_admitted_repaired` | non-vacuity: the repaired step *succeeds* on that block |
| `fooDecl_WFC` | non-vacuity of the re-staged predicate: the honest companion passes `WFC` at `K = [`Foo]` |

Note what is **not** claimed.  This is not a proof that the repaired `env₂` is consistent —
`VEnv.Consistent` for any nontrivial environment is `leanTTConsistent`, open.  It is the
sharp statement that the input the witness needs does not exist.  Proving `¬ HasType … fooBad`
outright would need `HasType` const-inversion (`docs/research-const-inv.md`), which was not
attempted.

---

## 4. The guards, after this round

### G1 — re-staging: installed, and proved insufficient alone

`VInductDecl'.WFC env D K` is `VInductDecl'.WF` with the `ctors` clause staged over
`VEnv.addIndTypesC` instead of `VEnv.addIndTypes`.  `WFC_nil_iff : D.WFC env [] ↔ D.WF env`
is the conservativity theorem, so the eventual `Decl.lean` edit is a no-op on everything
already proved.

**`fooComp_WFC : fooCompDecl.WFC env₁ [`Foo]`, for arbitrary `env₁`.**  This is the machine
-checked form of `handoff-nested-companion.md`'s ordering rule.  Re-staging restores the
clause's *domain* (`addIndTypesC` succeeds, adding nothing, because `Foo` is a companion) but
gives it no *content* at `ctors = []`, since `∀ C ∈ T.ctors, …` is vacuous however it is
staged.  G1 is what makes G2's constraint reachable; it is not a substitute for it, and
landing it alone is exactly the configuration `fooComp_inconsistent` refutes.

Stated here rather than by editing `VInductDecl'.WF`, because that record is read by
`Inductive/Lemmas.lean`, `StructureClosed.lean`, `DeclExamples.lean` and every `Verify/`
consumer.  **The `Decl.lean` flip is still not done** and must go in one commit with the
resolution (see §7).

### G2 — completeness: a theorem

```lean
theorem VInductDecl'.resolveC_complete : D.resolveC ds K = some D' → D'.CompanionComplete ds K
```

and the sharper form it comes from:

```lean
theorem VInductDecl'.resolveC_companion (h : D.resolveC ds K = some D')
    (hT : D'.types[j]? = some T) (hK : T.name ∈ K) :
    ∃ D₀ j₀, VDecl.induct D₀ ∈ ds ∧ D₀.types[j₀]? = some T
```

— the companion member *is* the declaring block's member.  Under-claim and over-claim are
both impossible because there is no claim.

**And the zero-constructor case falls out.**  `resolveC_zero_ctors`: a companion with
`ctors = []` is admitted only when the declaring block's member has `ctors = []`.  Exit 4's
ι-certificate vanishes exactly there (`VInductDecl'.iotaRules_eq_nil`), and the unsoundness
witness is *itself* a zero-minor recursor, so this was not a cosmetic gap.  Resolution needs
no certificate: emptiness is inherited rather than asserted.  This closes
`Theory/Inductive/Nested.lean`'s second open item **for the companion** — it does not touch
the `recType` telescope inversion that exit 3 needs for other reasons.

### G2a — type agreement: a theorem, modulo `CompanionShape`

```lean
theorem VInductDecl'.resolveC_sound (H : VEnv.WF' ds env) (h : D.resolveC ds K = some D')
    (hs : D'.CompanionShape ds K) : D'.CompanionSound env K
```

with

```lean
def VInductDecl'.CompanionShape (ds) (D) (K) : Prop :=
  ∀ D₀ j₀ T₀, VDecl.induct D₀ ∈ ds → D₀.types[j₀]? = some T₀ → T₀.name ∈ K →
    D₀.uvars = D.uvars ∧ D₀.params.length = D.params.length
```

The two conjuncts of `CompanionSound` need different things, and the difference is the
signpost for §6:

* `type_agree` needs only the **universe count**, because resolution took `T.type` verbatim
  and `WF'.constants_induct_type` says the environment holds it there.  `ElimNestedInductive`
  copies the universe parameters (read off source, **not** machine-checked), so this conjunct
  should be discharged rather than weakened.
* `ctor_agree` needs the **parameter count** as well, because `VIndCtor.type` splices the
  parameters as a de Bruijn run.  That is isolated as `VIndCtor.type_congr`, and it is
  precisely the equation the head generalisation turns into a substitution.

So `CompanionShape` is not a leftover assumption to be discharged by argument: it is the exact
statement of what the un-substituted head costs, and §6 is its removal.

### G3 — safety: reduced to the history

```lean
theorem VInductDecl'.resolveC_target_safe {Safe : VInductDecl' → Prop}
    (hsafe : ∀ D₀, VDecl.induct D₀ ∈ ds → Safe D₀) (h : D.resolveC ds K = some D')
    (hT : D'.types[j]? = some T) (hK : T.name ∈ K) :
    ∃ D₀, Safe D₀ ∧ VDecl.induct D₀ ∈ ds ∧ T ∈ D₀.types
```

`Companion.lean` §4's worry was that the `.safe` gate in `AddIndConsts.cons` examines only
*declared* constants, and a companion declares only its recursor — so `J` passes through
unexamined.  Under resolution the companion's target is not a constant recovered from
`env.constants`; it is a member of an `.induct` step of `ds`, **by construction**.  Whatever
gate the history's `.induct` steps passed, the target passed.  Nothing new needs checking at
the companion.

`Safe` is abstract because `VDecl` carries no safety tag.  On the refinement side it is "this
block was admitted by `TrEnv'.induct`", gated to `.safe` blocks — that gating is read off
`Verify/Environment/Basic.lean` and **is not machine-checked here**.

### G4 — the ι-rules are not renamed (**new**)

```lean
def VEnv.addInductC (env) (D) (K) (rn) : Option VEnv :=
  (env.addConstList (D.allConstsC K rn)).map (·.addIndRules D)
```

`rn` reaches `recConstsC` — the recursor *constants* — and stops.  `VEnv.addIndRules` takes
no renaming, and `VInductDecl'.iotaLhs` and `VInductDecl'.ihValues` both hard-code the head
`VExpr.const (Lean.mkRecName (D.types.getD j default).name) (VLevel.params D.recUvars)`.  So a
companion block **declares** `rn (mkRecName J)` and **emits its ι-rules under `mkRecName J`**.

Machine-checked core:

```lean
theorem VInductDecl'.key_iotaRule_ne_renamed (D) (j q) (C)
    (hrn : rn (Lean.mkRecName (D.types.getD j default).name)
             ≠ Lean.mkRecName (D.types.getD j default).name) :
    (D.iotaRule j q C).key ≠ [rn (Lean.mkRecName (D.types.getD j default).name), C.name]
```

with `fooCompRec_ne_mkRecName` (`by decide`) showing the hypothesis is met by the nested
path's own renaming, and `fooComp_iotaRule_misheaded` the instance.

Two consequences, neither addressed by G1–G3 and neither fixed by resolution:

1. **The companion's own recursor never reduces.**  `rn (mkRecName J)` is declared at
   `D.recType j` and appears on the left of no defeq.  The whole point of `Foo.rec_1` is that
   it computes.
2. **This block's minors are attached to another block's recursor.**  `iotaRules` ranges over
   `ctorsAll`, which includes companion members, so a companion with constructors emits rules
   keyed `[mkRecName J, C.name]` carrying *this* block's motive and minor telescopes.  Those
   are new equations about `J.rec`.

Consequence 2 is the dangerous one.  It should be caught downstream — with `D.nm ≠ 1` the
left-hand side is ill-typed against `J.rec`'s declared type, so `VDefEq.WF` fails — but
`addInductC` performs no such check and the guard list did not mention it.  **The repair is
not a check**: `rn` has to be threaded through `iotaLhs`, `ihValues` and `iotaRule` exactly as
it is through `recConstsC`.  That is the same set of definitions the head generalisation
edits, so the two belong in one change.

---

## 5. Machine-checked ledger

### Proved (no `sorry`; `[propext, Quot.sound]` unless noted)

`Lean4Lean/Theory/Inductive/CompanionResolve.lean`:

* lookup — `VInductDecl'.findType`, `findType_spec`, `VDecl.findIndType`, `findIndType_spec`
* resolution — `VInductDecl'.resolveType`, `resolveTypes`, `resolveC`, with
  `resolveType_of_not_mem`, `resolveType_name`, `resolveType_companion`, `resolveTypes_nil_K`,
  `resolveTypes_getElem`, `resolveC_fields`, `resolveC_getElem`
* conservativity — `resolveC_nil`, `VInductDecl'.WFC_nil_iff`, `VEnv.addIndTypesC_nil`,
  `VEnv.AddCompanion_nil`
* **G2** — `resolveC_companion`, `resolveC_complete`, `resolveC_zero_ctors`,
  `VEnv.AddCompanion_complete`
* **G2a** — `VInductDecl'.CompanionShape`, `VIndCtor.type_congr` (`[propext]`),
  `resolveC_sound`; supporting `VInductDecl'.mem_ctorsAll_of`,
  `VEnv.WF'.constants_induct_ctor`
* **G3** — `resolveC_target_safe`
* **G1** — `VInductDecl'.WFC`, `VEnv.AddCompanion`
* **G4** — `VInductDecl'.key_iotaRule_ne_renamed` (`[propext]`), `fooCompRec_ne_mkRecName`,
  `fooComp_iotaRule_misheaded`
* **the witness** — `fooComp_resolveC` (`rfl`), `fooDecl_recType_ne_comp`,
  `fooComp_allConstsC_resolved`, `fooComp_WFC`, `fooComp_killed`, `fooDecl_WFC`,
  `fooComp_admitted_repaired` (also `Classical.choice`)
* **the head** — `VInductDecl'.tyAppH`, `tyAppH_bvars`, `tyAppH_bvars'`,
  `map_liftN_map_liftN`, `map_instAll_map_liftN`, `liftN_tyAppH`, `instAll_tyAppH`,
  `atRec_tyAppH`

### Read off source, **not** machine-checked

* `ElimNestedInductive` copies the universe parameters (`CompanionShape`'s first conjunct).
* `restoreNested` copies rather than checks the auxiliary block's constructors, with the
  parameter instantiation substituted (`Inductive/Add.lean`, `design-inductive.md` §9.3).
* `TrEnv'.induct` is gated to `.safe` blocks; `AddIndConsts.cons` carries `TrConstant .safe`
  (`Verify/Environment/Basic.lean`) — G3's `hsafe`.
* `mkAuxRecNameMap` produces `(mkRecName mainName).appendIndexAfter i`; `fooCompRec` mirrors
  it but is not derived from it.

### Not attempted

* Any edit to `Decl.lean`, `VDecl.lean`, `Typing/Env.lean`, or `Companion.lean`.
* Threading `rn` into `iotaLhs`/`ihValues`/`iotaRule` (G4's repair).
* The construction rewrite for the generalised head (§6).
* `VIndRecArg.BindersIndep` under the companion's substitution — untouched, as before.
* Whether any resulting environment is *consistent*; that is `leanTTConsistent`, open.

---

## 6. Nested: what the head still needs

Part 9 of the file makes the target concrete:

```lean
def VInductDecl'.tyAppH (n : Name) (ls : List VLevel) (A : List VExpr) (k : Nat)
    (args : List VExpr) : VExpr :=
  (VExpr.const n ls).mkApp (A.map (·.liftN k) ++ args)
```

`A` is the stored instantiation over the block's parameters; at the use site the parameters
sit `k` binders deep, hence the entrywise weakening.  The conservativity equations

```lean
theorem tyAppH_bvars  : tyAppH (D.types.getD j default).name D.ownLvls  (bvars 0 D.np) k args = D.tyApp  j k args
theorem tyAppH_bvars' : tyAppH (D.types.getD j default).name D.selfLvls (bvars 0 D.np) k args = D.tyApp' j k args
```

pin it as a *generalisation*: at `A = bvars 0 D.np` — "the parameters, in order", which is
what every non-companion member has — it is the current head on the nose.  `Nested.lean`'s
prediction that the offset algebra survives is now checked rather than argued:

| move | lemma | side condition |
|---|---|---|
| lift past a cut below the block | `liftN_tyAppH` (from `map_liftN_map_liftN`, `VExpr.liftN'_liftN'`) | `c ≤ k` |
| saturated instantiation eats `ni` args | `instAll_tyAppH` (from `map_instAll_map_liftN`, `VExpr.instAll_liftN_of_le`) | `ιs.length = ni`, `ni ≤ k` |
| own-levels → recursor levels | `atRec_tyAppH` (from `VExpr.instL_liftN`) | none |

Both side conditions are the `cut ≤ k` that every existing offset lemma already supplies
(`hni : ni ≤ K₀` in `tyApp'_instAll'`, `hij : i + j ≤ k` in `shift_atRec_tyApp`).

**What is left, precisely.**  Threading `tyAppH` through the constructions that use `tyApp`
and `tyApp'`:

1. **A place to store `A`.**  Every use of `tyApp j k args` in `Decl.lean` reads the
   instantiation from nowhere — it *is* `bvars k D.np`.  A companion needs a per-member
   `List VExpr`.  Same choice as `K` in `Companion.lean`: an external list `As : List (List VExpr)`
   indexed like `D.types` avoids changing `VIndType`; a field is cleaner and costs a
   recompile of ~400 KB of files this stream does not own.  The external encoding is
   recommended for the same reason `K` was.
2. **The rewrites.**  `VIndRecArg.canonResult`, `VIndCtor.canonResult` (hence `VIndCtor.type`),
   `motiveType`, `recType`, `ihType`, `minorType`, `ihValues`, `iotaLhs`, `iotaType`,
   `ctorApp'` — each `bvars k D.np` step becomes its `A.map (·.liftN k)` counterpart, under
   the side condition the caller already has.  The three Part 9 lemmas are the entry points;
   the corresponding `Lemmas.lean` offset lemmas (`tyApp'_instAll`, `tyApp'_instAll'`,
   `shift_atRec_tyApp`, `liftN_atRec_tyApp`) get the same treatment.
3. **`VIndCtor.type_congr` becomes a substitution lemma.**  It currently says two blocks
   agreeing on universe count and parameter count derive the same stored constructor type.
   With a stored `A` the two sides differ by the instantiation, and `CompanionShape`'s second
   conjunct (`D₀.params.length = D.params.length`) is replaced by "the companion's `A` is a
   well-typed instantiation of `D₀.params`".  That is the *only* place `CompanionShape` is
   used, so this single change discharges the residue of G2a.
4. **G4 in the same edit.**  `iotaLhs` and `ihValues` are on both lists.
5. **`BindersIndep` under the substitution** — `Nested.lean`'s third open item, still
   untouched.  `wDecl_WF` (`DeclExamples.lean`) remains the standing satisfiability witness at
   the configuration where both fields of the companion constructor become recursive.

**Do not start at 2.**  Without §1–§4 of this document the spec admits `fooCompDecl`; with
them it does not, and `fooComp_killed` is the regression test that stays green.

---

## 7. What to pick up first

1. **G4's repair.**  Smallest, and it is a live defect in `addInductC` as it stands: thread
   `rn` through `iotaLhs`, `ihValues`, `iotaRule`, and give `addIndRules` a renamed variant.
   `key_iotaRule_ne_renamed` is the statement that must *stop* being applicable to the
   companion's own rules once it lands.
2. **The head generalisation** (§6.1–§6.3), with `tyAppH` and its three lemmas as the entry
   point.  This is the item that turns `addInductC` from "models the companion being skipped"
   into "models the companion being replaced by `List (Tree α)`".
3. **Then the `Decl.lean` / `VDecl.lean` / `Typing/Env.lean` flip**, in one commit: `WF.ctors`
   re-staged onto `addIndTypesC` (G1) *together with* resolution (G2).  `WFC_nil_iff` and
   `AddCompanion_nil` are the conservativity theorems that make the flip a no-op on existing
   proofs; `fooComp_WF` (`Companion.lean`) must *stop* being provable and `fooComp_WFC` must
   *become* unreachable, because the caller's block is no longer what gets checked.
4. **The `recType` telescope inversion** is no longer on the companion's critical path — the
   zero-constructor case is discharged by `resolveC_zero_ctors`.  It is still owed to exit 3
   for its own reasons; re-price it there, not here.

## 8. Standing ordering rule, restated

**G1 must never land without G2** — and this is now machine-checked, not argued:
`fooComp_WFC` (the witness passes the re-staged predicate, in every environment) together
with `fooComp_inconsistent` (`Companion.lean`).  With resolution in place the pair is safe;
`fooComp_killed` is the proof at the witness.
