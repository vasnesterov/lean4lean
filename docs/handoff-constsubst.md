# Substituting a constant by a term — and the nested step, closed at a witness

New files, both `sorry`-free and green:

* **`Lean4Lean/Theory/Typing/ConstSubst.lean`** (513 lines) — the general theory.
* **`Lean4Lean/Theory/Typing/ConstSubstNested.lean`** (899 lines) — the reduction of the
  nested step's three obligations to it, and the witnesses.

One owned file edited: `Lean4Lean/Theory/Typing/Lemmas.lean` gains one lemma,
`VEnv.IsType.forallE_congr`. No frozen file was touched. `lake build` (1364 jobs, guards
included) is green; `scripts/sorry-census.lean` still reports **19**, unchanged.

Axioms: every new declaration is on `[propext, Quot.sound]`, plus `Classical.choice` where
the proof goes through `Exists.choose`, `omega` or `simp`.

---

## 0. Bottom line

| question | answer |
|---|---|
| Does `Theory/` have a constant-substitution typing theorem? | It does now: `VEnv.IsDefEq.substC`. There was none — `mono` only adds constants, `instL` does not touch the constant map. |
| Is the naive statement true? | **Yes**, with four hypotheses, one of which (`val`) is subtler than "the term has the constant's type" — §2. |
| Is it non-vacuous? | Yes, and more than asked: it is fired at both nested witnesses, and at `nfnAux` it discharges **all three** remaining obligations. |
| Does the nested wall's remaining theorem follow? | **At the witness, completely**: `nfnAux_addInductR_ordered` — the nested step preserves `VEnv.Ordered`, unconditionally, at `inductive NFn \| node : PFn NFn → NFn`. In general it reduces to "produce σ and the bridge" (§4). |
| Is the relay's "three obligations to one" right? | **No** — §7. `addInductR_ordered'` still lists three; what is true, and better, is that **all three are the same substitution**. |
| Does it generalise? | It is stated for an arbitrary partial map `CSubst := Name → Option VExpr`, which is what obligations (B)/(C) need (they substitute the auxiliary block's *constructor* and *recursor* names too). |
| What is still open? | Congruence of typing under `≈` of universe levels, and a general β-bridge for parameterised blocks. Both are discharged at the witnesses by hand; neither exists as a theorem — §6. |

---

## 1. The definition

```lean
abbrev CSubst := Lean.Name → Option VExpr

def VExpr.substC : VExpr → CSubst → VExpr
  | .const c ls, σ => match σ c with | some t => t.instL ls | none => .const c ls
  | …structural…
```

A partial map from constant names to **closed** terms; an occurrence `.const c ls` is
replaced by the value instantiated at *that occurrence's* levels. This is what makes
`substC` commute with `instL` (`VExpr.substC_instL`, no hypothesis) — the composite level
list is `VExpr.instL_instL`.

`VDefEq.substC` is the entrywise version.

---

## 2. The theorem, and why each hypothesis is there

```lean
structure CSubst.WF (σ : CSubst) (env₀ env₁ : VEnv) (U : Nat) : Prop where
  closed : σ.Closed
  const  : ∀ {c ci}, σ c = none → env₀.constants c = some ci →
             env₁.constants c = some ⟨ci.uvars, ci.type.substC σ⟩
  defeq  : ∀ {df}, env₀.defeqs df → env₁.defeqs (df.substC σ)
  val    : ∀ {c t ci Γ ls ls'}, σ c = some t → env₀.constants c = some ci →
             (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
             ls.length = ci.uvars →
             env₁.IsDefEq U Γ (t.instL ls) (t.instL ls') ((ci.type.substC σ).instL ls)

theorem VEnv.IsDefEq.substC (hσ : σ.WF env₀ env₁ U) (H : env₀.IsDefEq U Γ e1 e2 A) :
    env₁.IsDefEq U (Γ.map (VExpr.substC · σ)) (e1.substC σ) (e2.substC σ) (A.substC σ)
```

with `HasType.substC`, `IsType.substC`, `IsDefEqU.substC`, `VConstant.WF.substC`,
`VDefEq.WF.substC` as corollaries.

Each field is forced by exactly one rule of `VEnv.IsDefEq`, and each one carries
information:

* **`closed`** — forced by every binder. Without it `substC` captures, and the two
  commutation lemmas `substC_liftN` / `substC_inst` are false at the first binder.
* **`const`** — forced by `constDF`. This is the clause that constrains `env₁`: at **every**
  constant `env₀` declares outside σ's domain, `env₁` must hold it *with its own type
  substituted*. Nothing here is a caller-chosen parameter: `ci` is pinned by
  `env₀.constants c = some ci`. Dropping the `.substC σ` on the right would be the failure
  mode the relay warned about — a clause that reads like a constraint and admits environments
  with constants at unrelated types.
* **`defeq`** — forced by `extra`.
* **`val`** — forced by `constDF` in the other branch, and it is the interesting one.

### Why `val` is not "the term has the constant's type"

`constDF` relates `.const c ls` to `.const c ls'` whenever `ls ≈ ls'` **pointwise**, not
`ls = ls'`. So the substitution has to make `t.instL ls` and `t.instL ls'` *definitionally
equal*, at the constant's declared type. A hypothesis of the shape

```lean
    ht : env₁.HasType ci.uvars [] t ci.type          -- NOT enough
```

is strictly weaker, and closing the gap needs congruence of typing under `≈` of universe
levels, i.e. `HasType Γ e A → ls ≈ ls' → IsDefEq _ (e.instL ls) (e.instL ls') (A.instL ls)`.
**That theorem is not in the tree, and it is not free**: the `symm` case of the obvious
induction needs `A.instL ls ≡ A.instL ls'`, which needs `A` to be typed, which
`IsDefEq Γ e1 e2 A` does not give without `Ordered env` *and* `OnCtx Γ` — the invariant is
too strong to propagate through the induction. This is exactly the mirror trap the relay
described, met head-on; the resolution was to leave `val` as the hypothesis that says what is
actually needed rather than to strengthen the theorem's premises until it broke.

Two sufficient conditions are supplied instead:

* `CSubst.val_zero` / `val_zero'` — when the replaced constant has **no** universe parameters
  both lists are empty and `val` follows from plain well-typedness plus `IsDefEq.weak0`;
* by hand, when the value's *shape* makes `≈`-congruence available: `sortDF` and `constDF`
  are already congruences for `≈`, so a value built from sorts, constants and applications
  needs no general theorem (`ntreeVal_val`, `nfnSubstAll_WF₃`'s recursor case).

### Why the context quantifier in `val` is unrestricted

`VEnv.IsDefEq` never demands a well-formed context — `sortDF` and `constDF` have no premise
about `Γ` — so no invariant on `Γ` survives the induction, and `Γ.map (substC · σ)` is
arbitrary at the `constDF` node. For a closed value the quantifier is discharged once by
`IsDefEq.weak0`. Restricting it would have been a statement carrying less information than
its own conclusion needs.

### Dischargeability

`const` and `defeq` ask for the *substituted* type of every other constant. In the intended
use σ's domain is fresh in the environment those constants came from, so their types are
untouched. That is a theorem, not a hypothesis:

```lean
def CSubst.FreshIn (σ : CSubst) (env : VEnv) : Prop :=
  ∀ c ci, env.constants c = some ci → σ c = none

theorem VEnv.Ordered.noCSubst (H : env.Ordered) (hfresh : σ.FreshIn env) :
    env.OnTypes fun _ e A => e.NoCSubst σ ∧ A.NoCSubst σ
```

— *nothing derivable in a well-formed environment mentions a constant it does not declare*.
The analogue of `IsDefEq.closedN'` for constants; it did not exist either.

Packaged builders: `CSubst.one_WF'` (one constant, `val` a hypothesis) and `CSubst.one_WF`
(one constant, no universe parameters — `val` free).

---

## 3. What this is for: the nested step

`VEnv.addInductR_ordered'` (`Theory/Inductive/NestedOrdered.lean`) leaves three obligations:

* **(A)** the declared constructors, at their **restored** types, in `e₁ = env + typeConstsC K`;
* **(B)** the **renamed** recursors, at their restored types, in `e₂ = e₁ + ctorConstsCR R K`;
* **(C)** the **restored** ι-rules, in `e₃ = e₂ + recConstsR R`.

The finding: **all three are the same constant substitution.** Extend the restoration to the
auxiliary block's constructor and recursor names, and every restored construction is the
stored one substituted. At `nfnAux` all three bridges are `rfl`:

```lean
theorem nfnNode_substCAll  : (nfnNode.type nfnAux 0).substC nfnSubstAll
                               = nfnNode.typeR nfnAux nfnRestore 0            := rfl
theorem nfn_recType_substC_0 : (nfnAux.recType 0).substC nfnSubstAll
                               = nfnAux.recTypeR nfnRestore 0                 := rfl
theorem nfn_recType_substC_1 : (nfnAux.recType 1).substC nfnSubstAll
                               = nfnAux.recTypeR nfnRestore 1                 := rfl
theorem nfn_iotaRules_substC : nfnAux.iotaRules.map (·.substC nfnSubstAll)
                               = nfnAux.iotaRulesR nfnRestore                 := rfl
```

with

```lean
def nfnSubstAll : CSubst := fun n =>
  if n = `_nested.PFn_1     then some (.app (.const ``PFn []) (.const ``NFn []))
  else if n = `_nested.PFn_1.mk  then some (.app (.const ``PFn.mk []) (.const ``NFn []))
  else if n = `_nested.PFn_1.rec then some (.const ``NFn.rec_1 [.param 0])
  else none
```

Note the third entry: `mkAuxRecNameMap`'s *renaming* is a constant substitution too, because
`substC` replaces a constant by a **term**, and a constant is a term. That is why the general
map form (rather than one name) was worth having.

### The three general reductions

```lean
theorem VEnv.ctorConstsCR_wf_of_substC   -- (A)
theorem VEnv.recConstsR_wf_of_substC     -- (B)
theorem VEnv.iotaRulesR_wf_of_substC     -- (C)
```

Each takes: the corresponding fact for the **ordinary** block (which
`addInduct'_ordered_final` already proves — `VIndCtor.WF.constant_wf`,
`VInductDecl'.recType_isType`, `VInductDecl'.iotaRules_WF`), a `CSubst.WF` between the two
staging environments, and a *syntactic* bridge equation. Nothing about inductives is used
beyond those. **That is what is left of the nested wall in general: produce σ and the
bridge.**

---

## 4. The witnesses

Both are the elaborator-checked blocks of `Theory/Inductive/NestedBuild.lean`, so they cannot
drift from what Lean's own kernel stores.

### `NFn`/`PFn` — the block with a non-empty `ξ`, and no parameters

`inductive PFn (α : Type) | mk : α → (Prop → α) → PFn α`,
`inductive NFn | node : PFn NFn → NFn`.

`NFn` has no parameters, so `_nested.PFn_1` is replaced by a **closed application** — no
lambda, no β — and `VIndCtor.typeR` **is** `VExpr.substC` on the nose.

| name | content |
|---|---|
| `pfnDecl_WF` | **`pfnDecl.WF VEnv.empty`** — `PFn`'s block is well formed over the empty environment. Previously absent: `NestedBuild.lean` states `nfnAux_WF` over an abstract `env₂` and never proves `env₂.Ordered`. |
| `pfnEnv_ordered` | …hence the history environment really is `Ordered`, so nothing below is hypothetical. |
| `nfnNode_substC` | the bridge, `rfl` |
| `nfnNode_type_mentions_aux` | …and it substitutes something: the checked type mentions `_nested.PFn_1`, so the theorem is not being applied where nothing moves |
| `nfnSubst_WF`, `nfnSubstAll_WF₂`, `nfnSubstAll_WF₃` | the substitution at each of the three staging pairs |
| `nfnAux_obligationA` | **(A), with no hypotheses left** — the three environment hypotheses are discharged by computation |
| `nfn_recConsts_wf` | the non-nested recursor obligation at `nfnAux` (this is `addInduct'_ordered'`'s inner argument, which upstream does not expose as a lemma) |
| `nfnAux_recConstsR_wf` | **(B)** |
| `nfnAux_iotaRulesR_wf` | **(C)** |
| **`nfnAux_addInductR_ordered`** | **`∃ env₂ env', VEnv.empty.addInduct' pfnDecl = some env₂ ∧ env₂.addInductR nfnAux nfnK nfnRestore = some env' ∧ env'.Ordered`** |

The last one is the nested-soundness wall, at a real nested block, unconditionally.

What the substitution does there that no environment weakening could: the companion's ι-rule
is **keyed to `PFn.mk`**, a constant the history already holds (`iotaRulesR_major_not_fresh`,
`NestedOrdered.lean`), and its right-hand side calls **`NFn.rec_1`**, a constant the step
declares under a name the auxiliary block never had.

### `NTree`/`List` — the block **with** parameters

`_nested.List_1` has arity 1, so the value is a **lambda** and every occurrence — always
saturated, because `VIndCtor.Canonical` stores recursive fields as `∀ ξ, I_idx params π` — is
a β-redex. The substituted type and the restored type are therefore β-related, not equal, and
this is measured rather than asserted:

```lean
theorem ntreeNode_substC_redex :        -- rfl
    (ntreeNode.type ntreeAux 0).substC ntreeSubst
      = .forallE P₀ (.forallE P₁ (.forallE (.app ntreeVal (.bvar 1)) Q))
theorem ntreeNode_typeR_reduct :        -- rfl
    ntreeNode.typeR ntreeAux ntreeRestore 0
      = .forallE P₀ (.forallE P₁ (.forallE (ntreeBody.inst (.bvar 1)) Q))
```

— one β-step, in a binder domain, and nowhere else. It is absorbed by the one lemma added to
`Theory/Typing/Lemmas.lean`:

```lean
theorem VEnv.IsType.forallE_congr (henv : Ordered env) (hA : env.IsDefEq U Γ A A' (.sort u))
    (H : env.IsType U Γ (.forallE A B)) : env.IsType U Γ (.forallE A' B)
```

(the content is moving the body between the two contexts, which is `IsDefEq.defeqDFC`; it is
not `forallEDF`). With it:

* `ntreeVal_val` — `CSubst.WF.val` at `uvars = 1`, by hand, from `sortDF`/`constDF`;
* `ntreeSubst_WF` — the substitution;
* `ntreeNode_beta_bridge` — the β-step;
* **`ntreeAux_ctorConstsCR_wf`** — obligation **(A)** at the parameterised witness.

(Conditional on `env₁.Ordered` for `List`'s own block: `listDecl.WF VEnv.empty` is not proved
— see §6.)

---

## 5. Inventory

**Machine-checked, in `ConstSubst.lean`.** `VExpr.substC` and its `simp` set;
`substC_instL`, `substC_liftN`, `substC_lift`, `substC_inst`, `substC_id`; `VDefEq.substC`;
`Lookup.substC`; `CSubst.WF`; `IsDefEq.substC_constDF`, `substC_extra`, **`IsDefEq.substC`**;
`HasType.substC`, `IsType.substC`, `IsDefEqU.substC`, `VConstant.WF.substC`,
`VDefEq.WF.substC`; `VExpr.NoCSubst` and its closure lemmas, `VDefEq.NoCSubst`,
`Lookup.noCSubst`, `IsDefEq.noCSubst'`, **`Ordered.noCSubst`**, `noCSubstC`, `noCSubstD`;
`CSubst.val_zero'`, `val_zero`, `CSubst.one_WF'`, `CSubst.one_WF`.

**Machine-checked, in `ConstSubstNested.lean`.** `VEnv.ctorConstsCR_wf_of_substC`,
`recConstsR_wf_of_substC`, `iotaRulesR_wf_of_substC`; the `NFn` development listed in §4;
the `NTree` development listed in §4.

**Machine-checked, in `Typing/Lemmas.lean`.** `VEnv.IsType.forallE_congr`.

**Read off source, not machine-checked.** That a recursive field's occurrence of an auxiliary
constant is always *saturated* — it is `VIndCtor.Canonical`'s stored form, and that is why the
gap for a parameterised block is exactly β and nothing worse. It holds by `rfl` at both
witnesses; the general statement is not proved.

**Refuted this round.** Nothing. §7 corrects one claim of the relay.

---

## 6. Open, named precisely

1. **Level congruence of typing.** `HasType env U Γ e A → List.Forall₂ (· ≈ ·) ls ls' →
   IsDefEq env U' _ (e.instL ls) (e.instL ls') (A.instL ls)`. Wanted to discharge
   `CSubst.WF.val` for an arbitrary value; discharged at the witnesses by `val_zero`
   (`uvars = 0`) or by hand. The obvious induction fails at `symm` (§2); the repair needs
   `Ordered env` and `OnCtx Γ`, which are not available inside the induction.
2. **A general β-bridge.** "`substC` by `mkLams params body`, at saturated occurrences, is
   definitionally the restoration." Carried out at `ntreeAux`'s single occurrence by hand;
   there is no theorem. `IsType.forallE_congr` is the tool; what is missing is the induction
   over the constructor's telescope.
3. **`listDecl.WF VEnv.empty`**, which would make the `NTree` results unconditional the way
   `pfnDecl_WF` makes the `NFn` ones unconditional. Purely mechanical (`pfnDecl_WF` is 50
   lines; `listDecl` has two constructors and one recursive field).
4. **(B) and (C) at `ntreeAux`.** Both need items 2 and 3.
5. **The general step**, i.e. `VEnv.addInductR_ordered'` for an arbitrary `D`, `K`, `R`.
   §3's three reductions say exactly what is left: a `CSubst.WF` and a bridge, for a general
   restoration. The natural next target is to *build* σ from `VIndRestore` — `tyName`,
   `tyLvls`, `tyArgs`, `ctorName`, `recName` are precisely the data of a constant
   substitution — and to derive the bridges from `VNestedOcc` (`NestedBuild.lean`), where the
   companion member is already computed rather than asserted.

---

## 7. Corrections to the relay

* **"The nested-inductive soundness wall reduced last round from three obligations to one."**
  Measured false as stated: `VEnv.addInductR_ordered'` takes `hctors`, `hrecs` and `hrules` —
  three. What `addInductR_ordered'` discharged is the *first of four* (`typeConstsC`). The
  useful statement is the one this round establishes: the three are **one substitution
  applied at three staging environments**, and at `nfnAux` all three now hold.
* **"There is nothing of the kind in `Theory/`" (no `ConstSubst`, `substConst`,
  `replaceConst`).** Confirmed by search before writing; `HasType.mono` / `IsType.mono` indeed
  cannot remove a constant.
* **"A naive 'substituting a constant preserves typing' is probably too strong."** Half right.
  The statement is *true*; what is too strong is the naive **hypothesis** `env₁ ⊢ t : ci.type`
  — §2. No weakening of the conclusion was needed.
* **Non-vacuity.** The relay asked for the theorem to be fired at `ntreeAux_*` / `nfnAux_*`.
  Done at both, and at `nfnAux` it goes past non-vacuity to the conclusion the obligations
  exist for.
