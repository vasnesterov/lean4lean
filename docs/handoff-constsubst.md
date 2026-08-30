# The restoration as a constant substitution — σ built, and the level-congruence wall was never there

Successor to the previous revision (which named σ-construction, a β-bridge, `listDecl.WF` and
"level congruence of typing under `≈`" as the four open items).  Everything below is either
**[MC]** machine-checked in this tree (named), or **[RS]** read off source and *not* proved.

Files edited, all owned: `Lean4Lean/Theory/Typing/ConstSubst.lean`,
`Lean4Lean/Theory/Typing/ConstSubstNested.lean`.  No frozen file touched, no unowned file
touched.  `lake build` green (1365 jobs, guards included).  `scripts/sorry-census.lean`:
**19 before, 19 after**.  Every new declaration is on `[propext, Quot.sound]`, plus
`Classical.choice` where the proof goes through `simp`/`omega`/`Exists.choose`.

---

## 0. Bottom line

| question | answer |
|---|---|
| Is σ still hand-written per witness? | **No.** `VIndRestore.csubst` builds it from the five fields, and it *is* all three hand-written witness substitutions **[MC]**. |
| Is level congruence of typing under `≈` missing from the tree? | **No — the previous revision was wrong.**  It is `VEnv.IsDefEq.instL_r` (`Theory/Typing/Strong.lean`), sorry-free, on `[propext, Quot.sound]`.  §2. |
| So what does `CSubst.WF.val` actually need? | The **naive** hypothesis after all: the value has the constant's substituted type, in an `Ordered` target environment.  `CSubst.WF_of_hasType` **[MC]**.  Both hand-built `≈`-congruences are deleted. |
| Is the *syntactic* bridge true in general? | **No, and it is now refuted, not merely unproved**: `ntreeNode_substC_ne_typeR`, by `decide`, at a real parameterised block **[MC]**. |
| What replaces it? | A **telescope defeq** bridge: `VEnv.TeleDefEq`, `IsType.mkPi_congr'`, and `VEnv.ctorConstsCR_wf_of_substC'` — fired at `ntreeAux`, where the whole block-specific input is one `IsDefEq.beta` **[MC]**. |
| Is `listDecl.WF VEnv.empty` proved? | **Yes** **[MC]**, so the `NTree` development is unconditional: `ntreeAux_obligationA`. |
| Is the general nested `Ordered` theorem proved? | **No.**  Obligation (A) is general modulo a per-block telescope defeq; (B) and (C) are still witness-only, and only at `NFn`.  §5 names the exact remaining step. |

---

## 1. σ from `VIndRestore`'s five fields

`VIndRestore` carries `tyName`, `tyLvls`, `tyArgs`, `ctorName`, `recName`.  Member `j` is
*presented* as `R.tyName j |>.{R.tyLvls j} (R.tyArgs j)` with `R.tyArgs j` a telescope over
the block's own parameters, so the term the constant stands for is that application
abstracted over `D.params`:

```lean
def VIndRestore.tyVal   (R) (D) (j)   : VExpr := mkLams D.params ((.const (R.tyName j) (R.tyLvls j)).mkApp (R.tyArgs j))
def VIndRestore.ctorVal (R) (D) (j) C : VExpr := mkLams D.params ((.const (R.ctorName C.name) (R.tyLvls j)).mkApp (R.tyArgs j))
def VIndRestore.recVal  (R) (D) (n)   : VExpr := .const (R.recName n) (VLevel.params D.recUvars)

def VIndRestore.csubst   (R) (D) (K) : CSubst      -- type + ctor + recursor entries
def VIndRestore.csubstTy (R) (D) (K) : CSubst      -- the type entries alone
```

Two design points, both load-bearing:

* **One σ covers both universe numberings.**  A block head occurs at `D.ownLvls` inside
  `tyApp`/`ctorApp` and at `D.selfLvls` inside `tyApp'`/`ctorApp'`/the recursor.  `substC`
  instantiates the value at *the occurrence's* levels (`substC_const_some`), and `instL`
  distributes over `mkLams`/`mkApp`, so `csubst` produces `tyAppR` in the first case and
  `tyAppR'` in the second with no second substitution.  This is why `substC_instL` was the
  right primitive.
* **The domain is guarded by `K`, not by "is a block name".**  Off `K`, `VIndRestore.OwnId`
  says the restoration renames nothing, so an entry there would be an **η-expansion**
  (`mkLams params (I.{ownLvls} (bvars 0 np))`), not the identity.  Machine-checked negative
  controls: `nfn_csubst_own_none`, `nfn_csubst_ownRec_none`, `ntree_csubstTy_own_none` — all
  `rfl`.

### It builds the witnesses, not something that resembles them

| **[MC]** | statement |
|---|---|
| `nfn_csubstTy` | `nfnRestore.csubstTy nfnAux nfnK = nfnSubst` |
| `nfn_csubst` | `nfnRestore.csubst nfnAux nfnK = nfnSubstAll` — *including* the recursor rename, which is `mkAuxRecNameMap`'s entry read off `R.recName` |
| `ntree_csubstTy` | `ntreeRestore.csubstTy ntreeAux ntreeK = ntreeSubst` — here `tyVal`'s `mkLams` really is a lambda, because `NTree` has a parameter |
| `ntree_csubst_ty_val` | `… `_nested.List_1 = some ntreeVal`, by `rfl` |
| `csubst_closed`, `csubstTy_closed` | closedness from two hypotheses: the parameter telescope is closed, and each presented spine mentions no variable beyond the parameters |
| `nfn_csubst_closed`, `ntree_csubstTy_closed` | …discharged at both witnesses |

Every existing result stated against `nfnSubst` / `nfnSubstAll` / `ntreeSubst` therefore holds
verbatim of the general σ, by rewriting along these equations.

---

## 2. The correction: level congruence is in the tree

The previous revision's §6 item 1 said:

> **Level congruence of typing.** `HasType env U Γ e A → List.Forall₂ (· ≈ ·) ls ls' → IsDefEq …`
> … **That theorem is not in the tree, and it is not free**: the `symm` case of the obvious
> induction needs `A.instL ls ≡ A.instL ls'`, which needs `A` to be typed, which
> `IsDefEq Γ e1 e2 A` does not give without `Ordered env` *and* `OnCtx Γ`.

The diagnosis was right and the conclusion was wrong.  The theorem is
**`VEnv.IsDefEq.instL_r`**, `Theory/Typing/Strong.lean`:

```lean
theorem IsDefEq.instL_r (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U'))
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls')
    (H : env.IsDefEq U' Γ e1 e2 A) :
    env.IsDefEq U (Γ.map (VExpr.instL ls)) (e1.instL ls) (e2.instL ls') (A.instL ls)
```

`#print axioms` — `[propext, Quot.sound]` **[MC]**.

It exists for exactly the reason the previous revision said it could not: the repair that
"has worked twice" *is* what `Strong.lean` does.  `VEnv.IsDefEqStrong` is `IsDefEq` with the
missing typing premises added at `bvar`, `constDF`, `appDF`, … ; the induction runs there;
`VEnv.Ordered.strong : Ordered env → OnTypes env (EnvStrong env)` is the bridge, and
`EnvStrong`'s **third clause is literally this statement for closed terms**.  `Ordered env` and
`OnCtx Γ` sit in the public statement, which is where the previous revision said they had to
sit — they were already there.

### What that buys

```lean
theorem CSubst.val_of_hasType (henv₁ : env₁.Ordered)
    (ht : env₁.HasType ci.uvars [] t (ci.type.substC σ)) : … val …

theorem CSubst.WF_of_hasType (henv₁ : env₁.Ordered) (hcl : σ.Closed)
    (hval : ∀ {c t ci}, σ c = some t → env₀.constants c = some ci →
              env₁.HasType ci.uvars [] t (ci.type.substC σ))
    (hconst …) (hdefeq …) : σ.WF env₀ env₁ U

theorem CSubst.one_WF_of_hasType …    -- the one-constant case, no universe hypothesis
```

So `CSubst.WF`'s `val` clause is discharged by **plain well-typedness of the value**, given
`Ordered env₁` — precisely the hypothesis the previous revision called "strictly weaker and
**not enough**".  It is enough.  `CSubst.val_zero`, `val_zero'` and `CSubst.one_WF` are now
special cases and are kept only because existing proofs cite them.

Two hand-built `≈`-congruences were **deleted as unnecessary**:

* `ntreeSubst_WF` now calls `one_WF_of_hasType` with `by type_tac` where it previously called
  `ntreeVal_val` (≈30 lines of `sortDF`/`constDF` congruence by hand).  `ntreeVal_val` is kept
  above it as the measurement it was.
* `nfnSubstAll_WF₃`'s recursor case — the one value in either witness with a universe
  parameter — is now `CSubst.val_of_hasType hFo (…constDF…)`; the `match ls, hlen with | [l]`
  destructuring is gone.

---

## 3. The syntactic bridge is false, and what replaces it

`VEnv.ctorConstsCR_wf_of_substC` (previous round) needs
`(C.type D j).substC σ = C.typeR D R j` **on the nose**.  At `D.np = 0` that holds; at
`D.np > 0` the restoration replaces a companion constant by a `mkLams`, every occurrence is
saturated, and the two sides differ by one β-step per parameter per occurrence.

**[MC]** `ntreeNode_substC_ne_typeR : (ntreeNode.type ntreeAux 0).substC ntreeSubst ≠ ntreeNode.typeR ntreeAux ntreeRestore 0`
— by `decide`.  Not "unproved": refuted, at `inductive NTree (α) | node : α → List (NTree α) → NTree α`.

The replacement is a **telescope defeq**:

```lean
inductive VEnv.TeleDefEq (env) (U) : List VExpr → List VExpr → List VExpr → Prop
  | nil  : env.TeleDefEq U Γ [] []
  | rfl  : env.TeleDefEq U (A::Γ) As As' → env.TeleDefEq U Γ (A::As) (A::As')
  | cons : env.IsDefEq U Γ A A' (.sort u) →
           env.TeleDefEq U (A::Γ) As As' → env.TeleDefEq U Γ (A::As) (A'::As')

theorem VEnv.IsType.mkPi_congr  (henv : Ordered env) : TeleDefEq … → IsType Γ (mkPi As B) → IsType Γ (mkPi As' B)
theorem VEnv.IsType.mkPi_congr' (henv : Ordered env) : TeleDefEq … → IsDefEq (As.reverse ++ Γ) B B' (.sort v) →
                                                        IsType Γ (mkPi As B) → IsType Γ (mkPi As' B')
theorem VExpr.substC_mkPi : (mkPi As B).substC σ = mkPi (As.map (·.substC σ)) (B.substC σ)

theorem VEnv.ctorConstsCR_wf_of_substC'   -- obligation (A), defeq bridge
```

`TeleDefEq.rfl` is the design point: without it the caller would have to supply a reflexivity
derivation for every entry it is **not** touching, i.e. re-type the whole telescope.  With it,
obligation (A) at `ntreeAux` reads

```lean
    refine ⟨.succ (.param 0), .rfl (.rfl (.cons (u := .succ (.param 0)) ?_ .nil)), by type_tac⟩
    refine VEnv.IsDefEq.beta … <;> type_tac
```

— the entire block-specific content is **one `IsDefEq.beta`**.  `ntreeAux_ctorConstsCR_wf` is
now proved this way rather than through the bespoke `ntreeNode_beta_bridge` (which is kept, as
the hand computation it supersedes).

---

## 4. `listDecl.WF VEnv.empty`, and the parameterised witness unconditional

**[MC]** `listDecl_WF : listDecl.WF VEnv.empty`.  Unlike `pfnDecl`, `listDecl` has a
**recursive** field, so `VIndField.WF.pos` is reached in its `some r` branch and all nine of
its clauses are discharged (`binders_indep` is reached with an earlier recursive field and
`ξ = []`, the `mutDecl_WF` rung).

Downstream, all **[MC]**: `listEnv_ordered`, `ntree_fresh'`, `ntreeAux_staged_exists`,
`ntreeAux_declared_exists`, and

```lean
theorem ntreeAux_obligationA :
    ∃ env₁ env₂ env₃, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ ∧
      ∀ c ∈ ntreeAux.ctorConstsCR ntreeRestore ntreeK, VConstant.WF env₃ c.2
```

with no hypotheses — the parameterised counterpart of `nfnAux_obligationA`.

Unchanged and still true: **`nfnAux_addInductR_ordered`**, the nested step preserving
`VEnv.Ordered` unconditionally at `inductive NFn | node : PFn NFn → NFn` **[MC]**.

---

## 5. Open, named precisely

1. **(B) and (C) at `ntreeAux`.**  The gap is *not* level congruence any more, and *not* the
   congruence half of the β-bridge (§3).  It is:
   * (B): the same `mkPi_congr'` instantiation for `recTypeR`.  `recType j` is
     `mkPi (atRecTele params ++ motives ++ minors ++ liftTele … indices) (…)`; four entries of
     that telescope mention `_nested.List_1` (motive 1, and the two `_nested.List_1`
     minors' field telescopes and `ctorApp'`s), so it is four `IsDefEq.beta`s in
     progressively deeper contexts rather than one.  Nothing new is needed; it is volume.
     The reduction lemma `recConstsR_wf_of_substC'` is **not written** — deliberately: it would
     be an unfired general statement, and this stream's failure mode is exactly that.
   * (C): `VDefEq.WF` transports `lhs`, `rhs` **and** `type`.  `type` is a `mkPi` and is
     covered.  `lhs`/`rhs` are `mkLams`, and **there is no `mkLams` congruence** —
     `IsType.mkPi_congr'`'s proof uses `IsType.forallE_inv`, whose λ-analogue is
     `HasType.lam_inv` (`Theory/Typing/Strong.lean`, available, needs `OnCtx Γ`).  That is the
     one missing lemma for (C).
   * Both also need `(ntreeRestore.csubst ntreeAux ntreeK).WF` at the constructor and recursor
     staging pairs, which by §2 is now just "each of the four values is well typed at its
     substituted stored type".
2. **The general n-ary β step.**  `mkApp (mkLams D.params V) (bvars k D.np) ≡ V` lifted —
   i.e. `tyApp` substituted is `tyAppR` up to `D.np` β-steps.  At `np = 1` this is one
   `IsDefEq.beta`, done.  The general form needs an induction over the parameter telescope in
   which each intermediate application is typed; `IsDefEq.beta`'s premises are
   `A::Γ ⊢ e : B` and `Γ ⊢ e' : A`, so the induction has to carry the split of the value's
   own pi-type — that is the exact missing step, and it is where `HasType.app_inv` /
   `HasType.lam_inv` (both available in `Strong.lean`) come in.
3. **The general σ's `WF`.**  With §2 this is: for each companion member `j`,
   `env₁ ⊢ R.tyVal D j : (T.type).substC σ`, and likewise for `ctorVal`/`recVal`.
   `VIndRestore.Faithful.ty_agree` says `R.instAt D (npJ j) j ci.type = T.type` where `ci` is
   the *declared* constant — i.e. the fact is available; turning it into a `HasType` of the
   `mkLams` form is "apply a constant to its parameter spine and re-abstract", which is the
   same telescope machinery as item 2.  **[RS]** — this is read off `Faithful`, not proved.
4. **`VIndRestore.KeysDistinct` derivable rather than assumed** — unchanged, blocks nothing.
5. **The general step** `VEnv.addInductR_ordered'` for arbitrary `D`, `K`, `R`: items 1–3.

**Removed from this list since the previous revision:** level congruence (§2, it exists);
`listDecl.WF VEnv.empty` (§4, proved); "produce σ" (§1, it is a definition now); and (A) at
the parameterised witness (§3–4, unconditional).

---

## 6. The gate list

`docs/handoff-inductive-add.md` §N is the list this feeds.  Update to row (i) only; **no flip
was attempted**, per the standing ruling.

| gate | status |
|---|---|
| (i) the nested-soundness theorem | **still open**, and now decomposed: (A) general modulo a per-block telescope defeq **and unconditional at both witnesses**; (B), (C) witness-only and only at `NFn`.  The sub-blockers are §5 items 1–3 — all telescope volume, no missing metatheory |
| (ii) the `DeltaUnique` repair | CLOSED (unchanged) |
| (ii′) `VIndRestore.KeysDistinct` | open, blocks nothing (unchanged) |
| (iii) the `inductNested` rule and case arms | gated on (i) (unchanged) |
| (iv) the nine `Verify/TypeChecker/` placeholders | **the human's standing ruling: they stay.**  Reported, not acted on |
| (v) the shape strengthenings | CLOSED (unchanged) |
| (vi) `IsStructure.types` | open, other stream (unchanged) |

Row (i) did **not** close, so the `AddInduct` flip is not landable and was not attempted.
What changed is its character: after this round every remaining sub-obligation is a
*telescope* computation in an environment already known to be `Ordered`, with every piece of
metatheory it needs (`instL_r`, `mkPi_congr'`, `forallE_inv`, `lam_inv`, `app_inv`, `beta`)
present and sorry-free.

---

## 7. Inventory

**Machine-checked, new in `Theory/Typing/ConstSubst.lean`.**  `CSubst.val_of_hasType`,
`CSubst.WF_of_hasType`, `CSubst.one_WF_of_hasType`.  (Import added:
`Lean4Lean.Theory.Typing.Strong`.)

**Machine-checked, new in `Theory/Typing/ConstSubstNested.lean`.**
`VEnv.TeleDefEq`; `VEnv.IsType.mkPi_congr`, `mkPi_congr'`; `VExpr.substC_mkPi`;
`VEnv.ctorConstsCR_wf_of_substC'`;
`VIndRestore.tyVal`/`ctorVal`/`recVal`/`csubstTyList`/`csubstList`/`csubstTy`/`csubst`,
`List.lookup_mem`, `mem_csubstList_closed`, `csubst_closed`, `csubstTy_closed`;
`list_const_staged`, `listDecl_WF`, `listEnv_ordered`;
`ntreeNode_substC_ne_typeR`; `ntree_fresh'`, `ntreeAux_staged_exists`,
`ntreeAux_declared_exists`, `ntreeAux_obligationA`;
`nfn_csubstTy`, `nfn_csubst`, `nfn_csubst_own_none`, `nfn_csubst_ownRec_none`,
`ntree_csubstTy`, `ntree_csubst_ty_val`, `ntree_csubstTy_own_none`,
`nfn_csubst_closed`, `ntree_csubstTy_closed`.

**Machine-checked, re-proved.**  `ntreeSubst_WF` (through `one_WF_of_hasType`),
`ntreeAux_ctorConstsCR_wf` (through `ctorConstsCR_wf_of_substC'`), `nfnSubstAll_WF₃`'s
recursor `val` case (through `val_of_hasType`).

**Refuted this round.**  The syntactic bridge for a parameterised block
(`ntreeNode_substC_ne_typeR`).  And the previous revision's claim that level congruence is
absent from the tree — §2.

**Read off source, not machine-checked.**  §5 item 3 (that `Faithful.ty_agree` supplies the
typing the general σ's `WF` needs).  Also, still: that a recursive field's occurrence of an
auxiliary constant is always *saturated* — it is `VIndCtor.Canonical`'s stored form; it holds
by `rfl` at both witnesses, and the general statement is still not proved.

---

## 8. Corrections to the relay

* **"Level congruence of typing under `≈` — the hard one.  The naive induction fails at
  `symm`."**  The diagnosis is right; the premise that it is *open* is **false**.
  `VEnv.IsDefEq.instL_r` has been in `Theory/Typing/Strong.lean`, sorry-free, and the fix the
  relay described ("weaken until it survives the structural step and keep the strong
  hypothesis in the public statement") is precisely what `IsDefEqStrong` + `Ordered.strong`
  already implement.  Cost of the miss: two hand-built congruence proofs in the previous
  round, both now deleted.  **The lesson is the relay's own, one level up: audit what the tree
  already proves before deciding a statement is open.**
* **"Parameterised blocks cost exactly one β-step, measured."**  True *for
  `ntreeNode`* — one occurrence, one parameter.  It is one β-step **per occurrence per
  parameter**; `ntreeAux.recType` has four occurrences (§5 item 1).  The measurement was of
  obligation (A), not of the block.
* **"With the general theorem, the `AddInduct` flip's obligation (i) closes."**  The general
  theorem was not obtained, so (i) did not close.  §6 says what did.
* **"`listDecl.WF VEnv.empty` — mechanical."**  Correct; it went through essentially first
  try, modelled on `pfnDecl_WF` plus `mutDecl_WF`'s recursive-field rung.
