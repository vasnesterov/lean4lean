# Working backwards from `kernel_sound`

**Scope.** `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` read in full (frozen,
not edited). `Verify/Bridge.lean`, `Theory/Consistency.lean`, `Theory/Equiconsistency.lean`,
`Theory/Typing/{Basic,Env,UniqueTyping,RawDefEq,Injectivity}.lean`,
`Theory/SetModel/{Interp,InterpSound,SoundInduction,PropSplitAudit,LevelAssignUnsat}.lean`,
`PLAN.md`, `docs/{handoff-stratified,thesis-architecture,model-interface,soundness-ledger,logrel-scope,options-circularity-breakers}.md`.
One machine-checked cone scan over the import closure of `Verify/Bridge.lean` (§3).

Nothing here re-attempts a closed route. The closed routes are listed and checked against in §8.

---

## 0. The answer, first

**There is a statement that is sufficient for `kernel_sound`, it is not one of the six refuted
things, and it is strictly less than what the project currently plans to prove.**

> **`PropTypeAgree env 0`** — *for a term with two types, both types are propositions or neither*,
> stated at **zero universe parameters**:
> ```lean
> ∀ {Γ e A A' u u' ls}, u.WF 0 → u'.WF 0 →
>   env.HasType 0 Γ e A → env.HasType 0 Γ e A' →
>   env.HasType 0 Γ A (.sort u) → env.HasType 0 Γ A' (.sort u') →
>   (u.eval ls = 0 ↔ u'.eval ls = 0)
> ```
> (`Theory/SetModel/PropSplitAudit.lean:119`, at `nv := 0`.)

The plan says the model needs **two** statements — `PropUniq ∧ PropTypeAgree`
(`PropSplitAudit.propSplitOf`, and `model-interface.md` §5, which records `PropUniq` as
irreducible after the "minimum convention" repair failed). The backward reading says the second
is free, for a reason that only appears when you start from the theorem:

> **`kernel_sound` hands you a proof of `False` before you have to interpret anything.**
> Its hypothesis `hfalse` is discharged *into* the proof, so the whole model construction runs
> with an inhabitant of **every proposition** in scope. `PropUniq` is a statement about types
> that are propositions — and in that environment every one of them is inhabited, which is
> exactly the extra premise `PropTypeAgree` needs. Under `hfalse`, `PropTypeAgree ⟹ PropUniq`.
> (§6; analysis, ~20 lines of Lean, row-zero named in §9.)

The second finding is negative and equally load-bearing:

> **`IsDefEq.uniq` is genuinely required by `kernel_sound` as the tree stands, and it is required
> by `Verify/`, not by the model.** Machine-checked cone scan (§3): in the import closure of
> `Verify/Bridge.lean` the injectivity family reaches the goal through exactly one door, and
> `sort_inv` has exactly **one** direct consumer, `IsDefEq.uniq`. But the door is a *statement
> shape*, not a mathematical fact: every one of the 174 declarations in that cone reaches
> `sort_inv` through `IsDefEqU.trans` / `.of_l` / `.of_r` / `.defeqDF`, all four of which are
> **rules** in the reference's three-place judgment and **theorems** here. `Theory/` is free
> machinery; `kernel_sound` does not make that choice. §5 names the enlargement that removes it
> and prices what it does *not* remove.

And the answer to the question the task posed most sharply:

> **No, `kernel_sound` cannot avoid interpreting everything.** §7 gives the two arguments — the
> collapse of proofs is forced by cardinality, and data cannot be collapsed because of large
> elimination into `Prop` (`Nat.rec (motive := fun _ => Prop)`). Both are cheap and both are new
> here. "Soundness only at `Prop`" is refuted; "a model of the fragment a `False`-proof lives in"
> is the whole theory.

---

## 1. What `kernel_sound` asserts, quoted

`Lean4Lean/Verify/Soundness.lean:185–191`:

```lean
theorem kernel_sound (ds : List Declaration) (fuel : FuelConfig)
    (env : Kernel.Environment)
    (hok : foldAddDecl fuel (stdPrelude ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Declaration.IsAxiomFree d)
    (hfalse : ContainsSafeProofOfFalse env) :
    Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰
```

with (`:154`, `:161`, `:166`, `:170`)

```lean
def foldAddDecl (fuel) (ds) := ds.foldlM (fun env d => addDecl env d (check := true) (fuel := fuel))
                                          (Kernel.Environment.empty `main)
def Declaration.IsAxiomFree : Declaration → Prop | .axiomDecl _ => False | _ => True
def falseExpr : Expr := .forallE `p (.sort .zero) (.bvar 0) .default
def ContainsSafeProofOfFalse (env) : Prop :=
  ∃ n ci, env.find? n = some ci ∧ ci.isUnsafe = false ∧ ci.isPartial = false ∧
    ci.levelParams = [] ∧ ci.type = falseExpr
```

**Class of environments and declarations.** Every `env : Kernel.Environment` reachable by running
the *executable* `Lean4Lean.addDecl` with `check := true` from `Kernel.Environment.empty` over
`stdPrelude ++ ds`, at **any** `fuel`, where `ds` contains no `.axiomDecl` and is otherwise
unrestricted — definitions, theorems, opaques, inductives (nested included), mutual blocks, and
`unsafe`/`partial` declarations are all permitted. `stdPrelude` is seven explicit `Declaration`
literals (`Eq`, `Iff`, `propext`, `.quotDecl`, `Quot.sound`, `Nonempty`, `Classical.choice`),
pinned to this toolchain's actual declarations by a build-time `#eval`.

**Five things the statement does *not* say, each of which is a real economy:**

1. **`VEnv` occurs zero times.** The statement is over `Kernel.Environment`, `Declaration`, and
   Foundation's `Entailment.Inconsistent`. The abstract type theory is *entirely* proof
   machinery; every judgment in `Theory/` may be redesigned without touching the goal.
   (Confirmed by the frozen file's imports: `Lean4Lean.Environment` and
   `Foundation…InaccessibleCardinal` only.)
2. **Only one direction of the equiconsistency is needed.** `Theory/Equiconsistency.lean:45`
   states an `↔`; `kernel_sound` needs only `Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent`,
   contraposed. The (→) half — building models of ZFC inside Lean TT — is not on the path.
   `PLAN.md:174` already records this.
3. **Only the `.safe` model is needed** (`Bridge.lean:236,249`: `TrEnv .safe`). A
   `partial`/`unsafe` block contributes nothing to it. Recorded already in
   `handoff-stratified.md` §14.6; restated here because it is a *hypothesis* economy on the
   `Verify/` side, not a conclusion economy.
4. **The `False` witness is pinned to one syntactic form** — safe, `levelParams = []`, type
   *literally* `∀ p : Prop, p`. `Bridge.trExprS_falseExpr_inv` and `Bridge.hasType_falseProp`
   already discharge the transport, unconditionally and sorry-free.
5. **`fuel` is universally quantified**, so no fuel-dependent reasoning is available or needed;
   `Bridge.addDeclWF` already covers every setting.

**The conclusion is `Σ₁`, not a truth claim.** `Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰` is
`𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 ⊢ ⊥`. The intended route reaches it classically: assume `Consistent`, get a model by
Foundation's completeness (`SetTheory.provable_of_models`, `PLAN.md:28–36`), interpret, contradict.
So **the working hypotheses available inside the proof are two: a model `M ⊧ 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`, and
`hfalse`.** §6 is about the second one, which nobody has used.

---

## 2. The chain, as the tree actually has it

`kernel_sound` is `sorry`. Its intended discharge is `Bridge.not_leanTTConsistent_of_kernel_proves_false`
(`Verify/Bridge.lean:245`) composed with `leanTTConsistent` and Foundation's completeness.
Reading the Bridge rather than the plan:

| link | statement | status |
|---|---|---|
| refinement | `foldAddDecl fuel ds = .ok env → ∃ venv, TrEnv .safe env venv ∧ venv.WF` | `Bridge.foldAddDecl_tr`, **proved**, but `sorryAx`-tainted through `addDecl.WF` |
| prelude bookkeeping | `PreludeBridge` — the result is `VEnv.LeanWF` | **hypothesis**; blocked on the inductive keystone (`AddInduct` has no constructors) |
| `False` transport | `ContainsSafeProofOfFalse env → ∃ e, venv.HasType 0 [] e falseProp` | `Bridge.hasType_falseProp`, **proved, sorry-free**, axioms `[propext, Classical.choice, Quot.sound, 3 PHashMap axioms]` |
| consistency | `leanTTConsistent : ∀ env, env.LeanWF → ¬∃ e, env.HasType 0 [] e falseProp` | open; the whole of link 2 |
| discharge | completeness ⟹ `Inconsistent` | mechanical, not started |

Machine-checked, this session: `collectAxioms Lean4Lean.Bridge.not_leanTTConsistent_of_kernel_proves_false`
= `[propext, sorryAx, Classical.choice, Quot.sound]` + the 27 frozen `Verify/Axioms.lean` axioms
that Guard check 2 whitelists — i.e. **the Bridge export's only non-whitelisted content is
`sorryAx`, inherited from `addDecl.WF`.** No axiom outside the whitelist has crept in.

**Two obligations are on the critical path and are independent of everything in this document:**
the inductive keystone (`AddInduct`'s constructors, `addInduct_WF`, `TrProj`) and `PreludeBridge`.
Nothing below shortens them. A reader looking for the single next thing to fund should note that
the analysis here is about the *other* branch.

---

## 3. Re-deriving the gateway from `kernel_sound`'s side — machine-checked

`handoff-stratified.md` §14.5 records a cone scan done from `Injectivity.lean`'s side. I re-ran it
from the goal's side: the import closure of `Verify/Bridge.lean` — i.e. exactly the declarations
`kernel_sound` will be able to use — with a transitive `getUsedConstantsAsSet` fixpoint,
**including** internal names (a first pass that filtered them broke the chain at
`foldlM_addDecl_WF` and undercounted; that is a scan trap worth recording).

| statement | transitive users | non-internal | reaches `addDecl.WF` | reaches the Bridge export | direct users |
|---|---|---|---|---|---|
| `IsDefEqU.sort_inv` | 187 | 174 | yes | yes | **1** — `IsDefEq.uniq` |
| `IsDefEqU.forallE_inv_stratified` | 188 | 175 | yes | yes | **2** — `IsDefEq.uniq`, `IsDefEqU.forallE_inv` |
| `IsDefEqU.forallE_inv` | 58 | 50 | yes | yes | **2** — `TrExpr.beta`, `inferApp.loop.WF` |
| `IsDefEqU.sort_forallE_inv` | **0** | 0 | no | no | — |
| `IsDefEqU.const_sort_inv` | **0** | 0 | no | no | — |
| `IsDefEqU.const_forallE_inv` | **0** | 0 | no | no | — |
| `IsDefEqU.const_app_inv` | **0** | 0 | no | no | — |

And: `Lean4Lean.VEnv.IsDefEq.church_rosser` and `Lean4Lean.VEnv.Params` **do not exist in that
closure at all** — `ChurchRosser.lean` (2207 lines, 88 declarations, 5 `sorry`s) and the
`Params`/`Pattern` machinery are not imported by `Verify/Bridge.lean`. Neither is
`Theory/SetModel/` (nothing outside that directory imports it).

**Three corrections to §14.5, all in the favourable direction:**

* **Four dead statements, not three.** `sort_forallE_inv` joins the three `const_*_inv` at zero
  call sites in `kernel_sound`'s closure. §14.5 attributed its consumers to `ChurchRosser.lean`;
  those are outside the closure.
* **`forallE_inv` has two *live* consumers, not zero.** §14.5 says its remaining consumers "sit
  inside `class Params`, which has no instance in the tree, so they are already vacuous". In
  `kernel_sound`'s closure `forallE_inv` is used directly by `TrExpr.beta`
  (`Verify/Typing/Lemmas.lean:2585`) and `inferApp.loop.WF` (`Verify/TypeChecker/InferType.lean`),
  neither of which is under `Params`. So the load-bearing set is **three** statements, not two:
  `sort_inv`, `forallE_inv_stratified`, `forallE_inv`.
* **`sort_inv` has exactly one direct consumer in the whole closure.** That is a sharper target
  than "the gateway `IsDefEq.uniq`": everything downstream is `uniq`'s ~28-member family.

**And the load split is exactly as §14.5 says, from the other direction:** every one of the 174
declarations in `sort_inv`'s cone is in `Verify/*` or in `Theory/Typing/UniqueTyping.lean` itself.
**The model does not consume `sort_inv`** — it is not even in the closure. `soundness-ledger.md`'s
own case table agrees ("Soundness consumes **no** injectivity fact at all; `sort_inv` is spent on
constructing `LevelAssign`, and nowhere else"), and `LevelAssign` has since been replaced by
`PropSplit`, which is weaker again.

So there are **two independent gateways**, and they are not the same statement:

* **Gateway A, `Verify/`:** `IsDefEq.uniq` (⟸ `sort_inv` + `forallE_inv_stratified`), plus
  `forallE_inv` at two sites.
* **Gateway B, model:** `PropSplit` (⟸ `PropUniq ∧ PropTypeAgree`).

B follows from A. A does not follow from B. §5 and §6 take them in turn.

---

## 4. Gateway B, exactly: what the model imports and nothing more

`interp` (`SetModel/Interp.lean:469`) is a **function of a raw `VExpr` and a raw `List VExpr`
context** — not of a derivation. Its only non-structural clauses are three branches:

```lean
| Γ, .app f a      => if L.IsProof M Γ f      then ⟨fun _ ↦ pt, _⟩ else ⟨…apply…⟩
| Γ, .lam A b      => if L.IsProof M (A::Γ) b then ⟨fun _ ↦ pt, _⟩ else ⟨mkLam …⟩
| Γ, .forallE A B  => if L.IsProp  M (A::Γ) B then ⟨mkForallProp …⟩ else ⟨mkForallType …⟩
```

`PropSplit` (`Interp.lean:391`) is six fields: two predicates, two decidability fields, and

```lean
prop_sound  : u.WF nv → env.HasType nv Γ A (.sort u) → (IsPropAt ls Γ A ↔ u.eval ls = 0)
proof_sound : u.WF nv → env.HasType nv Γ e A → env.HasType nv Γ A (.sort u) →
              (IsProofAt ls Γ e ↔ u.eval ls = 0)
```

`PropSplitAudit.propSplitOf` (`:173`) builds one from `PropUniq ∧ PropTypeAgree`; and the
converse is one line from `prop_sound`/`proof_sound` read at two sorts of one type / two types of
one term. **So `PropSplit` is *equivalent* to `PropUniq ∧ PropTypeAgree`, not merely implied by
it.** That is the model's entire syntactic import: everything else in `SetModel/` is sorry-free
(22 files, 0 live `sorry`s, verified), and `soundAbove`/`sound`/`sound_nil`/`interp_congr` are
**proved** modulo six hypotheses — `hle`, `henv`, `hS : L.Stable`, `hC : CoherentOn`, `hR :
CtxInvariant`, `hRd`.

Two further facts, both relevant to §6 and neither previously composed:

* **`⟦falseProp⟧ = ∅` is branch-independent.** `PropSplitAudit.prop_forces_true` machine-checks
  `L.IsPropAt ls [.sort .zero] (.bvar 0)` for *any* `PropSplit`, so `falseProp`'s Π takes the
  `mkForallProp` branch. But it does not matter which branch: `⟦.sort .zero⟧ = U κ 0` contains
  `∅`, and the fibre over `∅` is `∅`, so `mkForallProp` is `∅` (some fibre is empty) and
  `mkForallType` is `∅` (no function can pick an element of `∅`). **The consistency conclusion is
  robust to the split being wrong at `falseProp`.** Nothing in the tree composes this with
  `sound_nil`; it is a short, unwritten step, and it should be written first because it is the
  only place the goal actually touches the model.
* **The model, as `kernel_sound` needs it, runs at `nv = 0`.** `hfalse` gives
  `HasType 0 [] e falseProp`, so `sound_nil` is instantiated at `nv := 0`, `Γ := []`. At `nv = 0`
  every `VLevel` in scope is closed, so `u.eval ls` is independent of `ls` and
  `u.eval ls = 0 ↔ u ≈ .zero`. *Analysis:* `PropUniq env nv` and `PropTypeAgree env nv` both
  reduce to their `nv = 0` instances by `IsDefEq.instL` (`Theory/Typing/Lemmas.lean:595`) — both
  conclusions are about `u.eval` at a *single* valuation `ls`, and any `ls` is realised by closed
  `VLevel`s (`succ^n zero`). Whether the *outer* `CoherentOn` induction can also be run at
  `nv = 0` (defining `M.cnst c us` by interpreting `ci.value.instL us` rather than uniformly in
  the level parameters) is a separate check, named in §9.

---

## 5. Gateway A: required as the tree stands, and an artifact of a choice `kernel_sound` does not make

`Theory/Typing/Basic.lean:18` makes `IsDefEq` **four-place**: `Γ ⊢ e₁ ≡ e₂ : A`, with the type an
*index shared by every rule* — `trans` demands one `A` for both halves, `lamDF` one `u` and one
`B`, `forallEDF` one `u` and one `v`. `IsDefEqU Γ e₁ e₂ := ∃ A, IsDefEq Γ e₁ e₂ A` is derived.
`RawDefEq.lean` already documents that the reference's judgment (`axioms.tex:30–41`) is
**three-place**, with `symm` and `trans` carrying no type at all, and calls this "the single
load-bearing divergence".

That file diagnoses the divergence for `ChurchRosser.lean`. The cone scan says the same diagnosis
holds for the part that matters, and `ChurchRosser.lean` is not even in the goal's closure. Every
`uniq` consumer in `kernel_sound`'s cone is an instance of one of four lemmas, all in
`UniqueTyping.lean`, all of which are **rules** three-place:

| lemma | `UniqueTyping.lean` | three-place status |
|---|---|---|
| `IsDefEqU.trans` | `:167` | the `trans` rule |
| `IsDefEq.trans_l`, `.trans_r`, `.transU_*` | `:124–138` | the `trans` rule |
| `IsDefEqU.of_l`, `.of_r`, `HasType.defeqU_*` | `:147–165` | the conversion rule of *typing* |
| `IsDefEqU.defeqDF` | `:140` | the conversion rule of *typing* |

`RawDefEq.lean` records the mechanical version of this: `IsDefEq.defeqDF` — the conversion rule —
**erases to nothing** under `IsDefEq.raw`; its case is `exact ih2`.

### The enlargement that removes it, named — and what it does not remove

> **(E) `IsDefEqU'`** — replace the derived `IsDefEqU` by the reflexive/symmetric/transitive
> **closure** of `fun e₁ e₂ => ∃ A, IsDefEq Γ e₁ e₂ A`, and change `IsDefEq`'s conversion rule
> from `Γ ⊢ A ≡ B : .sort u → Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ ≡ e₂ : B`
> to `IsDefEqU' Γ A B → Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ ≡ e₂ : B`.

*What it buys, and the reason it is worth writing down:* **the enlargement is model-neutral.**
The model's part 4 for `IsDefEqU'` follows from part 4 for `IsDefEq` by composition of equalities,
with **no typing on the middle term at all** — `EqSound M L Γ e₁ e₂` is
`∀ ρ ∈ interpCtx, ⟦e₁⟧ρ = ⟦e₂⟧ρ`, which is transitive and symmetric for free, and
`interp_congr` (`SoundInduction.lean:424`, proved) is exactly the base case. The `Above` wrapper
composes by `max` (`model-interface.md` §4's "`Above` algebra"). Part 3 for the enlarged
conversion rule is then free too: `⟦A⟧ = ⟦B⟧` gives `⟦e⟧ ∈ ⟦B⟧` from `⟦e⟧ ∈ ⟦A⟧`.
**The step `sort_inv`'s `trans` case cannot take syntactically — composing across an arbitrary
middle term — the model takes for free, because `interp` is total on raw syntax.**
With (E), `sort_inv` and `forallE_inv_stratified` leave `kernel_sound`'s cone entirely: 174
declarations' worth of dependence becomes four constructors.

*What it does not buy, stated because it is the reason (E) is not the answer:* it does **not**
remove `IsDefEqU.forallE_inv`, whose two consumers (`TrExpr.beta`, `inferApp.loop.WF`) need
Π-injectivity for the conversion relation, and (E) makes that relation larger, so injectivity for
it is at least as hard. Π-injectivity for an untyped conversion is precisely the reference's
Church–Rosser development, whose port is closed at the index (`handoff` §12). **(E) is a
simplification of two thirds of Gateway A, not a discharge of it.** Whether the two `forallE_inv`
sites can be restructured out of `Verify/` is owned by that stream and is not priced here.

*Trap check.* (E) enlarges the judgment, so it weakens `kernel_sound`'s refinement obligation and
strengthens the model's — the standard trade. The claim above is that the strengthening is *nil*,
because the only new closure is under `trans`/`symm`, on which the model's conclusion is already
an equation. That is analysis, not machine-checked; row-zero in §9.

---

## 6. The candidate: `PropTypeAgree` alone, because the goal hands you the `False` proof

This is the finding the forward routes could not reach, and it is entirely a consequence of
reading the theorem rather than the plan.

### 6.1 The observation

`leanTTConsistent` is `∀ env, env.LeanWF → ¬ ∃ e, env.HasType 0 [] e falseProp`. Because
`¬ P` **is** `P → False`, a proof of it may begin

```lean
intro env hwf ⟨e, he⟩          -- he : env.HasType 0 [] e falseProp
```

**before any model is built.** From that point on, every proposition of `env` is inhabited: for
any `Γ ⊢ A : .sort .zero`, weakening `he` into `Γ` (`falseProp` is closed) and applying gives
`Γ ⊢ .app e' A : A`, since `falseProp = .forallE (.sort .zero) (.bvar 0)` and
`(.bvar 0).inst A = A`.

Nothing in `Theory/SetModel/` uses this. `PropSplitAudit.propSplitOf` takes `PropUniq` and
`PropTypeAgree` as bare hypotheses; `soundAbove` is parameterised on `PropSplit envF nv` with no
inhabitation hypothesis anywhere. **The `False` proof lives in `envF` — the *final* environment,
which is exactly the environment `PropSplit` is stated for** (`soundAbove` takes
`hle : env₀ ≤ envF` and `L : PropSplit envF nv`, the derivation in `env₀`). So the hypothesis is
available precisely where the split is needed.

### 6.2 The derivation

> **Claim (analysis).** Let `env : VEnv` with `∃ e, env.HasType 0 [] e falseProp`. Then
> `env.PropTypeAgree 0 → env.PropUniq 0`.

*Proof.* Take `Γ ⊢ A : .sort u`, `Γ ⊢ A : .sort v` with `u.WF 0`, `v.WF 0`, and any `ls`. If
neither `u.eval ls` nor `v.eval ls` is `0` the biconditional is trivial. Otherwise, WLOG
`u.eval ls = 0`. Since `u.WF 0`, `u` is closed, so `u ≈ .zero`; `sortDF` gives
`Γ ⊢ .sort u ≡ .sort .zero : .sort (.succ u)` and `defeqDF` gives `Γ ⊢ A : .sort .zero`. Weaken
`he` into `Γ` and apply, obtaining `t := .app e' A` with `Γ ⊢ t : A`. Now instantiate
`PropTypeAgree` at `e := t`, `A := A`, `A' := A`, sorts `u`, `u'` := `v`: its four hypotheses are
`Γ ⊢ t : A` (twice), `Γ ⊢ A : .sort u`, `Γ ⊢ A : .sort v`, and its conclusion is
`u.eval ls = 0 ↔ v.eval ls = 0`. ∎

The whole content is the one substitution `A' := A`: **`PropUniq` is `PropTypeAgree`'s diagonal,
guarded by the existence of an inhabitant** — and `hfalse` supplies the inhabitant exactly where
the guard bites, because the guard bites only at propositions.

Combined with §4's `nv`-reduction, the model's syntactic import becomes one statement:

> **`PropTypeAgree envF 0`.**

### 6.3 Why this is not circular, and why it is not a weakening in disguise

*Not circular.* `hfalse` is a hypothesis of the theorem, not something the model produces. The
model is built after it, and the model's job is to contradict it. Assuming it while constructing
the model is exactly the classical shape of the argument (`¬P` is proved by `intro`), and the
Bridge already delivers `hfalse` in usable form (`hasType_falseProp`, proved, sorry-free) *before*
`leanTTConsistent` is invoked.

*Not a restatement.* Nothing about `leanTTConsistent`'s statement changes. `Verify/Soundness.lean`
is untouched. What changes is where the `intro` goes, and that is free.

*Trap #11 check — is `PropTypeAgree` a genuinely different statement from `PropUniq ∧
PropTypeAgree`?* Yes, in the only direction that matters: the conjunction implies it; the
converse is the content of §6.2 and needs `hfalse`. Without `hfalse` I do **not** claim
`PropTypeAgree ⟹ PropUniq` — the diagonal instantiation has nothing to instantiate `e` with at an
uninhabited proposition. If someone later shows `PropTypeAgree ⟹ PropUniq` unconditionally, the
conclusion of this section is unchanged and stronger; the two outcomes are not in tension.

*Trap #10 check — does the pass cost something?* It does: it consumes a hypothesis (`hfalse`) that
no previous formulation had in scope, and it fails without it. It is not a triviality obtained by
restating.

### 6.4 Where this differs from the "minimum convention", which was attempted and refuted

`model-interface.md` §5 records an attempt to remove `PropUniq` by weakening `IsProp` to "*some*
sort of `A` evaluates to `0`" and dropping the ⟹ direction of `prop_sound`. It failed at two
named places: `propSound_of_mem_sort`'s load-bearing `u.eval ls = 0` (machine-checked by
hypothesis-necessity), and `Sound.proof`'s use of the premise's own sort — i.e. at **parts 1 and
2** of the soundness bundle.

**The candidate here does not weaken `prop_sound`.** `PropSplit` keeps both directions of both
fields; the ↔-form stands exactly as `model-interface.md` §5 concluded it must. What changes is
only how `PropUniq` — one of the two statements `propSplitOf` needs — is *discharged*. So the two
failure sites are untouched: they are consumers of `prop_sound`, and `prop_sound` still holds in
full. **This is a different move from the one that was refuted, and it is aimed at a different
part of the interface.** That distinction is the single most important thing to check before
funding it (§9, RZ-1).

---

## 7. Can the negative statement be reached without interpreting everything? — No, twice

The task asked whether a *negative* conclusion admits a cheaper argument than a positive
interpretation. Two cheap arguments say it does not, and both are worth recording because they
are the natural first ideas and neither is written down in the tree.

### 7.1 The collapse of proofs is forced by cardinality, not by the thesis's design

`model-interface.md` §5 gives half of this ("the `{•}` collapse at a `Prop` is forced by
impredicativity … its rank is that of the domain, which impredicativity leaves unbounded"). The
full form is a two-line cardinality argument and it settles the general question:

Let `S := ⟦Sort 0⟧`, a **set** (because `Sort 0 : Sort 1` forces `S ∈ ⟦Sort 1⟧`). Impredicativity
forces `S` to be closed under set-indexed dependent products from *arbitrary* index sets: for any
`A` and any `F : A → S`, `Π(A,F) ∈ S`. If some `X ∈ S` had `|X| ≥ 2`, then `Π(A, const X)` has
cardinality `|X|^{|A|}`, unbounded as `A` ranges over all sets — so `S` would not be a set.
Hence **every element of `⟦Sort 0⟧` is a subsingleton.** A dependent product of subsingletons is a
subsingleton, so `Π(A,F)` *is* one — but its unique element is a function whose rank tracks `A`,
so the singletons `Π(A,F)` produced this way form a proper class. For `S` to be a set they must be
identified with a canonical `{•}`. **That identification is the split, and it is forced in any ZFC
model of this theory, whatever the interpretation's shape.** No parameterisation removes it; the
only question is which syntactic statement decides it, which is §4.

### 7.2 "Soundness only at `Prop`" is refuted by large elimination

The natural economy — the conclusion is about a `Prop`, so interpret only `Prop` and collapse all
data to a single point `⋆` — is unsound, and the refutation is one line:

`Nat.rec (motive := fun _ => Prop)` eliminates `Nat` into `Prop`. Its ι-rules force
`⟦Nat.rec m z s .zero⟧ = ⟦z⟧` and `⟦Nat.rec m z s (.succ n)⟧ = ⟦s n (Nat.rec m z s n)⟧`. Choose
`z := True`, `s := fun _ _ => False`: the two must be `{•}` and `∅`. But `⟦.zero⟧ = ⟦.succ .zero⟧ = ⋆`,
so both are `⟦Nat.rec m z s ⋆⟧` — one value. **Contradiction.** So the data layer must be
interpreted faithfully wherever a `Prop` can be computed from it, which in Lean is everywhere a
non-subsingleton inductive large-eliminates. The `False`-proof's derivation may use any of it, so
"a model of the fragment a `False`-proof lives in" is a model of the whole theory.

### 7.3 What the negative *does* buy

Exactly two things, and both are in this document:

* **`⟦falseProp⟧ = ∅` is branch-independent** (§4) — the conclusion does not depend on the split
  being correct at the one place it is finally applied.
* **`hfalse` inhabits every proposition** (§6) — which discharges `PropUniq`.

Nothing else. In particular `hfalse` does *not* help with `PropTypeAgree`: that statement is about
two types of one term, and an extra inhabitant of each type says nothing about their sorts.

---

## 8. Check against the six closed routes

| closed route | is the candidate one of them? |
|---|---|
| the logical relation (`docs/logrel-scope.md`) | **No.** Nothing here is defined by recursion on types or reducibility, there is no weak-head reduction, no PER, no fundamental lemma. `PropTypeAgree` is a statement about `HasType`; the model that consumes it is the existing `SetModel/`, sorry-free. |
| the alternation index and its four repairs | **No.** `PropTypeAgree env 0` is the **unstratified** statement, at zero universe parameters. `Stratified.lean`/`UniqueTypingN.lean` are not on the path. |
| the reduction development (`unique.tex` §§3–4, `SubstT` refuted) | **No.** No κ-reduction, no `≡ₚ`, no confluence, no substitution into a typing at a preserved index. |
| universe discrimination / `common_sort` | **No.** That family tried to read *sort-shaped vs Π-shaped* off a universe, refuted by `succ_eq_imax`. `PropTypeAgree` reads a `Prop`/non-`Prop` bit off a *type*, and `model-interface.md` §5 records that it survives the cumulativity check that killed `SortUniq` and `PropUniq`. |
| the hereditary shape strengthening | **No.** No spines, no `Apply`, no shape predicates. And §6 is a *weakening* of the model's import, checked in both directions (§6.3), not a strengthening. |
| the joint induction (`thesis-architecture.md` §8, row zero refuted in `PropShadow.lean`) | **No.** There is no simultaneous derivation of unique typing and soundness, and no index to preserve. `regularity_two_typing_false` is about `⊢ₙ₊₁ → ⊢ₙ`; §6 never drops an index. Note the contrast: in the **unstratified** four-place judgment regularity is free (`IsDefEq.hasType`, `Theory/Typing/Lemmas.lean:244`), so the refutation does not transfer. |

Also checked against the two live negatives that bound the neighbourhood:
`LevelAssignUnsat.no_levelAssign` refutes the *unguarded* `LevelAssign`, a structure the model no
longer uses; `SortUniq`'s cumulativity refutation applies to `SortUniq` and `PropUniq` and — by
`model-interface.md` §5's own table — **not** to `PropTypeAgree`.

---

## 9. Row zeros, cheapest first

Each can kill the candidate before the expensive part. Run them in this order.

1. **RZ-1 — the `nv` question, and it is the whole route's row zero.** §6.2 discharges
   `PropUniq env 0`, at **zero universe parameters**. Does the model's outer induction
   (`CoherentOn`, `ModelData.cnst`) run at `nv = 0`? A `.def` step's value is typed at
   `HasType ci.uvars [] value type`, so the naive answer is no. The proposed repair is to define
   `M.cnst c us := ⟦ci.value.instL us⟧` for closed `us`, using `IsDefEq.instL`
   (`Lemmas.lean:595`), which keeps every interpretation at `nv = 0`. **If the model cannot be run
   at `nv = 0`, §6 delivers `PropUniq` only at closed levels and the candidate is dead as stated.**
   *This is cheap: it is a reading of `InterpSound.CoherentOn` and `ModelData`, not a proof.*
2. **RZ-2 — is `PropUniq env nv` really reducible to `PropUniq env 0`?** Both statements'
   conclusions are `u.eval ls = 0 ↔ v.eval ls = 0` at a *single* valuation `ls`, and any `ls` is
   realised by closed levels `succ^n zero`; `IsDefEq.instL` transports the two typings. Needs the
   eval-commutes lemma `(u.instL us).eval [] = u.eval (us.map (·.eval []))`. If this reduction
   holds, RZ-1 is unnecessary and the candidate stands at every `nv`. *Run RZ-2 before RZ-1 — it
   is smaller and it subsumes it.*
3. **RZ-3 — weakening `hfalse` into an arbitrary `Γ`.** `PropUniq`/`PropTypeAgree` as stated in
   `PropSplitAudit.lean` carry **no context well-formedness hypothesis**. §6.2 weakens a closed
   typing into `Γ`; check that `IsDefEq.weakN` does not need `OnCtx Γ`. If it does, `PropSplit`'s
   consumers all have `CtxClosed Γ` or `OnCtx Γ` in scope (`soundAbove`, `sound`), so the fields
   can carry it — but that is a change to `PropSplit`, owned by the model stream.
   *`PLAN.md`'s own lesson applies: a statement over an arbitrary `Γ` with no well-formedness
   hypothesis is suspect by default on this project (`pat_wf`, `SExpr.IsDefEq.strong`).*
4. **RZ-4 — write `⟦falseProp⟧ ∅ = ∅` and compose it with `sound_nil`.** Nothing in the tree does
   this, and it is the only place the goal touches the model. Both branches give `∅` (§4), so it
   does not wait on anything. **It should be written first regardless of the rest of this
   document**, because until it exists nobody knows what `sound_nil` has to be instantiated at.
5. **RZ-5 — (E), the `IsDefEqU'` enlargement (§5), model-neutrality.** Check that
   `EqSound`-composition plus the `Above` algebra really discharges part 4 for the closure. This
   is independent of §6 and is owned jointly by the `Theory/` and `Verify/` streams; its payoff is
   removing `sort_inv` from the cone, not removing `forallE_inv`.

---

## 10. Confidence, kept apart

**Machine-checked, this session:**

* The cone scan of §3 — all seven statements, user counts, direct-consumer lists, reachability of
  `addDecl.WF` and of the Bridge export, and the absence of `church_rosser`/`Params` from the
  closure. Script: a transitive `getUsedConstantsAsSet` fixpoint over the full `constants` map,
  internal names included.
* `collectAxioms` on `Bridge.not_leanTTConsistent_of_kernel_proves_false`,
  `Bridge.hasType_falseProp`, `addDecl.WF` (§2).

**Reading results (quoted, not inferred):**

* `kernel_sound`'s statement and the five things it does not say (§1).
* `PropSplit` ⟺ `PropUniq ∧ PropTypeAgree` — `propSplitOf` is in the tree; the converse is one
  line from the ↔-fields.
* `SetModel/` has zero live `sorry`s and `soundAbove` is proved modulo six hypotheses.
* `model-interface.md` §5's record that the minimum convention was attempted and refuted at
  `propSound_of_mem_sort` and `Sound.proof`.

**Analysis, not machine-checked:**

* §6.2, the derivation `hfalse + PropTypeAgree ⟹ PropUniq`. Every step is a named lemma of the
  tree (`sortDF`, `defeqDF`, weakening, `appDF`/`beta`), but it has not been written; ~20 lines.
* §4's `nv = 0` reduction and §9's RZ-1/RZ-2.
* §5's claim that (E) is model-neutral.
* §7.1's cardinality argument and §7.2's large-elimination refutation. Both are short enough to
  formalise; neither is in the tree.

**Not established, and not claimed:**

* That `PropTypeAgree` is provable. It remains open, with three characterised obstructions at the
  index (`handoff` §5: `forallEDF`, `proofIrrel`, `eta`, the last reducing to
  `SortForallEDisjoint`) and no price unstratified. **This document does not move it one inch.**
  What it claims is that it is now the *only* thing the model needs.
* That `PropTypeAgree ⟹ PropUniq` without `hfalse`.
* That (E) removes `forallE_inv`. It does not (§5).
* That any of this shortens the inductive keystone or `PreludeBridge` (§2). It does not.

---

## 11. If the candidate fails

Then the honest statement is the one the project owner needs, and it is this:

`kernel_sound` requires, irreducibly, (i) the inductive keystone, (ii) `PreludeBridge`, (iii) a
ZFC model of the *whole* theory — §7 closes both cheap escapes — and (iv) a decision procedure for
"is this a proof?" that is correct on raw syntax, which is `PropUniq ∧ PropTypeAgree`. Of those,
(iv)'s first conjunct is in the `sort_inv`/normalisation family, whose every known route is closed:
the reference's `thm:utype` is machine-checked invalid, its four index repairs are closed by
arithmetic, §§3–4 is closed by `SubstT`, universe discrimination is refuted, the hereditary
strengthening is the statement itself, the joint induction's row zero is false, and the logical
relation is priced out on scope. In that case the project's remaining options are exactly the two
`logrel-scope.md` §7 names — build a normalisation proof for full Lean, which is an open research
problem, or assume it, which `Verify/Guard.lean`'s whitelist forbids — and the decision is the
owner's, not a stream's.

The candidate in §6 is worth running first because it is small, because its row zeros are readings
rather than proofs, and because it is the only thing found in this analysis that changes which of
those two options the project is facing.
