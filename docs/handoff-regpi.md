# `RegPi`, and `PropConvInv`'s `extra` case

Stream deliverable for the two items `Theory/Typing/PropConv.lean` flags live.  Everything
claimed proved is in `Theory/Typing/RegPiSat.lean`, sorry-free, axioms `propext`,
`Quot.sound`, `Classical.choice` — all on `Guard.lean`'s whitelist.  Claims read off source
rather than machine-checked are marked **[read]**.

---

## 0. Headline

1. **`RegPi` is false.**  Not "unproved": refuted, for every environment, every `U`, every
   `n`, base index and empty environment included (`regPi_false`).  Its only consumer,
   `propTypeAgree_appCase_of`, is therefore void — it proves nothing, though it refutes
   nothing either.
2. **The repair exists and is satisfiable at a non-degenerate environment.**  `RegPiOn` =
   `RegPi` under `OnCtxN`, obtained from a genuine regularity statement `Regular`, replayed
   at index 0 over `CycleConv.lean`'s `propLoopEnv` (two constants, two δ-rules), with the
   consumer re-proved against it end to end.
3. **`PropConvInv`'s `extra` case is open**, discharged in `propConvInv_of` by the hypothesis
   `PropExtraConv` and nothing else.  It is now reduced one step further to `DefEqTypeN` +
   `SameTypeProp`, and at `propLoopEnv` the first half is discharged at every index, leaving
   the case environment-free there.
4. **`SortNotProp`'s dependency on `PropConvInv` is a genuine same-index cycle** — not caused
   by `extra`, and not repaired by it.

---

## 1. Proved (machine-checked, `Theory/Typing/RegPiSat.lean`)

| name | content |
|---|---|
| `regPi_false` | `¬ env.RegPi U n` for all `env U n`. Witness `Γ = [.forallE (.bvar 0) (.bvar 0)]`, `f = .bvar 0`; `Lookup.zero` supplies the Π-typing, `HasTypeN.bvar_inv` + `Lookup.lt` kill `.bvar 1` in a length-1 context |
| `IsTypeN`, `OnCtxN`, `OnCtxN.lookup`, `IsTypeN.mono`, `OnCtxN.mono` | the relativisation apparatus |
| `RegPiOn`, `Regular`, `EnvReg`, `RegConvE` | the repaired statement and its ingredients |
| `regular_of'`, `regular_of` | `Ordered` + `EnvReg` + `InstLvl` + `RegConvE` ⟹ `Regular`; induction on the typing judgment, all seven cases |
| `Regular.regPiOn`, `Regular.lvlWF` | `Regular` ⟹ `RegPiOn`; and ⟹ "the universe of a type is well formed", the datum `Stratified.lam` does not ship |
| `RegConvE.zero`, `EnvReg.of_constPropType`, `regular_zero`, `regPiOn_zero` | satisfiability at the base index |
| `propLoopEnv_constPropType`, `propLoopEnv_regular`, `propLoopEnv_regPiOn`, `propLoopEnv_regPiOn_fires` | the **non-degenerate** witness: `CycleConv.lean`'s `propLoopEnv`, and `RegPiOn` applied at a real Π-typed variable in a real well-formed context |
| `OnCtxN.of_onCtx` | `OnCtx Γ (env.IsType U)` ⟹ `∃ m, OnCtxN env U m Γ` — the hypothesis is reachable from the one `Injectivity.lean`'s targets already carry |
| `PropTypeAgree.AppCaseOn`, `propTypeAgree_appCase_on_of` | the consumer, re-priced at `RegPiOn` |
| `PropTypeAgreeOn`, `propTypeAgree_on_of'`, `propTypeAgree_on_of` | the six closing cases of `propTypeAgree_of` survive relativisation; `lam` is where the context grows and where `Regular.lvlWF` is spent |
| `propTypeAgreeOn_of_residuals` | the whole chain at `n = k+1` from `DefInv` + `Regular` + `InstLvl` + `PropUniq` + `PropConvInv` |
| `PropTypeAgree.AppCaseOn.zero`, `PropTypeAgreeOn.zero`, `propTypeAgreeOn_zero_from_residuals` | the relativised reduction replayed at index 0, **over `propLoopEnv`**, so not vacuous |
| `DefEqTypeN`, `SameTypeProp`, `propExtraConv_of` | `extra` closes from those two and nothing else |
| `PropTypeUniq`, `.sameTypeProp`, `.zero`, `SameTypeProp.zero` | the strong form of the second half, and both at index 0 |
| `propLoopEnv_defEqTypeN`, `propLoopEnv_propExtraConv`, `propLoopEnv_propExtraConv_zero` | at the witness environment `DefEqTypeN` holds at **every** index, so `extra` there is exactly `SameTypeProp` |
| `envReg_single`, `defEqTypeN_single` | the index exists **per constant / per rule** — the true shape of the §16.5 obstruction |
| `propConvInv_from_sortNotProp_cycle` | the `PropConvInv → SortNotProp → PropNotProof → PropConvInv` loop, written out |

---

## 2. The consumer enumeration (structural, not `grep`)

Transitive `getUsedConstantsAsSet` cone over the whole `Lean4Lean.Theory.Typing` subtree
(script in the scratchpad; `Theory.SetModel` cannot be imported alongside it, see §6):

```
transitive consumers of Lean4Lean.VEnv.RegPi: 1
  Lean4Lean.VEnv.propTypeAgree_appCase_of
```

That is the whole of it, and it has no consumers of its own.  Cross-check: **no file in the
repository imports `Theory/Typing/PropConv.lean`** — it is a leaf — so the cone over the
subtree is the cone over the repository.

**What survives if `RegPi` is dropped.**  Everything except `propTypeAgree_appCase_of`.
Nothing downstream of `PropTypeAgree.AppCase` breaks, because nothing is downstream: the
`AppCase` statement is untouched by the refutation, only that one derivation of it is void.
`PropConv.lean`'s summary line "each reduction is replayed [at the base index] … the one
exception is `RegPi`" is exactly right about the scope of the damage.

**What replaces it.**  `propTypeAgree_appCase_on_of` — the same proof, the same four other
ingredients, `RegPi` → `RegPiOn` and a context hypothesis.  It does **not** discharge
`PropTypeAgree.AppCase`; it discharges `PropTypeAgree.AppCaseOn`, and the statement
`PropTypeAgree` has to be relativised with it (`PropTypeAgreeOn`), because the `lam` case of
its own induction grows the context.  That relativisation is done and replayed at index 0.

Corrected price of `PropTypeAgree`'s `app` case, superseding handoff-stratified §16.3:

    Regular + InstLvl + PropUniq + PropConvInv          (all under `OnCtxN`)

with `Regular` resting on `Ordered` + `EnvReg` + `InstLvl` + `RegConvE`.

---

## 3. What `RegPiOn`'s satisfiability does and does not cover

`regPiOn_zero` needs `Ordered env` and `EnvReg env U 0`.  `EnvReg` — "a constant's
instantiated type is a type *at the index*" — is the only environment-specific residual, and
it is **not** free from `Ordered`:

* `envReg_single` (machine-checked): for one constant, in an ambiently well-formed context,
  the index exists.  `defEqTypeN_single` is the same for one rule.
* What does not follow is one index for all constants at once.  `VEnv.constants` is a
  function `Name → Option VConstant` with no finiteness, and `Stratified.mono` only raises an
  index.  This is `docs/handoff-stratified.md` §16.5's "second obstruction inside `extra`",
  and it is generic: **every** residual whose discharge needs a typing from the environment
  meets it.  §16.5 marked it "analysis, not machine-checked"; the positive half is now
  machine-checked and the negative half is a statement about the datatype, not a theorem.

So: the witness covers *ordered environments whose constant types are types at the index*,
which includes `propLoopEnv` (constants and δ-rules both inhabited) and excludes nothing that
the base-index setting can reach anyway — at `n = 0` a constant whose type derivation genuinely
uses a conversion is out of reach, and that is a property of index 0, not of the repair.

---

## 4. `PropConvInv`'s `extra` case — the true state

**It is open.**  `propConvInv_of`'s branch is one line, `exact r7 (.extra h1 h2 h3) h1 h2 h3`:
the case is discharged by the `PropExtraConv` hypothesis and by nothing else.  `PropExtraConv`
is stated, not proved.  `PropExtraConv.zero` holds, but only because `≡₀` is syntactic
equality and the residual carries the rule's own conclusion as a premise — so unlike the other
six residuals, the base index carries no information about this one.

The instruction that it "closes mechanically" was wrong, and `PropConv.lean`'s own section
("The `extra` case is not settled by rule shape") already says why: `WF.instL_lhs_ne_sort` and
`instL_lhs_ne_forallE` conclude *an endpoint is not this syntactic shape*; `PropConvInv`'s
conclusion is a typing, and a rule's left-hand side may perfectly well be a proposition.
**[read]** — verified by reading `propConvInv_of` and `Theory/Typing/DeclRules.lean`'s two
lemmas, not by attempting the mechanical proof.

**What it needs, exactly** (`propExtraConv_of`, machine-checked):

1. `DefEqTypeN` — both sides of every rule are typed at `df.type.instL ls` **at the index the
   rule concludes at**.  Environment fact; meets the §16.5 obstruction above.
2. `SameTypeProp` — two terms of one type agree on being propositions.  No environment, no
   rule; implied by `PropTypeUniq` (unique typing at a proposition).

The conversion premise `PropExtraConv` carries is *not used* by the reduction, which is worth
knowing: unlike the other five conversion residuals, `extra` does not become easy by being
handed its own conclusion.

**The step at which the mechanical route fails**, precisely: after
`obtain ⟨hl, hr⟩ := hdt h1 h2 h3` one has `Γ ⊢ₙ lhs' : T` and `Γ ⊢ₙ rhs' : T` and the
hypothesis `Γ ⊢ₙ lhs' : .sort .zero`.  To move to `Γ ⊢ₙ rhs' : .sort .zero` one needs
`T ≡ₙ .sort .zero`, i.e. unique typing at the index — and `PropTypeAgree` does **not** supply
it: `PropTypeAgree` transports propositionhood between the two types *of one term*, and here
the two terms differ.  Neither direction of `PropTypeAgree` applies (the instance one wants
would need `IsPropN Γ (.sort .zero)`, which is false).  That is why the residual is
`SameTypeProp` and not an instance of anything already in the file.

At `propLoopEnv` half 1 is discharged **at every index** (`propLoopEnv_defEqTypeN`): both
sides of both rules are `.const`s, and the `const` rule mentions no conversion, so nothing has
to be lowered.  That is the general recipe — the obstruction bites only for rules whose sides
need `conv`.

---

## 5. `SortNotProp` — is the dependency circular?

`SortNotProp.of_propConvInv : DefInv → PropConvInv → SortNotProp`.  It derives `SortNotProp`
from the **statement** `PropConvInv`, not from `propConvInv_of`, so:

* the open `extra` case does **not** make it unsound or circular *as a lemma*;
* but the loop it closes is real.  `propConvInv_of'` takes `PropNotProof` as one of its seven
  residuals; `propNotProof_of''` produces `PropNotProof` from `SortNotProp`; `SortNotProp`
  comes from `PropConvInv`.  `propConvInv_from_sortNotProp_cycle` writes the composite out and
  makes the shape visible: `PropConvInv` appears among the hypotheses of a derivation of
  `PropConvInv`, at one fixed index, with no descent.
* `SortNotProp` has exactly two producers in the tree, `of_propConvInv` and `.zero` (direct
  users measured structurally; classified into producers/consumers **[read]**).  The other
  route to `PropNotProof`, `propNotProof_of`, consumes `PropTypeAgree`, which in this file is
  produced only from `PropConvInv`.  So at a general index there is currently **no** route from
  `PropConvInv`'s own residual set to `PropNotProof` that does not pass back through
  `PropConvInv`; at `n = 0` the loop is cut by `PropNotProof.zero`, which is why
  `propConvInv_zero_from_residuals` goes through and says nothing about `n > 0`.

Consequence for whoever attacks `PropConvInv`: `SortNotProp` is not a cheaper sub-goal on the
way to it.  It is a legitimate obligation *for `PropNotProof` taken on its own*, and it is
exactly what handoff §16.2 already says sits in the `sort_inv` family.

---

## 6. Two corrections to the surrounding record

* **`Lean4Lean.VEnv.PropTypeAgree` and `Lean4Lean.VEnv.PropUniq` are each declared twice**, in
  `Theory/Typing/{UniqueTypingN,PropShadow}.lean` and in
  `Theory/SetModel/PropSplitAudit.lean`, with different statements (stratified `env U n` vs
  unstratified `env nv`).  The two module trees **cannot be imported together** — Lean refuses
  with "environment already contains 'Lean4Lean.VEnv.PropTypeAgree'".  Machine-checked (that
  error is the check).  Any sentence of the form "the model consumes `PropTypeAgree`" is
  ambiguous between two different propositions, and no cone measurement can span both.
* `PropConv.lean`'s `RegPi` docstring says `Injectivity.lean`'s targets "do not carry"
  `OnCtx`.  They do carry `OnCtx Γ (env.IsType U)` (see `IsDefEqU.sort_inv`, `Injectivity.lean`
  line 222); what they do not carry is the *stratified* version.  `OnCtxN.of_onCtx` bridges
  the two, at the cost of an index that depends on the context.

---

## 7. Pick up first

1. **`SameTypeProp`.**  It is now the whole of `extra` at any environment whose rules are
   conversion-free (which is the common case), it mentions no environment, and it has an
   obvious strengthening (`PropTypeUniq`) and an obvious base case.  Run the criterion on it:
   induction on the *typing* of `e`, keeping `e' : T` as a hypothesis, is the manoeuvre that
   worked for `PropUniq` in §16.1 and has not been tried here.
2. **`EnvReg` at a fixed index.**  Either find a formulation of `Stratified` in which
   environment facts enter at index 0 by construction (constant types carry their own
   conversion-free derivation), or accept `EnvReg` as a standing environment hypothesis and
   check what it costs downstream.  It is now load-bearing for `Regular`, hence for
   `RegPiOn`, hence for `PropTypeAgree`'s `app` case.
3. **Do not re-derive `RegPi`.**  It is false.  Anything phrased as "regularity at a Π-type"
   without a context hypothesis is false for the same one-line reason.
