# Handoff: the indexed nested block — the flag, measured against Lean's own kernel

**Started 2026-09-03.  Written incrementally; every line below was true when written.**
My files: `Lean4Lean/Theory/Inductive/IndexedWit*.lean`, this doc.  Nothing else edited.

## 0. Running log of findings (append-only)

### F1 (measured, `lake env lean` on scratch files in `/tmp/ixw`) — **Lean's own kernel REJECTS the
class the flag is about.**

`docs/handoff-valat.md` §2(c) flags: *if a nested block's foreign member has an index whose type
depends on a foreign parameter, then `member.indices = instAllTele (src.indices.map (·.instL lvls))
args 0` mentions the spine, and `WF.indices_constsIn` forces the spine to be `env`-clean — which a
nesting spine is not.  So `D.WF env` looks unsatisfiable for that class.*

Three scratch declarations, run through the real Lean frontend + kernel:

| # | declaration | Lean's verdict |
|---|---|---|
| t1 | `W (α : Type) : α → Type`, then `T1.node : (t : T1) → W T1 t → T1` | **rejected**: `(kernel) invalid nested inductive datatype 'W', nested inductive datatypes parameters cannot contain local variables` |
| t2 | `V (α : Type) : List α → Type`, then `S1.node : V S1 [] → S1` | **rejected**: `(kernel) unknown constant 'S1'` |
| t3 | `Vec (α : Type) : Nat → Type` (param-INdependent index), then `T3.node : Vec T3 2 → T3` | **accepted** |

t2's error is exactly the predicted mechanism: the companion member's *index telescope* would be
`List S1 → …`, i.e. a block member's stored type mentioning another member of the same block, and
the kernel type-checks each member's type in the environment *before* the block is declared.
t3 is the shape the spec must (and does) cover.

**Consequence for the flag**: if `D.WF env` is unsatisfiable for the parameter-dependent-index
nesting class, that is a *completeness* fact about a class the kernel refuses to declare, not a
coverage gap in `kernel_sound` — provided the Lean4Lean checker rejects it too (being checked).

### F2 (measured) — the taxonomy of indexed nestings, by Lean's own verdict

Nine scratch declarations (`/tmp/ixw/t1..t9.lean`), all through the real frontend + kernel.  What
separates accept from reject is **what the companion's index telescope ends up mentioning**, i.e.
`instAllTele (src.indices.map (·.instL lvls)) args 0` — the spec's own `VNestedOcc.member.indices`
(`Theory/Inductive/NestedBuild.lean:448`):

| companion index telescope, after instantiation | example | Lean |
|---|---|---|
| closed | t3 `Vec T3 2` (`Nat`); t9 `MI5 Prop (fun _ => T9 α) True` (`Prop`); the repo's own `TQ` (`Type`) | **accepted** |
| block-free, depends on the OUTER block's parameters | t5 `V2 γ (T5 γ) []` with `V2 (α β : Type) : List α → Type`, companion `_nested.V2_1 γ : List γ → Type` | **accepted** |
| mentions a member of the block | t2 `V S1 []`, t6 `V3 T6 []` | **rejected**: `(kernel) unknown constant 'S1'` / `'T6'` |
| (separate rule) index ARGUMENT contains a local | t1, t4, t7 | **rejected**: `nested inductive datatypes parameters cannot contain local variables` (`~/lean4/src/kernel/inductive.cpp:1053`, `is_nested_inductive_app`) |

### F3 (read off `~/lean4/src/kernel/inductive.cpp`) — the spec's staging is the kernel's staging

`check_inductive_types()` (`:254`) runs `tc().check(type, m_lparams)` on **every member's stored
type**, and `declare_inductive_types()` (`:360`) — which adds the block's constants — runs only
afterwards (`:870-871`).  So a member whose stored type mentions another member of the same block is
rejected with `unknown constant`, which is precisely the row-3 verdict above.  `VIndType.WF.isType`
and `VIndType.WF.indices` are staged at the pre-block `env` in `VInductDecl'.WF`
(`Theory/Inductive/Decl.lean:689,718`) — **the same staging**.  So the flag's unsatisfiability, if
real, coincides with a kernel rejection and is therefore NOT a coverage gap in `kernel_sound`;
it is a completeness statement about declarations no Lean environment can contain.

### F4 (machine-checked, `Lean4Lean/Theory/Inductive/IndexedWit.lean` §2) — **the flag is REAL**

`IndexedWit.wiAux` is a two-member block whose second member is
`wiOcc.member wiAux.header wiRestore` **by `rfl`** (`wi_member_built`) — the specification's own
member construction, at a foreign block `WI : (α : Type) → α → Type` whose one index's type *is*
its one parameter, nested at `α := TI`, the block's own member.  `instAllTele` then puts the own
head into the companion's index telescope (`wi_member_indices : … = [.const tiName []]`) *and* into
its stored type (`wi_member_type : … = TI → Type`).

| theorem | content |
|---|---|
| `wi_not_WF_indices` | `¬ wiAux.WF env` for every `Ordered env` in which the own head is fresh — through `VIndType.WF.indices` |
| `wi_not_WF_isType` | the same, independently, through `VIndType.WF.isType` (the flag's second half) |
| `wi_fresh_of_step` | freshness is **free**: `VEnv.addConst` returns `none` on a taken name, so any `env` at which `addIndTypes wiAux` succeeds has the own head fresh |
| `wi_not_WF_of_step` | therefore **no environment at which the declaration step is even defined satisfies `wiAux.WF`** |
| `wi_not_WF_wiEnv` | closed instantiation at an environment that *declares the container* `WI` at its declared type, and is `Ordered` — so the refutation is not vacuous for want of the foreign block |
| `VNestedOcc.not_WF_of_member_index_undeclared` | the class-level statement, stated on `instAllTele (N.src.indices.map (·.instL N.lvls)) N.args 0` — the flag's own expression |

Two general lemmas carry it: `VInductDecl'.not_WF_of_index_undeclared` and
`not_WF_of_type_undeclared` (the `Theory`-layer contrapositives of `ValAtPrice.lean` §4's
`WF.indices_constsIn`, which lives under `Verify` and so cannot be imported here).

### F5 (machine-checked, §4) — **and the spec DOES cover the indexed nested block**

`MRedex.TQWit.tqAuxB_WF : (tqAux tqAuxNodeB).WF env`, for an arbitrary `env`.  That block
(`Theory/Inductive/IndexedNested.lean` §1, another stream's, read only) is the tree's one indexed
nested block: `TQ (α : Type) : Type → Type` nesting through the indexed container
`MI (α : Type) (β : α → Type) : Type → Type`; **both** members carry an index and the companion is
`VNestedOcc.member`'s output (`tq_member_built`).  The proof is `ParamRedex.lean` §11's
`mpAuxB_WF` (the unindexed parameterised redex block) with the four index positions filled instead
of discharged by `.nil`: `VIndType.WF.indices` over a two-entry context (`tq_indexCtx_WF`),
`args_len` as `1 = 1`, and `VIndCtor.WF.args_ty` / `VIndField.WF.pos`'s index clause as real
`HasArgs.cons` steps.  **So brief-outcome 3 is refuted**: an indexed nested block is buildable and
`D.WF` is satisfiable there.  The flag's scope is exactly F2's row 3.

### F6 (machine-checked, §5) — the three never-exercised `MotiveHargs` slots

* `hAs_nil_of_spine_nil` makes `docs/handoff-faminhab.md` §4b item 1 precise as a theorem: an empty
  spine **forces** `As = []`, hence `hpi`/`hsort` are identities.  That is why the slots were dead.
* `tq_motiveHargs` inhabits `VIndRestore.MotiveHargs` at `tqAux`'s **indexed** companion (`t = 1`,
  `tqT1.indices = [Type]`), for an arbitrary `σ`: `As = [Type]`, spine `[.bvar 0]`, and `hAs` a real
  `HasArgs.cons` on a `Lookup` into the index window `liftTele t` opens.
* `tq_hmotD` is the ∀-shape `VEnv.recConstsR_wf_of_recHargsD` binds, with the `T.name ∈ K` guard
  discharged at the block (both branches reached: `TQ ∉ tqK`, companion `∈ tqK`).
* `tq_motiveHargs_As_len` — **the slot cannot be dodged here**: *every* witness at this member has
  `As.length = 1`, by `HasArgs.length_eq` on the one-entry spine.  So this is not one lucky `As`.

### F7 — what is still NOT exercised (disclosed)

The index type at `tqAux`'s companion is the **closed** `Type`, so nothing in `As` depends on the
block's parameters.  F2's row 2 — a companion index telescope that is block-free but depends on the
outer parameters (`V2 (α β : Type) : List α → Type` nested as `V2 γ (T5 γ) []`, which **Lean
accepts**) — has no witness in the tree, mine included.  That is the next coordinate, and it is now
a *named, kernel-confirmed-reachable* gap rather than an unknown.

### F8 (machine-checked, §6) — **F7's coordinate closed too**: a parameter-dependent companion index

The gap F7 named was closed in the same round.  `IndexedWit.WJ (α β : Type) : (α → Type) → Type` is
the smallest *reachable* container with a parameter-dependent index type — the index type `α → Type`
has the closed inhabitant `fun _ : α => Prop`, whereas §2's `WI : (α : Type) → α → Type` has none,
which is why the kernel's *other* rejection rule (F2 row 4) bites there and not here.  Both
`inductive WJ` and `inductive T5 (γ : Type) | node : WJ γ (T5 γ) (fun _ => Prop) → T5 γ` are
declared for real in my file, so **Lean's own kernel accepts them as part of the build**, and the
transcription is anchored three ways: `vconst(type_of% @WJ)`, `vconst(type_of% @WJ.mk)`,
`vconst(type_of% @T5)`, plus `t5_node_declared` against `vconst(type_of% @T5.node)`.

| theorem | content |
|---|---|
| `t5_member_built` / `t5_ctor_built` | the companion member *and* its constructor are `VNestedOcc.member` / `.ctor` output, by `rfl` |
| `t5_companion_indices` | `[γ → Type]` — the companion's index telescope mentions the block's **parameter** |
| `t5_companion_indices_noBlock` | …and no block constant, which is why `WF` survives (contrast §2) |
| `t5_index_not_closed` | it is genuinely open at the parameter depth (`¬ ClosedTele … 0`) |
| `t5_node_canonical` | the block is **canonical**, not a redex block, so `pos` needs no β step (a second coordinate away from `TQWit`) |
| `t5_indexCtx_WF` | `VIndType.WF.indices` here *needs* the parameter in context — the clause a closed index type cannot exercise |
| `t5Aux_WF` | **`VInductDecl'.WF` holds**, over an arbitrary environment |
| `t5_motiveHargs`, `t5_hmotD` | `MotiveHargs` with `As = [#2 → Type]`, i.e. a **parameter-dependent** telescope; `hAs`' `Lookup` typechecks only after `liftTele t` opens the index window |
| `t5_As_not_closed` | that `As` really is parameter-dependent |

The `unusedSectionVars` linter is live in this file and silent on both include lists — **verified by
deliberately adding a third section variable to `t5_motiveHargs` and watching it warn**, then
reverting.  So `hWJ` and `hT5` are both load-bearing.

## 1. Verdict

| brief outcome | result |
|---|---|
| 1. indexed nested block built, `D.WF` satisfiable there, three slots exercised | **reached**, twice: at `TQWit`'s indexed redex block (§4, §5) and at a new canonical block with a **parameter-dependent** companion index (§6) |
| 2. `D.WF` unsatisfiable for the parameter-dependent-index case, with a witness | **reached** (§2) — and it is a completeness fact, **not** a `kernel_sound` coverage defect, because Lean's own kernel rejects the identical class for the identical staging reason (F1, F3).  **No spec repair is required, and none is proposed.** |
| 3. an indexed nested block cannot be built at all | **refuted** (§4, §6) |

**So the flag of `docs/handoff-valat.md` §2(c) is retired, sharply**: `VInductDecl'.WF` is
unsatisfiable exactly when the built companion's index telescope (or stored type) mentions a member
of the block being declared, and that is exactly the class `check_inductive_types` rejects with
`unknown constant`.  The staging of `VInductDecl'.WF.types` at the pre-block `env` is **correct, not
a defect** — it is the kernel's own staging.  `Theory/Inductive/Decl.lean` needs no edit.

## 2. Where the brief is wrong, or imprecise

**(a) "Both need the same thing: an indexed nested block.  That is your target."**  Half of it was
already in the tree.  `Theory/Inductive/IndexedNested.lean` (another stream's, committed) *is* an
indexed nested block — `TQ (α : Type) : Type → Type` through the indexed `MI`, with
`tq_member_built` and `tq_aux_indices` — so brief-outcome 3 was already refutable at HEAD by
reading, and what was missing was only its `WF` and its `MotiveHargs`.  The brief's own pointer
(`docs/handoff-faminhab.md` §8 item 1, *"`IndexedNested.lean` is where such a block would go"*) is
stale: it had already gone there.  Two rounds' worth of the target existed; **I built the two
theorems about it that did not.**

**(b) "`D.WF env` may be unsatisfiable … If it is real it is a staging defect in
`VInductDecl'.WF` … it matters for CLAUDE.md's full-Lean-type-theory requirement."**  The
conditional's antecedent is true (§2) and its consequent is false (F1/F3).  The inference
"unsatisfiable ⇒ defect ⇒ coverage loss" skips the step that decides it: whether the class contains
any declaration a Lean environment can hold.  It contains none — the kernel checks every member's
stored type *before* declaring any of them, so a companion whose index telescope mentions a sibling
member is rejected outright, with the very same "unknown constant" the spec-side `ConstsIn`
argument produces.  A predicate that is unsatisfiable exactly on the kernel's reject set is not a
narrowing of `kernel_sound`; it is agreement.

**(c) "`VInductDecl'.WF` is a structure … its cone says nothing about satisfiability; the question
is whether it is *inhabited* at an indexed block, and that lives in witnesses only."**  Right, and
this is the part of the brief that paid: both answers came from witnesses, and both were cheap once
`ParamRedex.lean` §11's `mpAuxB_WF` was found as the template.  Worth adding: the refutation half
did **not** need a witness's inhabitation at all — a negative statement is immune to vacuity of its
hypotheses — but it *did* need the member to be `VNestedOcc.member`'s output by `rfl`, or it would
have been a statement about a hand-written record rather than about the construction.

**(d) A finding orthogonal to the brief, which validates the restoration layer.**  In this
toolchain **no `_nested.*` constant reaches the environment at all**: `inductive Tree | node : List
Tree → Tree` leaves none (checked by enumerating `env.constants`), and `Tree.rec`'s second motive is
over `List Tree`, not over a companion.  The auxiliary block lives only inside the kernel's
`add_inductive`.  That is exactly what `VIndRestore` / `csubst` model — the block is checked in
companion form and *published* in restored form — so the whole restoration layer is not an artefact
of the spec but a faithful account of the kernel.  It also means the accept/reject verdicts in F1/F2
are the only observable, which is why F3 reads the C++ rather than inferring from names.

**(e) The brief's constraints were all respected and none of them bound.**  No
`HasArgs.of_mkApp` (my `HasArgs` are `.cons`/`.nil` only, and every one of my declarations reports
a `sorryAx`-free cone while `of_mkApp`'s cone reaches `sorryAx`); no `AddInduct` flip;
`tryEtaStructCore.WF` / `isDefEqUnitLike.WF` untouched; `Theory/Inductive/Decl.lean` not edited and
no edit to it is proposed; frozen files not read for editing, not written, not `touch`ed.

## 3. Grading: hole-freeness vs inhabitation, stated apart

**Hole-freeness (measured).**  `Lean4Lean/Theory/Inductive/IndexedWit.lean`, **31 declarations, 31
`#print axioms` lines, all hole-free** — `[]`, `[propext]`, `[propext, Quot.sound]`, or
`+ Classical.choice` (only `wi_not_WF_wiEnv`, through `type_tac`'s use of the pre-existing typing
lemmas).  Names are read off this file's own `namespace` lines.  **This says nothing about content**
(`docs/vacuity-ledger.md` §0).

**Inhabitation (separate).**
* `tqAuxB_WF` and `t5Aux_WF` are positive statements over an arbitrary `env`, so they are inhabited
  at every environment, `VEnv.empty` included; the blocks they are about are non-degenerate in the
  coordinate that matters (`tq_indices`, `tq_aux_indices`, `t5_companion_indices` all non-empty, and
  `tq_recArg_args_ne_nil` / `t5_index_not_closed` show the index data is not `[]`-in-disguise).
* `tq_motiveHargs` / `t5_motiveHargs` are inhabited relative to **two constant lookups each**, both
  load-bearing (linter-verified), and the ∀-shapes `tq_hmotD` / `t5_hmotD` discharge the `T.name ∈ K`
  guard at the block with **both branches of the split reached**.
* `tq_motiveHargs_As_len` is the anti-luck check: *every* witness at that member has `As.length = 1`.
* **Negative results are graded differently and deliberately**: §2's five refutations are used
  contrapositively, so vacuity of their hypotheses would not matter — but they are not vacuous:
  `wi_not_WF_wiEnv` exhibits an `Ordered` environment declaring the container.
* **Disclosed degeneracies.** §2's container `WI` has `ctors = []` (the refutation touches only
  `VIndType.WF`, so constructors cannot rescue it, but the witness is degenerate in that
  coordinate); §2's block is not shown to satisfy `Built`/`OccursN` and cannot be, since Lean cannot
  declare it; §5's index type is closed (which §6 then fixes); `t5AuxMk` has no fields.
* **Not exercised by me**: the `IotaHargs` index slots; `Faithful`/`Built` at either §4's or §6's
  block; the recursor types and ι-rules of §6's block; anything about `Verify/`.

## 4. Verification record

* `lake build`: **1599 jobs, exit 0**, zero `error:` lines (twice: after §4 and after §6).
* `lake build Lean4Lean.Theory.Inductive.IndexedWit`: exit 0, **31** `#print axioms` lines, **no
  warnings from my file**.
* `grep -c "automatically included section variable"` over my module's log: **0** (and the linter is
  live — F8).
* `lake env lean --run scripts/sorry-census-all.lean`: **HOLES 13**, `BUILT: 416`, **`NOT BUILT: 0`**.
  My file is in the population and adds no hole.
* `scripts/dup-names.lean`: *"no duplicate Lean4Lean declarations across the joined cone"* — checked
  after adding §1's `ctxConstsIn_of_index`, which is deliberately **not** named `ctxConstsIn_mem`
  (that name is `ValAtPrice.lean`'s).
* Guards: `guard 1 ✓ (24 frozen axioms)`, `guard 2 ✓ (whitelist; proof INCOMPLETE — sorryAx, unchanged)`,
  `guard 3 ✓ (2/2)`.
* Frozen files: `git status --short` on `Verify/Soundness.lean`, `Verify/Axioms.lean`,
  `Verify/Guard.lean` is **empty**; none read for editing, written, or `touch`ed.
* Files created: `Lean4Lean/Theory/Inductive/IndexedWit.lean`, `docs/handoff-indexedwit.md`.
  **No other file edited.**  Read only: `IndexedNested.lean`, `ParamRedex.lean`, `RecTyped.lean`,
  `NestedBuild.lean`, `Decl.lean`, `Restore.lean`, `RestoreBridge.lean`, `Telescope.lean`,
  `NestedHead.lean`, `FamInhabNTree.lean`, `ValAtPrice.lean`, `Consts.lean`, `StrengthenAxiom.lean`,
  `~/lean4/src/kernel/inductive.cpp`.
* No state-changing `git`, no `lake update`, nothing sent outside this repo.

### 4a Measured vs read off

**Measured this session:** every axiom line; the Lean accept/reject verdicts F1/F2 (ten scratch
files in `/tmp/ixw`); that no `_nested.*` constant reaches the environment and `Tree.rec`'s restored
motive (F-(d)); every `rfl` anchor and every `decide`; both `WF`s; both `MotiveHargs`; that the
`unusedSectionVars` linter is live here; the census, dup-names, guards, job count, section-variable
count.

`HasArgs.of_mkApp` is **measured** absent, not asserted: `scripts/exists.lean` reports its cone as
`reaches sorryAx: true` (holes `IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`), while
`t5Aux_WF` (cone 1964), `tqAuxB_WF` (1969) and `wi_not_WF_of_step` (1239) all report
`reaches sorryAx: false`, so it cannot be in any of them; the string does not occur in my file
either (`grep -c` = 0).  This corner stays `PiInv`-free.

**Read off source, not independently re-derived:** `check_inductive_types` / `is_nested_inductive_app`
in `~/lean4/src/kernel/inductive.cpp` (I quote line numbers and behaviour, I did not instrument the
kernel); `ParamRedex.lean` §11's `mpAuxB_WF` as the template (used, not re-verified);
`IndexedNested.lean` §1's block data and its `tq_member_built` / `tq_indices` (used as given);
`RecTyped.lean` §3's `MotiveHargs` definition; `docs/handoff-valat.md` §2(c) and
`docs/handoff-faminhab.md` §4b as statements of the two gaps.

## 5. Pick up first

1. **Nothing further is needed on the flag.**  It is settled in both directions and no `Decl.lean`
   edit is proposed.  If a future round wants the last shred: `wiAux` could be given a container
   with constructors, which changes only the companion's `ctors` field and no clause of the
   refutation.
2. **`IotaHargs`' index slots** are the same gap one family over: `docs/handoff-faminhab.md` §8 item
   1 pairs `MotiveHargs`' spine machinery with "the corresponding `IotaHargs` slots", and only the
   former is now exercised.  §6's block is the cheap place to do it — it is canonical, so no β step,
   and `t5Aux_WF` is already available as the input `RecCtx`-style lemmas want.
3. **`Faithful` / `Built` at §6's block.**  Neither §4's nor §6's block has an `OccursN`/`Built`
   instance in the tree; §6's is the better target because Lean really declares it (so its history
   environment is realisable) and because its spine `[γ, T5 γ]` has a **parameter** in it, which
   `KFresh.argsNoK`-style clauses have never been tested against.
4. **Do not** expect a general `MotiveHargs` producer from these: §5/§6 are data, supplied at a
   concrete block, exactly as `docs/handoff-faminhab.md` §5.1 explains.
