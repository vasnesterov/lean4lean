# `Built.fields_noK`: the removal assessed, the site list corrected, the replacement chosen

Round: 2026-09-03.  Owner of this round: the `FieldsNoK` stream.
Files changed: `Lean4Lean/Theory/Inductive/FieldsNoK.lean` (§8 added),
`Lean4Lean/Theory/Inductive/NestedBuild.lean` (`VEnv.ConstsClosedC` and `VInductDecl'.KFresh`
lifted above `Built`; `KFresh`'s three theorems added at §F5).  **No existing statement changed.**

Verdict: **outcome 4, with a repair.**  The removal as specified — `fields_noK` replaced by
`hyg : VEnv.KHyg env K` — is *refuted*: it narrows a proved bridge.  A strictly weaker clause,
`VInductDecl'.KFresh`, works at every site, and the whole edit is machine-checked as a model.
The removal itself is **not applied**: it rippled to six files, five outside this stream's grant.

---

## 1. The site list, measured — five, not six

The task relayed a claim of "six `Built`-building sites".  **That is wrong.**  Measured as a
structural query over the compiled environment (every constant whose value or type applies
`Lean4Lean.VInductDecl'.Built.mk`, minus the three auto-generated recursors `rec`/`recOn`/
`casesOn`), there are **five**:

| # | site | file | `KHyg` available? |
| --- | --- | --- | --- |
| 1 | `InductiveDeclExamples.ntreeAux_built` | `Theory/Inductive/NestedBuild.lean` | **yes** — `FieldsNoK.lean` §4.1 `ntreeK_hyg` |
| 2 | `InductiveDeclExamples.nfnAux_built` | `Theory/Inductive/NestedBuild.lean` | **yes** — §4.2 `nfnK_hyg` |
| 3 | `InductiveDeclExamples.nfnAuxDirty_built` | `Theory/Inductive/RestoreBridge.lean` | **yes** — §4.3, same `env`/`K` as #2 |
| 4 | `MRedex.QNWit.qnAux_built` | `Theory/Inductive/MemberRedex.lean` | **yes** — §4.4 `qnK_hyg` |
| 5 | `ElimNestedInductive.Result.RestoreData.mkRestore_built` | `Verify/Inductive/NestedRestoreWit.lean` | **as a hypothesis only** — it carries none of the three; see §2 |

`FieldsNoK.lean` §6.1's producer table was right at five.  Its §4 prose "six" double-counted
`Verify/Inductive/NestedOccData.lean`'s `OccData.mkRestore_built`, which does **not** apply
`Built.mk` — it delegates to `RestoreData.mkRestore_built`.  It is a caller of the site, not a
site.  (`FieldsNoK.lean` §8.0.1 now records the corrected count.)

The same query settles two other §6.1 claims, both confirmed: `Built.fields_noK` has exactly
three users, all consumers (`Built.toFresh`, `Built.toFaithful`,
`InductiveDeclExamples.fields_noK_needs_spine`), and **`Built.toFresh` has zero users** — it is
dead, and the removal should delete rather than port it.

## 2. Why `KHyg` is the wrong clause

Site 5 is the only general one and takes its `fields_noK` from a `BuiltFresh` hypothesis; post-edit
it would take `hyg` the same way.  Its three reduced forms must then supply it:

| reduced form | `constsClosedC` | `notContains` | `isNested` |
| --- | --- | --- | --- |
| `RestoreData.mkRestore_built_of_blockK` (`Verify/Inductive/SpineTransfer.lean`) | `hcc` ✓ | `hK` ✓ | ✓ `h.isNestedName_of_mem hKB` |
| `RestoreData.mkRestore_built_of_spine` (`Verify/Inductive/NestedFreshBridge.lean`) | `hcc` ✓ | `hK` ✓ | **✗** |
| `OccData.mkRestore_built` (`Verify/Inductive/NestedOccData.lean`) | hypothesis | hypothesis | hypothesis |

`mkRestore_built_of_spine` has no route to `isNested`: `RestoreData.isNestedName_of_mem` needs
`hKB : ∀ n ∈ K, n ∈ D.blockNames`, which is exactly the hypothesis `mkRestore_built_of_blockK`
*adds* and `_of_spine` deliberately does without.  So carrying `KHyg` on `Built` would cost the
weaker of the two reduced bridges a genuinely new hypothesis — it would **narrow a proved
result**, which is the same failure mode the `Occurs`-strengthening was rejected for.

## 3. The weaker clause that does suffice: `VInductDecl'.KFresh`

Measured, not chosen.  Every one of the four `Theory/`-side `fields_noK :=` bodies is literally

    VNestedOcc.fields_noK_of_occurs hcc <occurs> hK <args_noK> hC₀ hF₀

with `<args_noK>` being `listOcc_args_noK`, `pfnOcc_args_noK` (twice) and `qnOcc_args_noK` — all
`by decide`.  Site 5 takes the same list through `BuiltFresh`.  So what the sites have in hand is
`fields_noK_of_occurs`'s premise list, and that is what `KFresh` bundles
(`Theory/Inductive/NestedBuild.lean`, Part 6):

    structure VInductDecl'.KFresh (D) (K) (env) (occ) : Prop where
      constsClosedC : env.ConstsClosedC
      notContains   : ∀ n ∈ K, ¬ env.contains n
      argsNoK       : ∀ j T, D.types[j]? = some T → T.name ∈ K →
                        ∀ a ∈ (occ j).args, VExpr.NoConsts K a

Ordering, both directions machine-checked in `FieldsNoK.lean` §8:

* `KHyg` ⟹ `KFresh`, given `Built.occurs` (§8.2 `KFresh.of_khyg`, `Built'.toBuilt''` §8.6).
* `KFresh` ⇏ `KHyg` (§8.3 `kfresh_not_khyg`): at `K = ntreeK ++ [`Junk]` and `env₁`, `KFresh`
  holds — `Junk` is undeclared and `listOcc.args = [NTree α]` mentions neither name — and `KHyg`
  fails, on `isNested`.  That is `mkRestore_built_of_spine`'s exact position.
* `KFresh.of_spine hcc hK hspine ha` (`NestedBuild.lean` §F5) is `KFresh` from
  `mkRestore_built_of_spine`'s **own** hypotheses, so that site's edit is a one-line splice.
* `KFresh.fields_noK_of_occurs` needs only `Occurs`, not `OccursN`. So the `KFresh` route does
  **not** depend on the `OccursN` retype — a difference from §3's `KHyg` route worth recording.

## 4. The prerequisite no earlier round named

Both candidate clauses mention `VEnv.ConstsClosedC`, and `NestedBuild.lean` defined that at §F2.1
— **after** `VInductDecl'.Built`.  A field of `Built` can only mention what precedes `Built`, so
until `ConstsClosedC` was lifted **neither `KHyg` nor `KFresh` could be a field at all**.
Measured: placing `KFresh` above `Built` with `ConstsClosedC` left at §F2.1 gave four
`invalidField` errors and `sorryAx`-tainted two theorems.

`§7`'s `Built'` model could not have detected this, and neither can `§8.4`'s `Built''`: a model
stated in `FieldsNoK.lean` sits downstream of `NestedBuild.lean` with everything in scope.  This
round fixed it: `NestedBuild.lean` Part 6 now declares `VEnv.ConstsClosedC` and
`VInductDecl'.KFresh` immediately above `Built`, with `KFresh`'s three theorems left at §F5 where
`VNestedOcc.fields_noK_of_occurs` is in scope.  Pure relocation; no statement changed.

A consequence that is part of the diff: `Built.toFresh` sits *between* `Built` and §F5, so it
cannot read the replacement projection.  Delete it — it has zero users.

## 5. The edit, per file.  Six files; five outside this stream's grant

Everything below is proved as a model in `FieldsNoK.lean` §8.4–§8.11 (`Built''`, its
`fields_noK`/`toFresh`/`toFaithful`, `ntreeAux_built''`, `fields_noK_needs_spine''`), each with the
original's proof term and axiom set `[propext, Quot.sound]`.  `NestedFresh.lean`'s
`fields_noK_needs_spine` is `§8.11`'s model verbatim, positional application included.

1. **`Theory/Inductive/NestedBuild.lean`** *(this stream's grant; prerequisite done, edit not)*
   * `Built`: delete `fields_noK`, add `kfresh : D.KFresh K env occ`.
   * delete `Built.toFresh` (dead).
   * after §F5, add `theorem VInductDecl'.Built.fields_noK (h) := h.kfresh.fields_noK_of_occurs
     fun j T hT hK => (h.occurs j T hT hK).toOccurs` — `FieldsNoK.lean` §8.5 is this proof term.
   * `ntreeAux_built`: `fields_noK := …` → `kfresh := ⟨listEnv_constsClosedC h,
     ntreeK_not_contains h, fun _ _ _ _ => listOcc_args_noK⟩` (§8.10 checks exactly this).
   * `nfnAux_built`: → `kfresh := ⟨pfnEnv_constsClosedC h, nfnK_not_contains h,
     fun _ _ _ _ => pfnOcc_args_noK⟩`.  `nfnAux_builtFresh` stays (it is a `BuiltFresh`).
   * `Built.toFaithful`: **unchanged** (§8.8).
2. **`Theory/Inductive/RestoreBridge.lean`** — `nfnAuxDirty_built`: same substitution as
   `nfnAux_built`; the three arguments are already in the file.
3. **`Theory/Inductive/MemberRedex.lean`** — `qnAux_built`: `kfresh := ⟨qjEnv_constsClosedC h,
   qnK_not_contains h, fun _ _ _ _ => qnOcc_args_noK⟩`.  `qnAux_builtFresh` stays.
4. **`Verify/Inductive/NestedRestoreWit.lean`** — `mkRestore_built`: replace
   `(hf : D.BuiltFresh K occ)` by `(hnd : D.blockNames.Nodup) (hkf : D.KFresh K env occ)`;
   `nodup := hnd`, `kfresh := hkf`, `fields_noK :=` line gone.  Then thread the two arguments
   through `mkRestore_faithful`, `mkRestore_AddNested`, `mkRestore_AddNestedStep`, and at
   `nfnAux_built'` pass `(by decide)` and `⟨pfnEnv_constsClosedC h, nfnK_not_contains h,
   fun _ _ _ _ => pfnOcc_args_noK⟩` in place of `(nfnAux_builtFresh h)`.
5. **`Verify/Inductive/NestedOccData.lean`** — `OccData.mkRestore_built` and
   `OccData.mkRestore_faithful`: same `hf → hnd, hkf` swap, passed straight through.
6. **`Verify/Inductive/NestedFreshBridge.lean`** — `mkRestore_built_of_spine`: its inline
   `VInductDecl'.builtFresh_of_occurs hcc hnd … hK (fun j T hT hKT a hmem => hspine … )`
   becomes `hnd` plus `VInductDecl'.KFresh.of_spine hcc hK hspine ha`.  The spine/`ha` shuffle
   currently written inline **is** `of_spine`'s body, so this shortens the proof rather than
   changing it.  `mkRestore_AddNested_of_spine` and `nfnAux_built'_of_spine`: unchanged.
7. **`Verify/Inductive/SpineTransfer.lean`** — **zero edits.**  `mkRestore_built_of_blockK` and
   `mkRestore_AddNested_of_blockK` delegate to `_of_spine`, whose signature does not change.

Ripple: six files, ~11 declarations.  Every retype meets the "existing proof term accepted
unchanged" bar except item 6, which gets *shorter*.  Five of the six files are outside this
stream's grant, which is why the edit is stated here and not applied.

## 6. Anti-vacuity

* **`KFresh` is inhabited** at a non-empty `K`: `ntreeAux_built''` (§8.10) has one, at
  `K = ntreeK` and `env₁ = the environment of VEnv.empty.addInduct' listDecl`, supplied by `rfl`.
  `kfresh_not_khyg` (§8.3) gives a second at the widened `K`.  Both are **hole-free**: the whole
  of `FieldsNoK.lean` and `NestedBuild.lean` reports `[propext, Quot.sound]` or weaker under
  `#print axioms`, with no `sorryAx`.  *(Inhabitation and hole-freeness are separate claims and
  both hold here; neither witness routes through a hole.)*  Neither witness environment is
  inconsistent: `env₁` is `VEnv.empty` plus `listDecl`, and the file's own
  `listEnv_constsClosedC`/`listEnv_ordered` are proved of it.
* **`KHyg` is inhabited** — `khyg_inhabited` (§5.1), unchanged from the previous round.
* **Each clause is a real restriction**: `isNested` §5.2, `notContains` §5.3, and now the
  separation of `KFresh` from `KHyg` §8.3.
* **The four controls the task named still hold, with the same axiom sets** — re-run this round:
  `VNestedOcc.occurs_args_congr`, `InductiveDeclExamples.listOccBadSpine_occurs`,
  `InductiveDeclExamples.fields_noK_needs_spine` (all `Theory/Inductive/NestedFresh.lean`) and
  `InductiveDeclExamples.occursN_args_congr_false` (`Verify/Inductive/OccArgsTyping.lean`), each
  `[propext, Quot.sound]`.  Nothing in this round touches `Occurs`.

## 7. Verification

* `lake build`: **my whole cone green**, target by target — `Theory.Inductive.NestedBuild` 64
  jobs, `.FieldsNoK` 70, `.NestedFresh` 65, `.RestoreBridge` 67, `.MemberRedex` 65,
  `Verify.Inductive.NestedRestoreWit` 159, `.NestedOccData` 188, `.NestedFreshBridge` 161,
  `.SpineTransfer` 176, `.OccArgsTyping` 178, `Verify.Guard` 1144.  A whole-tree `lake build`
  at 08:13 failed on `Lean4Lean.Theory.Typing.ShapeVar` — an **untracked file a concurrent stream
  was editing 5 s earlier**, not this round's — plus one racing `Verify/TypeChecker.olean`.
  Baseline before this round's edits: 1555 jobs green.
* Guards: `guard 1: 24 frozen axioms ✓` / `guard 2: whitelist ✓ (proof INCOMPLETE: sorryAx
  present)` / `guard 3: 2/2 remaining ✓`.
* `scripts/sorry-census-all.lean`: 374 modules built, **0 in population but NOT BUILT**, 13 holes
  — all pre-existing, none in `Theory/Inductive/`.
* `scripts/dup-names.lean`: no duplicates.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is empty.

## 8. Pick up first

1. Ask the human to apply §5, in the order 1 → 4 → 5 → 6 → 2 → 3.  The prerequisite (§4) is
   already landed, so item 1's structure edit compiles the moment it is made.
2. When it lands, delete `FieldsNoK.lean` §7 and §8.4–§8.11 (the two models) and keep §8.0–§8.3
   and §8.12 — the corrections and the ordering are the durable content.
3. `VEnv.KHyg` (§2) then has **one** remaining user, §8.2.  Either keep it as the recorded
   stronger candidate or delete it; it is not needed by the edit.
