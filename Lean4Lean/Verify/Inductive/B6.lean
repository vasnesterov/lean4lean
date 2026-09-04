import Lean4Lean.Verify.Inductive.ClaimB

/-!
# B6: the real restoration — `recArg` populated, and B7's `whnf` gap shut on the map's own output

`Verify/Inductive/SurfaceMap.lean` built the surface→abstract construction and reached
`eraseRecArgs ntreeAux`: every member name, stored type, `indices`, and every constructor's
`name`, `params`, `fields` (types *and* universes) and `args` on the nose — but `recArg = none` at
every field, because `surfIndCtor?` writes `recArg := none` (`SurfaceMap.lean:145`).
`Verify/Inductive/ClaimB.lean` §3 measured the consequence: `VIndField.typeR` is `F.type` on the
`none` branch, so `C.fieldTypesR D R = C.fields.map (·.type)` for **every** `R`, the restoration is
a no-op on the whole field telescope, and the map's output cannot match a user constructor type at
any restoration.  **The blocker was `recArg := none`, not the domain.**  This file removes it.

## What is here

* §1 **the range invariant of the fragment, and the lemma it buys.**  `VExpr.noLam`;
  `noLam_of_ctorTr` (`ctorTr?`'s output is `.lam`-free, *with no hypothesis on the context*, because
  its `.bvar` clause returns the de Bruijn variable itself); `VExpr.noLam_peelPis` (closure under
  the projection the reader applies); `VExpr.betaSpine_eq_mkApp` and
  `VExpr.betaHead_eq_self_of_noLam` (**head β is the identity on a `.lam`-free term** — the general
  form of a fact `Theory/Inductive/MemberRedex.lean:559` states only in prose at a concrete block);
  and the payload `VInductDecl'.recArgOf_eq_recog_of_noLam`: on a `.lam`-free stored type the
  two-stage reader **equals its first stage**, because the two stages are the same call.
* §2 **the header**, which is why two passes are forced and why they are cheap.
  `VIndRestore.recogAt` reads only `tyName k`, `tyLvls k`, `tyArgs k`, and `recog` adds `nm`; at
  `D.idRestore` all four are functions of `Lean4Lean.VIndHeader` — the structure
  `Theory/Inductive/NestedBuild.lean` introduced for exactly this circularity ("an auxiliary
  member's own field types are headed by constants of the block being declared").  So pass 2 needs
  the member *headers* and not the constructors.  §2.1 sharpens it: `recog` inspects only
  `k < nm`, so pass 1's header only has to be right below `nm` (`VIndHeader.recArgOf_congr`).
* §3 **the two-pass map**, as a literal composition:
  `surfInductDeclR? = (surfInductDecl? …).map (surfHeader …).setRecArgsD`.  §3.1 shows pass 2 moves
  no name, no field *type*, no `params`, no `args`, no `tyApp` and no `nameSkelV`; §3.2 is **B6
  part 2**, and the collapse is `VIndField.typeR_id` — `@[simp]` and *unconditional* since ruling
  116d — **not** `VIndRestore.restore_noK`, which asks `VExpr.NoConsts K` of the whole subterm and
  therefore cannot apply to the very field that has to move.
* §4 **B6 part 1**: `recArgOf_surfHeader` — the reader pass 2 ran with **is** the finished block's
  own `VInductDecl'.recArgOf`, as an equation.  That is what makes the two passes well founded
  rather than circular.  `recArg_surfInductDeclR?` then reads off every field, and §4.1/§4.2
  compose with §1: on this map's output the stored `recArg` is the answer of the **single-stage,
  purely syntactic** `VIndRestore.recog` (`recArg_eq_recog_surfInductDeclR?`).  B7's `whnf` gap is
  real in general — `Lean4Lean.ROWit` is a block `Lean4Lean.addDecl` accepts whose field type is a
  β-redex — and it **cannot open here**.
* §5 the three arms at the populated block (`trType`, the supplier-neutral `CtorStoresTr`,
  `trCtors`), transported and not re-proved, plus `surfInductDeclR?_arms_ctorTr` at the `ctorTr?`
  supplier.  §5.1 is **B6 part 3**, *verified rather than redone*: `ClaimB`'s
  `Lean4Lean.ctorStoresTr_of_ctorTr` has `{D}` and `{R}` both free and no `surfInductDecl?`
  hypothesis, so it applies verbatim to a populated block at any restoration — one line.
* §6 the **arity-0 witness** at `InductiveDeclExamples.ntreeAux`, and its headline is one `rfl`:
  `ntreeRTypes_mapsR : surfInductDeclR? … ntreeRTypes = some ntreeAux`.  Not "up to `recArg`" —
  `ntreeAux` itself, the block Lean's nested elimination actually produces.  Three negative
  controls, two of them on the artefact.
* §6.3 **and a finding about `SurfaceMap.lean` §6 that is recorded rather than inherited.**
  `not_oracleSound_vtr?`: `OracleSound (vtr? Us') env Us` is **false at every environment**, because
  `vtr?` translates `.bvar 0` while the empty `VLCtx` has no entry for it — `vtr?` deletes exactly
  the context lookup `ctorTr?`'s `.bvar` clause performs, and that clause is what soundness turns
  on.  So every conjunct of the form `∀ env Us, OracleSound (vtr? …) env Us → …` — four in
  `ntreeAux_surfaceMap_witness`, three carried into `ntreeAux_b6_witness` for continuity — is
  **vacuously true**.  §6.3 therefore supplies the non-vacuous version: `ntreeΓc` (the two block
  constants as a table), `ntreeEnv`, `oracleSound_ntree` (`ClaimB`'s producer, at that table),
  `constLookup_staged_ntree` (through `FlipWiring.lean`'s named lemma), and
  `ntreeRTypes_mapsR_ctorTr` — the two-pass map landing on `ntreeAux` at the **real** `ctorTr?`
  supplier, by `rfl`.  The three arms are then stated at `ntreeEnv` with **no oracle hypothesis at
  all**.

## Structural exclusions

This file imports **exactly one** module, `Lean4Lean.Verify.Inductive.ClaimB`; the closure is
**170** modules (`ClaimB`'s 169 plus this file).  That is wider than `SurfaceMap.lean`'s 148, and
the extra 22 are the price `ClaimB` already paid and disclosed for using a *real* supplier:
`ctorTr?` lives in `Verify.Inductive.TrExprSGeneral`, which sits on
`Verify.Inductive.ExprConstructionScope`, which imports `Verify.Inductive.ValAtParam`, and
`Verify.Inductive.NestedRunInvariant` / `NestedRestoreWit` / `AddDeclWF` come with it.  Nothing in
this file cites any of them.

Measured, not asserted: **35 modules in the tree mention `TrIndDeclN`, `TrIndCtorR` or
`TrIndType`, and this closure contains 20 of them.**  The three unavoidable ones are
`Verify.Environment.Induct` (declares `TrIndDecl`/`TrIndType`),
`Verify.Environment.InductR` (declares `TrIndDeclN`/`TrIndCtorR` and the `exprOf%` elaborator) and
`Verify.Inductive.CtorsLenGeneral` (declares `SkelPrefix`, `TrCtorsLen`, `CtorNameOwn`); the
statements are about their contents.  `Verify.Inductive.SurfaceMap`, `Verify.Inductive.ClaimB`,
`Verify.Inductive.FlipWiring`, `Verify.Inductive.TrExprSGeneral`, `Theory.Inductive.Restore`,
`Theory.Inductive.MemberRedex` and `Theory.Inductive.NestedHead` are likewise disclosed as not
droppable: they declare `surfIndCtor?`/`CtorStoresTr`/`OracleSound`, `recArgOf`/`ctorOracle`,
`ctorTr?`, `VIndField.typeR`/`restore`, `VIndRestore.recog`/`betaHead`/`VIndHeader`, and `ntreeAux`
itself.  The remaining ten in-closure modules — `Verify.Inductive.ValAtParam`,
`NestedRestoreWit`, `AddDeclWF`, `NestedRestore`, `RestrictCompanion`, `SpineClause`,
`ArgsTypedSupply`, `ValAtPrice`, `NestedOccData`, `SpineTransfer` — are inherited through
`ExprConstructionScope` and none of them holds a hand-built `TrIndType` or `TrIndCtorR` instance at
`ntreeAux`; they mention the relation in prose or at other blocks.

**The 15 excluded include every module holding a hand-built `ntreeAux` instance of the thing §6
concludes**: `Verify.Inductive.TrIndDeclNProducer` (the hand-built `ntreeAux`
`trType`/`trCtors` witnesses — and the named consumer for this line of work),
`Verify.Inductive.CtorPointwise`, `Verify.Inductive.TrTypeProducer`,
`Verify.Inductive.TrSpineProducer`, `Verify.Inductive.TrIndDeclNCtorOwn`,
`Verify.Inductive.FlipConstruct` (`tr_ntreeType`, `tr_ntreeNodeType`),
`Verify.Inductive.FlipGeneral`, `Verify.Inductive.FlipRemainder`,
`Verify.Inductive.FragmentWiden`, `Verify.Inductive.RestoreFaithful`,
`Verify.Inductive.RunIdentity`, `Verify.Inductive.SpineClosedLand`,
`Verify.Inductive.HargsAttack`, `Verify.Inductive.StagesFiring`, and
`Verify.Inductive.MemberRedexScan` (the 790-field coverage measurement).  So §6's arms are reached
through §1-§5 and three `rfl`s, and not through any hand-built instance at this block.

Like `SurfaceMap.lean` §6, §6 here uses `InductiveDeclExamples.vtr?` — that file's restatement of
`ctorTr?`'s first component with the environment deleted — so that the witness *computes*.  The
general theorems are stated at `Lean4Lean.OracleNoLam tr`, a range hypothesis both `vtr?`
(`oracleNoLam_vtr?`) and `ctorOracle` (`oracleNoLam_ctorOracle`) satisfy, so §6 is an instance of
the general result and not a parallel track.
-/

set_option autoImplicit false

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 `.lam`-freeness, and why the two-stage reader collapses on the map's output -/

namespace VExpr

/-- **`.lam`-free**, decidably.  `VExpr` has six constructors and `ctorTr?` builds its output
from five of them, so this is the exact range invariant of the fragment. -/
def noLam : VExpr → Bool
  | .bvar _ => true
  | .sort _ => true
  | .const _ _ => true
  | .app f a => f.noLam && a.noLam
  | .lam _ _ => false
  | .forallE A b => A.noLam && b.noLam

@[simp] theorem noLam_bvar {i : Nat} : (VExpr.bvar i).noLam = true := rfl
@[simp] theorem noLam_sort {u : VLevel} : (VExpr.sort u).noLam = true := rfl
@[simp] theorem noLam_const {c : Name} {us : List VLevel} : (VExpr.const c us).noLam = true := rfl
@[simp] theorem noLam_app {f a : VExpr} :
    (VExpr.app f a).noLam = (f.noLam && a.noLam) := rfl
@[simp] theorem noLam_lam {A b : VExpr} : (VExpr.lam A b).noLam = false := rfl
@[simp] theorem noLam_forallE {A b : VExpr} :
    (VExpr.forallE A b).noLam = (A.noLam && b.noLam) := rfl

/-- A `.lam`-free term is not a `.lam`. -/
theorem ne_lam_of_noLam : ∀ {e : VExpr}, e.noLam → ∀ A b, e ≠ .lam A b
  | .bvar _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _
  | .app _ _, _, _, _ | .forallE _ _, _, _, _ => nofun
  | .lam _ _, h, _, _ => by simp at h

/-- `.lam`-freeness passes to the spine head. -/
theorem noLam_spineFn : ∀ {e : VExpr}, e.noLam → e.spineFn.noLam
  | .bvar _, h | .sort _, h | .const _ _, h | .forallE _ _, h => h
  | .app f _, h => by
    simp only [noLam_app, Bool.and_eq_true] at h
    exact noLam_spineFn (e := f) h.1
  | .lam _ _, h => by simp at h

/-- **`betaSpine` does nothing on a non-`.lam` head** — it re-applies the spine it was given.
The general form of `MemberRedex.lean`'s prose observation "the type is `.const`-headed, so
`betaHead` is the identity on it", which was recorded only at concrete blocks. -/
theorem betaSpine_eq_mkApp : ∀ (as : List VExpr) {f : VExpr}, (∀ A b, f ≠ .lam A b) →
    betaSpine as f = f.mkApp as
  | [], _, _ => rfl
  | _ :: _, .bvar _, _ | _ :: _, .sort _, _ | _ :: _, .const _ _, _
  | _ :: _, .app _ _, _ | _ :: _, .forallE _ _, _ => rfl
  | _ :: _, .lam A b, hf => absurd rfl (hf A b)

/-- **The head β step is the identity on a `.lam`-free term.**  This is the lemma that closes the
`whnf` gap wherever it applies: stage 2 of the two-stage reader is then *literally the same call*
as stage 1, not a second chance. -/
theorem betaHead_eq_self_of_noLam {e : VExpr} (h : e.noLam) : betaHead e = e := by
  rw [betaHead, betaSpine_eq_mkApp _ (ne_lam_of_noLam (noLam_spineFn h)),
    mkApp_spineFn_spineArgs]

/-- `.lam`-freeness passes to a peeled `∀`-telescope, entries and body. -/
theorem noLam_peelPis : ∀ {e : VExpr}, e.noLam →
    (∀ A ∈ (peelPis e).1, A.noLam) ∧ (peelPis e).2.noLam
  | .bvar _, h | .sort _, h | .const _ _, h | .app _ _, h => ⟨nofun, h⟩
  | .lam _ _, h => by simp at h
  | .forallE A b, h => by
    obtain ⟨hA, hb⟩ := (by simpa using h : A.noLam ∧ b.noLam)
    refine ⟨fun B hB => ?_, (noLam_peelPis hb).2⟩
    rw [peelPis_forallE] at hB
    rcases List.mem_cons.1 hB with rfl | hB
    · exact hA
    · exact (noLam_peelPis hb).1 B hB

end VExpr

/-- **The two-stage reader collapses to its first stage on a `.lam`-free stored type.**
`VInductDecl'.recArgOf`'s second stage runs `recog` on `VExpr.betaHead S`, and on a `.lam`-free
`S` that term *is* `S`. -/
theorem VInductDecl'.recArgOf_eq_recog_of_noLam {D : VInductDecl'} {i : Nat} {S : VExpr}
    (h : S.noLam) : D.recArgOf i S = D.idRestore.recog D.nm i S := by
  rw [VInductDecl'.recArgOf, VExpr.betaHead_eq_self_of_noLam h]
  cases D.idRestore.recog D.nm i S <;> rfl

/-! ### §1.2 `ctorTr?`'s output is `.lam`-free -/

/-- **THE RANGE INVARIANT.**  `ctorTr?` has clauses for `.sort`, `.bvar`, `.const`, `.app`,
`.forallE` and `.mdata` and returns `none` on everything else — in particular on `.lam` — and the
`.bvar` clause returns the de Bruijn variable itself (`bvarCtx_find?`), so no context entry can
smuggle a `.lam` into the *translation* component.  Hence the fragment's range is `.lam`-free,
with **no** hypothesis on the context. -/
theorem noLam_of_ctorTr {Γc : Name → Option VConstant} {Us : List Name} :
    ∀ (e : Expr) (Γ : List VExpr) (p : VExpr × VExpr), ctorTr? Γc Us e Γ = some p → p.1.noLam
  | .sort u, _, p, h => by
    rw [ctorTr?, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; rfl
  | .bvar i, Γ, p, h => by
    rw [ctorTr?] at h
    rw [(bvarCtx_find? h).1]; rfl
  | .const c us, _, p, h => by
    rw [ctorTr?, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    split at h
    · cases h; rfl
    · exact absurd h nofun
  | .app f a, Γ, p, h => by
    rw [ctorTr?, Option.bind_eq_some_iff] at h
    obtain ⟨p₁, h₁, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨p₂, h₂, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    split at h
    · cases h
      simp [noLam_of_ctorTr f Γ p₁ h₁, noLam_of_ctorTr a Γ p₂ h₂]
    · exact absurd h nofun
  | .forallE _ d b _, Γ, p, h => by
    rw [ctorTr?, Option.bind_eq_some_iff] at h
    obtain ⟨p₁, h₁, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨p₂, h₂, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    simp [noLam_of_ctorTr d Γ p₁ h₁, noLam_of_ctorTr b (p₁.1 :: Γ) p₂ h₂]
  | .mdata _ e, Γ, p, h => by
    rw [ctorTr?] at h; exact noLam_of_ctorTr e Γ p h
  | .fvar _, _, _, h | .mvar _, _, _, h | .lam _ _ _ _, _, _, h
  | .letE _ _ _ _ _, _, _, h | .lit _, _, _, h | .proj _ _ _, _, _, h => by
    simp [ctorTr?] at h

/-- **The oracle-side range hypothesis**, in the style of `Lean4Lean.OracleSound`: the translation
oracle returns `.lam`-free terms.  Stated separately so §4.1's conclusion is available at *any*
supplier with this property, not only at `ctorTr?`. -/
def OracleNoLam (tr : Expr → Option VExpr) : Prop := ∀ e e', tr e = some e' → e'.noLam

/-- …and `ctorOracle` has it, since it is `ctorTr?`'s first component. -/
theorem oracleNoLam_ctorOracle {Γc : Name → Option VConstant} {Us : List Name} :
    OracleNoLam (ctorOracle Γc Us) := by
  intro e e' h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
  exact noLam_of_ctorTr e [] p hp

/-! ## §2 The block **header**: what `recArgOf` actually needs, and why two passes are forced -/

/-- **The identity restoration of a header.**  `VIndRestore.recogAt` reads only `tyName k`,
`tyLvls k` and `tyArgs k`, and `recog` adds `nm`; at `D.idRestore` those four are
`(D.types.getD k default).name`, `D.ownLvls = VLevel.params D.uvars`, `bvars 0 D.params.length`
and `D.types.length` — every one of them a function of `Lean4Lean.VIndHeader`.  So `recArgOf`
needs the block's **member headers** and nothing else: not its constructors, not its fields.
That is the precise sense in which the construction must run in two passes. -/
def VIndHeader.idRestore (H : VIndHeader) : VIndRestore where
  tyName := H.names
  tyLvls _ := VLevel.params H.uvars
  tyArgs _ := VExpr.bvars 0 H.params.length
  ctorName := id
  recName := id

/-- …and it agrees with the block's own identity restoration, by `rfl`. -/
theorem VInductDecl'.header_idRestore (D : VInductDecl') : D.header.idRestore = D.idRestore := rfl

/-- `VInductDecl'.recArgOf`, restated on a header — the form pass 2 can call before the
constructors exist. -/
def VIndHeader.recArgOf (H : VIndHeader) (i : Nat) (S : VExpr) : Option VIndRecArg :=
  (H.idRestore.recog H.nm i S).orElse fun _ => H.idRestore.recog H.nm i (VExpr.betaHead S)

/-- …and it **is** `VInductDecl'.recArgOf`, by `rfl`.  So nothing new is being read: §2 is a
change of *what the reader is applied to*, not of the reader. -/
theorem VIndHeader.recArgOf_header (D : VInductDecl') (i : Nat) (S : VExpr) :
    D.header.recArgOf i S = D.recArgOf i S := rfl

/-! ### §2.1 The recogniser only looks at members `k < nm`

Which is what lets pass 1 supply a header whose `names` is *any* function agreeing with the
finished block below `nm`. -/

private theorem findSome?_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.findSome? f = l.findSome? g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.findSome?_cons, List.findSome?_cons, h a List.mem_cons_self,
      findSome?_congr fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- `recogAt` depends on `R` through exactly three values, at the one index it is given. -/
theorem VIndRestore.recogAt_congr {R R' : VIndRestore} (i k : Nat) (S : VExpr)
    (hn : R.tyName k = R'.tyName k) (hl : R.tyLvls k = R'.tyLvls k)
    (ha : R.tyArgs k = R'.tyArgs k) : R.recogAt i k S = R'.recogAt i k S := by
  rw [VIndRestore.recogAt, VIndRestore.recogAt, hn, hl, ha]

/-- …hence `recog` depends on `R` only **below `nm`**. -/
theorem VIndRestore.recog_congr {R R' : VIndRestore} {nm i : Nat} {S : VExpr}
    (h : ∀ k, k < nm → R.tyName k = R'.tyName k ∧ R.tyLvls k = R'.tyLvls k ∧
      R.tyArgs k = R'.tyArgs k) : R.recog nm i S = R'.recog nm i S := by
  rw [VIndRestore.recog, VIndRestore.recog]
  refine findSome?_congr fun k hk => ?_
  have hk' : k < nm := by simpa using hk
  exact VIndRestore.recogAt_congr i k S (h k hk').1 (h k hk').2.1 (h k hk').2.2

/-- **The header only has to be right below `nm`.**  Two headers with the same universe count,
the same parameter count, the same member count and the same member *names below that count* read
the same `recArg` from every stored type. -/
theorem VIndHeader.recArgOf_congr {H H' : VIndHeader} (hnm : H.nm = H'.nm)
    (hu : H.uvars = H'.uvars) (hp : H.params.length = H'.params.length)
    (hn : ∀ k, k < H'.nm → H.names k = H'.names k) (i : Nat) (S : VExpr) :
    H.recArgOf i S = H'.recArgOf i S := by
  have key : ∀ (T : VExpr), H.idRestore.recog H.nm i T = H'.idRestore.recog H'.nm i T := by
    intro T
    rw [hnm]
    refine VIndRestore.recog_congr fun k hk => ⟨hn k hk, ?_, ?_⟩
    · show VLevel.params H.uvars = VLevel.params H'.uvars
      rw [hu]
    · show VExpr.bvars 0 H.params.length = VExpr.bvars 0 H'.params.length
      rw [hp]
  rw [VIndHeader.recArgOf, VIndHeader.recArgOf, key S, key (VExpr.betaHead S)]

/-! ## §3 The two-pass map: pass 1 is `surfInductDecl?`, pass 2 populates `recArg`

The restructure the predecessor named ("the map must compute the field telescope first and the
`recArg`s second") is *literally* a composition, because §2 shows pass 2 needs only the header,
and §2.1 shows the header only has to be right below `nm`. -/

/-- **Pass 2, at one constructor**: every field keeps its stored type and universe and gains the
`recArg` the reader finds. -/
def VIndHeader.setRecArgs (H : VIndHeader) (C : VIndCtor) : VIndCtor :=
  { C with fields := C.fields.zipIdx.map fun p => { p.1 with recArg := H.recArgOf p.2 p.1.type } }

/-- **Pass 2, at a whole block.** -/
def VIndHeader.setRecArgsD (H : VIndHeader) (D : VInductDecl') : VInductDecl' :=
  { D with types := D.types.map fun T => { T with ctors := T.ctors.map H.setRecArgs } }

/-- **Pass 1's header**, read off the *surface* member list — which is all pass 1 has, and by §2
all pass 2 needs. -/
def surfHeader (uvars : Nat) (ps : List VExpr) (rtypes : List InductiveType) : VIndHeader where
  uvars := uvars
  params := ps
  nm := rtypes.length
  names j := (rtypes.map (·.name)).getD j .anonymous

/-- **THE TWO-PASS CONSTRUCTION.**  `surfInductDecl?` unchanged, then `recArg` populated against
the header. -/
def surfInductDeclR? (tr : Expr → Option VExpr) (uvars : Nat) (ps : List VExpr) (lvl : VLevel)
    (isLE : Bool) (rtypes : List InductiveType) : Option VInductDecl' :=
  (surfInductDecl? tr uvars ps lvl isLE rtypes).map (surfHeader uvars ps rtypes).setRecArgsD

/-! ### §3.1 What pass 2 does not move -/

@[simp] theorem VIndHeader.setRecArgs_name (H : VIndHeader) (C : VIndCtor) :
    (H.setRecArgs C).name = C.name := rfl
@[simp] theorem VIndHeader.setRecArgs_params (H : VIndHeader) (C : VIndCtor) :
    (H.setRecArgs C).params = C.params := rfl
@[simp] theorem VIndHeader.setRecArgs_args (H : VIndHeader) (C : VIndCtor) :
    (H.setRecArgs C).args = C.args := rfl

@[simp] theorem VIndHeader.setRecArgs_fields_length (H : VIndHeader) (C : VIndCtor) :
    (H.setRecArgs C).fields.length = C.fields.length := by
  rw [VIndHeader.setRecArgs]; simp

/-- **The field *types* are untouched** — which is why every statement in `SurfaceMap.lean` §3-§5
transports. -/
theorem VIndHeader.setRecArgs_fieldTypes (H : VIndHeader) (C : VIndCtor) :
    (H.setRecArgs C).fields.map (·.type) = C.fields.map (·.type) := by
  rw [VIndHeader.setRecArgs]
  show (C.fields.zipIdx.map _).map _ = _
  rw [List.map_map]
  refine List.ext_getElem? fun n => ?_
  simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Function.comp_def]

@[simp] theorem VIndHeader.setRecArgsD_uvars (H : VIndHeader) (D : VInductDecl') :
    (H.setRecArgsD D).uvars = D.uvars := rfl
@[simp] theorem VIndHeader.setRecArgsD_params (H : VIndHeader) (D : VInductDecl') :
    (H.setRecArgsD D).params = D.params := rfl
@[simp] theorem VIndHeader.setRecArgsD_lvl (H : VIndHeader) (D : VInductDecl') :
    (H.setRecArgsD D).lvl = D.lvl := rfl
@[simp] theorem VIndHeader.setRecArgsD_isLE (H : VIndHeader) (D : VInductDecl') :
    (H.setRecArgsD D).isLE = D.isLE := rfl

@[simp] theorem VIndHeader.setRecArgsD_nm (H : VIndHeader) (D : VInductDecl') :
    (H.setRecArgsD D).nm = D.nm := by
  simp only [VIndHeader.setRecArgsD, VInductDecl'.nm, List.length_map]

theorem VIndHeader.setRecArgsD_types_getElem? (H : VIndHeader) (D : VInductDecl') (j : Nat) :
    (H.setRecArgsD D).types[j]?
      = (D.types[j]?).map fun T => { T with ctors := T.ctors.map H.setRecArgs } := by
  rw [VIndHeader.setRecArgsD]; exact List.getElem?_map ..

/-- Member names are untouched, at **every** index, defaults included. -/
theorem VIndHeader.setRecArgsD_typeName (H : VIndHeader) (D : VInductDecl') (j : Nat) :
    ((H.setRecArgsD D).types.getD j default).name = (D.types.getD j default).name := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    VIndHeader.setRecArgsD_types_getElem?]
  cases D.types[j]? <;> rfl

/-- …hence the block's own head application is untouched. -/
theorem VIndHeader.setRecArgsD_tyApp (H : VIndHeader) (D : VInductDecl') (j k : Nat)
    (args : List VExpr) : (H.setRecArgsD D).tyApp j k args = D.tyApp j k args := by
  rw [VInductDecl'.tyApp, VInductDecl'.tyApp, VIndHeader.setRecArgsD_typeName]
  rfl

/-- …and the name skeleton, which is what §3 of `SurfaceMap.lean` computes. -/
theorem VIndHeader.setRecArgsD_nameSkelV (H : VIndHeader) (D : VInductDecl') :
    (H.setRecArgsD D).nameSkelV = D.nameSkelV := by
  rw [VInductDecl'.nameSkelV, VInductDecl'.nameSkelV, VIndHeader.setRecArgsD]
  simp [List.map_map, Function.comp_def]

/-! ### §3.2 B6 part 2 — the collapse, re-proved

**And it is not `restore_noK`.**  `VIndField.typeR_id` (`Theory/Inductive/NestedHead.lean:139`) is
`@[simp]` and *unconditional* since ruling 116d: `typeR`'s `some` branch is a **restoration of the
stored type**, and at `idRestore` a restoration is the identity for every expression
(`VIndRestore.restore_id`), canonical or not.  So the collapse does not depend on `recArg` at all,
and the only thing left to check is that pass 2 does not move the *stored data* `VIndCtor.type`
reads — which is §3.1. -/

/-- Pass 2 does not move a constructor's stored type. -/
theorem VIndHeader.setRecArgs_type (H : VIndHeader) (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    (H.setRecArgs C).type D j = C.type D j := by
  rw [VIndCtor.type, VIndCtor.type, VIndCtor.canonResult, VIndCtor.canonResult,
    VIndHeader.setRecArgs_fieldTypes, VIndHeader.setRecArgs_fields_length,
    VIndHeader.setRecArgs_params, VIndHeader.setRecArgs_args]

/-- **B6 PART 2.**  `VIndCtor.typeR` at the identity restoration is unchanged by pass 2 — on both
the constructor and the block. -/
theorem VIndHeader.setRecArgs_typeR (H : VIndHeader) (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    (H.setRecArgs C).typeR (H.setRecArgsD D) (H.setRecArgsD D).idRestore j
      = C.typeR D D.idRestore j := by
  rw [VIndCtor.typeR_id, VIndCtor.typeR_id, VIndCtor.type, VIndCtor.type,
    VIndCtor.canonResult, VIndCtor.canonResult, VIndHeader.setRecArgs_fieldTypes,
    VIndHeader.setRecArgs_fields_length, VIndHeader.setRecArgs_params,
    VIndHeader.setRecArgs_args, VIndHeader.setRecArgsD_tyApp]

/-! ## §4 B6 part 1: the map's own reader **is** the finished block's reader -/

theorem VIndHeader.setRecArgs_fields_getElem? (H : VIndHeader) (C : VIndCtor) (i : Nat) :
    (H.setRecArgs C).fields[i]?
      = (C.fields[i]?).map fun F => { F with recArg := H.recArgOf i F.type } := by
  rw [VIndHeader.setRecArgs]
  show (C.fields.zipIdx.map _)[i]? = _
  simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Function.comp_def,
    Nat.zero_add]

/-- The inversion of the two-pass map: pass 1's output, and that pass 2 produced the answer. -/
theorem surfInductDeclR?_eq_some {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D') :
    ∃ D, surfInductDecl? tr uvars ps lvl isLE rtypes = some D ∧
      (surfHeader uvars ps rtypes).setRecArgsD D = D' :=
  Option.map_eq_some_iff.1 h

private theorem names_of_nameSkelV {D : VInductDecl'} {rtypes : List InductiveType}
    (h : D.nameSkelV = surfNameSkel rtypes) : D.types.map (·.name) = rtypes.map (·.name) := by
  have h2 := congrArg (fun l => l.map Prod.fst) h
  simpa [VInductDecl'.nameSkelV, surfNameSkel, List.map_map, Function.comp_def] using h2

private theorem getD_map_name {l : List VIndType} {k : Nat} (hk : k < l.length) :
    (l.map (·.name)).getD k .anonymous = (l.getD k default).name := by
  have hT : l[k]? = some l[k] := List.getElem?_eq_getElem hk
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, hT]
  rfl

/-- **THE TWO PASSES ARE WELL FOUNDED.**  The reader pass 2 was run with — a reader built from the
*surface* member list, before any constructor existed — is **the finished block's own reader**,
`VInductDecl'.recArgOf` at the output.  Not up to anything: an equation, at every field index and
every stored type.

This is what makes "populate `recArg` via `VInductDecl'.recArgOf`" a legitimate reading of the
declaration rather than a circular one, and it is exactly what §2/§2.1 were for: pass 2 needs the
header, and the header only has to be right below `nm`. -/
theorem recArgOf_surfHeader {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D') (i : Nat) (S : VExpr) :
    (surfHeader uvars ps rtypes).recArgOf i S = D'.recArgOf i S := by
  obtain ⟨D, hD, rfl⟩ := surfInductDeclR?_eq_some h
  obtain ⟨hu, hps, -, -⟩ := surfInductDecl?_data hD
  have hlen : D.types.length = rtypes.length := length_surfInductDecl? hD
  have hnames : D.types.map (·.name) = rtypes.map (·.name) :=
    names_of_nameSkelV (nameSkelV_surfInductDecl? hD)
  rw [← VIndHeader.recArgOf_header]
  refine VIndHeader.recArgOf_congr ?_ ?_ ?_ (fun k hk => ?_) i S
  · show rtypes.length = ((surfHeader uvars ps rtypes).setRecArgsD D).nm
    rw [VIndHeader.setRecArgsD_nm]; exact hlen.symm
  · show uvars = D.uvars
    rw [hu]
  · show ps.length = D.params.length
    rw [hps]
  · show (rtypes.map (·.name)).getD k .anonymous
      = (((surfHeader uvars ps rtypes).setRecArgsD D).types.getD k default).name
    rw [VIndHeader.setRecArgsD_typeName, ← hnames]
    refine getD_map_name ?_
    have hk' : k < ((surfHeader uvars ps rtypes).setRecArgsD D).nm := hk
    rw [VIndHeader.setRecArgsD_nm] at hk'
    exact hk'

/-- **B6 PART 1, at the field.**  Every field of every constructor of the two-pass map's output
carries the `recArg` that the *output block's own* two-stage reader returns on that field's stored
type.  `recArg := none` — the reason the restoration was a no-op — is gone. -/
theorem recArg_surfInductDeclR? {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D')
    {j : Nat} {T : VIndType} (hT : D'.types[j]? = some T)
    {q : Nat} {C : VIndCtor} (hC : T.ctors[q]? = some C)
    {i : Nat} {F : VIndField} (hF : C.fields[i]? = some F) :
    F.recArg = D'.recArgOf i F.type := by
  obtain ⟨D, hD, rfl⟩ := surfInductDeclR?_eq_some h
  rw [VIndHeader.setRecArgsD_types_getElem?, Option.map_eq_some_iff] at hT
  obtain ⟨T₀, hT₀, rfl⟩ := hT
  rw [show ({ T₀ with ctors := T₀.ctors.map (surfHeader uvars ps rtypes).setRecArgs } :
      VIndType).ctors = T₀.ctors.map (surfHeader uvars ps rtypes).setRecArgs from rfl,
    List.getElem?_map, Option.map_eq_some_iff] at hC
  obtain ⟨C₀, hC₀, rfl⟩ := hC
  rw [VIndHeader.setRecArgs_fields_getElem?, Option.map_eq_some_iff] at hF
  obtain ⟨F₀, hF₀, rfl⟩ := hF
  show (surfHeader uvars ps rtypes).recArgOf i F₀.type = _
  exact recArgOf_surfHeader (D' := (surfHeader uvars ps rtypes).setRecArgsD D)
    (Option.map_eq_some_iff.2 ⟨D, hD, rfl⟩) i F₀.type

/-! ### §4.1 …and on this map's output the reader is **single-stage**

Composing §1 with §4: the map's field types are segments of `peelPis` of the oracle's output, so if
the oracle is `ctorTr?` they are `.lam`-free, so `betaHead` is the identity on them, so the two
stages of `recArgOf` are the same call.  The `whnf` gap of B7 **cannot open on the map's own
output**. -/

/-- Every field type the map stores is `.lam`-free when the oracle is `ctorTr?`. -/
theorem noLam_field_surfIndCtor? {tr : Expr → Option VExpr} (hn : OracleNoLam tr)
    {uvars np : Nat} {fl : VLevel} {self : Name} {c : Constructor} {C : VIndCtor}
    (h : surfIndCtor? tr uvars np fl self c = some C)
    {i : Nat} {F : VIndField} (hF : C.fields[i]? = some F) : F.type.noLam := by
  obtain ⟨ct, hct, -, -, -, rfl⟩ := surfIndCtor?_eq_some h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hF
  obtain ⟨A, hA, rfl⟩ := hF
  refine (VExpr.noLam_peelPis (hn _ _ hct)).1 A ?_
  exact List.mem_of_mem_drop (List.mem_of_getElem? hA)

/-! ### §4.2 The descent into the map, and the single-stage conclusion at the block

`SurfaceMap.lean`'s `mapM` helpers are `private`, so the two this needs are re-derived here (they
are eight lines and carry no content). -/

private theorem forall₂_getElem? {α β : Type} {P : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ P l l' →
      ∀ (j : Nat) (a : α) (b : β), l[j]? = some a → l'[j]? = some b → P a b := by
  intro l l' h
  induction h with
  | nil => intro j a b ha; simp at ha
  | cons hab _ ih =>
    intro j a b ha hb
    match j with
    | 0 => cases ha; cases hb; exact hab
    | j+1 => exact ih j a b (by simpa using ha) (by simpa using hb)

private theorem mapM_getElem? {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') (j : Nat) (a : α) (b : β)
    (ha : l[j]? = some a) (hb : l'[j]? = some b) : f a = some b :=
  forall₂_getElem? (List.mapM_eq_some.1 h) j a b ha hb

/-- Every stored field type of the two-pass map's output is `.lam`-free at the `ctorTr?` oracle. -/
theorem noLam_field_surfInductDeclR? {tr : Expr → Option VExpr} (hn : OracleNoLam tr)
    {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D')
    {j : Nat} {t : InductiveType} {T : VIndType} (ht : rtypes[j]? = some t)
    (hT : D'.types[j]? = some T)
    {q : Nat} {c : Constructor} {C : VIndCtor} (hc : t.ctors[q]? = some c)
    (hC : T.ctors[q]? = some C) {i : Nat} {F : VIndField} (hF : C.fields[i]? = some F) :
    F.type.noLam := by
  obtain ⟨D, hD, rfl⟩ := surfInductDeclR?_eq_some h
  rw [VIndHeader.setRecArgsD_types_getElem?, Option.map_eq_some_iff] at hT
  obtain ⟨T₀, hT₀, rfl⟩ := hT
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hC
  obtain ⟨C₀, hC₀, rfl⟩ := hC
  rw [VIndHeader.setRecArgs_fields_getElem?, Option.map_eq_some_iff] at hF
  obtain ⟨F₀, hF₀, rfl⟩ := hF
  exact noLam_field_surfIndCtor? hn (F := F₀)
    (mapM_getElem? (surfIndType?_ctors (mapM_getElem? (surfInductDecl?_types hD) j t T₀ ht hT₀))
      q c C₀ hc hC₀) hF₀

/-- **THE ROUND'S BEST RESULT.**  On the two-pass map's own output at the `ctorTr?` oracle, the
stored `recArg` is the answer of the **single-stage, purely syntactic** recogniser
`VIndRestore.recog` — no head-β step, because there is nothing to contract.  So B7's `whnf` gap,
which is real in general (a declaration `addDecl` accepts can store a β-redex verbatim:
`Lean4Lean.ROWit`), **cannot open on this map's output**. -/
theorem recArg_eq_recog_surfInductDeclR? {tr : Expr → Option VExpr} (hn : OracleNoLam tr)
    {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D')
    {j : Nat} {t : InductiveType} {T : VIndType} (ht : rtypes[j]? = some t)
    (hT : D'.types[j]? = some T)
    {q : Nat} {c : Constructor} {C : VIndCtor} (hc : t.ctors[q]? = some c)
    (hC : T.ctors[q]? = some C) {i : Nat} {F : VIndField} (hF : C.fields[i]? = some F) :
    F.recArg = D'.idRestore.recog D'.nm i F.type := by
  rw [recArg_surfInductDeclR? h hT hC hF,
    VInductDecl'.recArgOf_eq_recog_of_noLam (noLam_field_surfInductDeclR? hn h ht hT hc hC hF)]

/-! ## §5 The map's arms, at the populated block

Nothing here is re-proved: §3.1 says pass 2 moves no name, no stored type and no
`VIndCtor.typeR` at the identity restoration, so every arm of `SurfaceMap.lean` §3-§5 transports. -/

theorem surfInductDeclR?_data {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D') :
    D'.uvars = uvars ∧ D'.params = ps ∧ D'.lvl = lvl ∧ D'.isLE = isLE := by
  obtain ⟨D, hD, rfl⟩ := surfInductDeclR?_eq_some h
  exact surfInductDecl?_data (D := D) hD

/-- **The skeleton equation survives pass 2** — an equation, not a prefix with unknown tail. -/
theorem nameSkelV_surfInductDeclR? {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D') :
    D'.nameSkelV = surfNameSkel rtypes := by
  obtain ⟨D, hD, rfl⟩ := surfInductDeclR?_eq_some h
  rw [VIndHeader.setRecArgsD_nameSkelV]
  exact nameSkelV_surfInductDecl? hD

theorem skelPrefix_surfInductDeclR? {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D') : SkelPrefix rtypes D' :=
  ⟨[], by rw [nameSkelV_surfInductDeclR? h, List.append_nil]⟩

theorem length_surfInductDeclR? {tr : Expr → Option VExpr} {uvars : Nat} {ps : List VExpr}
    {lvl : VLevel} {isLE : Bool} {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D') :
    D'.types.length = rtypes.length := by
  obtain ⟨D, hD, rfl⟩ := surfInductDeclR?_eq_some h
  rw [VIndHeader.setRecArgsD, List.length_map]
  exact length_surfInductDecl? hD

/-- **`TrIndDeclN.trType` at the populated block.**  `TrIndType` reads `T.name` and `T.type`, both
untouched by pass 2. -/
theorem trType_surfInductDeclR? {env : VEnv} {Us : List Name} {tr : Expr → Option VExpr}
    {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D') (hO : OracleSound tr env Us) :
    ∀ (j : Nat) t T, rtypes[j]? = some t → D'.types[j]? = some T → TrIndType env Us t T := by
  obtain ⟨D, hD, rfl⟩ := surfInductDeclR?_eq_some h
  intro j t T ht hT
  rw [VIndHeader.setRecArgsD_types_getElem?, Option.map_eq_some_iff] at hT
  obtain ⟨T₀, hT₀, rfl⟩ := hT
  exact trType_surfInductDecl? hD hO j t T₀ ht hT₀

/-- **The supplier-neutral premise at the populated block.**  `VIndCtor.typeR` at the identity
restoration does not move under pass 2 (`VIndHeader.setRecArgs_typeR`, B6 part 2), so the
proposition is transported and not re-proved. -/
theorem ctorStoresTr_surfInductDeclR? {env : VEnv} {Us : List Name} {tr : Expr → Option VExpr}
    {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D') (hO : OracleSound tr env Us) :
    CtorStoresTr env Us rtypes D' D'.idRestore := by
  obtain ⟨D, hD, rfl⟩ := surfInductDeclR?_eq_some h
  intro j t T ht hT q c C hc hC
  rw [VIndHeader.setRecArgsD_types_getElem?, Option.map_eq_some_iff] at hT
  obtain ⟨T₀, hT₀, rfl⟩ := hT
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hC
  obtain ⟨C₀, hC₀, rfl⟩ := hC
  obtain ⟨hn, ct, htr, heq⟩ := ctorStoresTr_surfInductDecl? hD hO j t T₀ ht hT₀ q c C₀ hc hC₀
  exact ⟨hn, ct, htr, by rw [VIndHeader.setRecArgs_typeR, heq]⟩

/-- **`TrIndDeclN.trCtors` at the populated block**, with the field's own staging. -/
theorem trCtors_surfInductDeclR? {env : VEnv} {Us K : List Name} {tr : Expr → Option VExpr}
    {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? tr uvars ps lvl isLE rtypes = some D')
    (hO : ∀ env₁, env.addIndTypesC D' K = some env₁ → OracleSound tr env₁ Us) :
    ∀ env₁, env.addIndTypesC D' K = some env₁ →
    ∀ (j : Nat) t T, rtypes[j]? = some t → D'.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
      TrIndCtorR env₁ Us D' D'.idRestore j c C :=
  trCtors_of_ctorStoresTr fun env₁ hst => ctorStoresTr_surfInductDeclR? h (hO env₁ hst)

/-- **All three arms at the populated block, at the `ctorTr?` supplier.**  `ClaimB`'s
`surfInductDecl?_arms_ctorTr`, with `recArg` populated. -/
theorem surfInductDeclR?_arms_ctorTr {env : VEnv} {Γc : Name → Option VConstant}
    {Us K : List Name} {uvars : Nat} {ps : List VExpr} {lvl : VLevel} {isLE : Bool}
    {rtypes : List InductiveType} {D' : VInductDecl'}
    (h : surfInductDeclR? (ctorOracle Γc Us) uvars ps lvl isLE rtypes = some D')
    (hΓc : ConstLookup Γc env)
    (hst : ∀ env₁, env.addIndTypesC D' K = some env₁ → ConstLookup Γc env₁) :
    (∀ (j : Nat) t T, rtypes[j]? = some t → D'.types[j]? = some T → TrIndType env Us t T) ∧
    CtorStoresTr env Us rtypes D' D'.idRestore ∧
    (∀ env₁, env.addIndTypesC D' K = some env₁ →
      ∀ (j : Nat) t T, rtypes[j]? = some t → D'.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ Us D' D'.idRestore j c C) :=
  ⟨trType_surfInductDeclR? h (oracleSound_of_ctorTr hΓc),
   ctorStoresTr_surfInductDeclR? h (oracleSound_of_ctorTr hΓc),
   trCtors_surfInductDeclR? h fun env₁ hs => oracleSound_of_ctorTr (hst env₁ hs)⟩

/-! ## §5.1 B6 part 3, verified rather than redone

`ClaimB`'s `Lean4Lean.ctorStoresTr_of_ctorTr` has `{D : VInductDecl'}` and `{R : VIndRestore}` both
free and no `surfInductDecl?` hypothesis, so it applies verbatim to a block whose `recArg`s are
populated, at **any** restoration.  This is that application, in one line — the point being that
the lemma needs no change, so part 3 was indeed already done. -/

/-- **B6 PART 3.**  `ctorStoresTr_of_ctorTr` at the populated block and an arbitrary restoration. -/
theorem ctorStoresTr_of_ctorTr_setRecArgs {env : VEnv} {Γc : Name → Option VConstant}
    {Us : List Name} {rtypes : List InductiveType} {D : VInductDecl'} {H : VIndHeader}
    {R : VIndRestore} (hΓc : ConstLookup Γc env)
    (h : ∀ (j : Nat) t T, rtypes[j]? = some t → (H.setRecArgsD D).types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        c.name = R.ctorName C.name ∧
        ∃ t', ctorTr? Γc Us c.type [] = some (C.typeR (H.setRecArgsD D) R j, t')) :
    CtorStoresTr env Us rtypes (H.setRecArgsD D) R :=
  ctorStoresTr_of_ctorTr hΓc h

/-! ## §6 The arity-0 witness at `ntreeAux` -/

namespace InductiveDeclExamples

/-- §6's oracle has the range property too — same clause list as `ctorTr?`, no `.lam` arm. -/
theorem noLam_of_vtr? {Us : List Name} :
    ∀ (e : Expr) (e' : VExpr), vtr? Us e = some e' → e'.noLam
  | .sort _, _, h => by
    rw [vtr?, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | .bvar _, _, h => by rw [vtr?] at h; cases h; rfl
  | .const _ _, _, h => by
    rw [vtr?, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | .app f a, _, h => by
    rw [vtr?, Option.bind_eq_some_iff] at h
    obtain ⟨f', hf, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    simp [noLam_of_vtr? f f' hf, noLam_of_vtr? a a' ha]
  | .forallE _ d b _, _, h => by
    rw [vtr?, Option.bind_eq_some_iff] at h
    obtain ⟨d', hd, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨b', hb, rfl⟩ := h
    simp [noLam_of_vtr? d d' hd, noLam_of_vtr? b b' hb]
  | .mdata _ e, _, h => by rw [vtr?] at h; exact noLam_of_vtr? e _ h
  | .fvar _, _, h | .mvar _, _, h | .lam _ _ _ _, _, h
  | .letE _ _ _ _ _, _, h | .lit _, _, h | .proj _ _ _, _, h => by simp [vtr?] at h

theorem oracleNoLam_vtr? {Us : List Name} : OracleNoLam (vtr? Us) := noLam_of_vtr?

/-- **THE MAP NOW REPRODUCES `ntreeAux` ON THE NOSE.**  `SurfaceMap.lean`'s `ntreeRTypes_maps`
lands on `eraseRecArgs ntreeAux` — every member name, stored type, `indices`, and every
constructor's `name`, `params`, `fields` (types *and* universes) and `args`, but `recArg = none`
everywhere.  The two-pass map lands on `ntreeAux` itself: `recArg`s included, at the block Lean's
nested elimination actually produces. -/
theorem ntreeRTypes_mapsR :
    surfInductDeclR? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
      ntreeRTypes = some ntreeAux := rfl

/-! ### §6.1 Negative controls -/

/-- **Negative control 1 — on the artefact, and it is a `recArg` control.**  `NTree.node`'s
recursive field applied to `Type u` instead of to the block's parameter `α`.  Every name is still
fresh, the constructor type still translates, and the map still **succeeds** — the guard does not
fire, because the guard looks at the *target*.  But `recogAt`'s parameter-run test
(`sp.take nA = (R.tyArgs k).map (·.liftN _)`) fails, so the field is recorded `recArg = none`.
So `recArg` is **read**, not stamped: change what the companion is applied to and the reader
changes its answer. -/
def ntreeNodeBadE : Expr :=
  .forallE `α (.sort (.succ (.param `u)))
    (.forallE `a (.bvar 0)
      (.forallE `as (.app (.const `_nested.List_1 [.param `u]) (.sort (.param `u)))
        (.app (.const ``NTree [.param `u]) (.bvar 2)) .default) .default) .default

def ntreeRTypesBad : List InductiveType :=
  [{ (ntreeRTypes.headD default) with
      ctors := [{ name := ``NTree.node, type := ntreeNodeBadE }] }] ++ ntreeRTypes.tail

/-- The positive reading, for contrast: at `ntreeAux` the same field is `some ⟨[], 1, []⟩`. -/
theorem ntreeAux_node_field1_recArg :
    (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default).recArg
      = some { binders := [], idx := 1, args := [] } := rfl

/-- …and the control: the map succeeds on the perturbed block and reads `none` there. -/
theorem ntreeRTypesBad_recArg_none :
    (surfInductDeclR? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
       ntreeRTypesBad).isSome = true ∧
    (((((surfInductDeclR? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
        ntreeRTypesBad).getD default).types.getD 0 default).ctors.getD 0
        default).fields.getD 1 default).recArg = none := ⟨rfl, rfl⟩

/-- **Negative control 2 — on the artefact, the map itself refuses a wrong block.**  Rename the
auxiliary member but not the occurrences of it: `_nested.List_2.cons`'s target no longer heads at
its own member, `surfIndCtor?`'s head guard fires, and the two-pass map returns `none` — pass 2
never runs. -/
theorem ntreeRTypesRenamed_failsR :
    surfInductDeclR? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
      ntreeRTypesRenamed = none := rfl

/-- **Negative control 3 — on the premise of §1.**  `noLam` is load-bearing: at `Lean4Lean.ROWit`'s
block, which `Lean4Lean.addDecl` **accepts**, the stored field type is a β-redex, `noLam` is
`false`, `betaHead` genuinely moves it, and the single-stage recogniser and the two-stage reader
**disagree**.  So §1's conclusion is not vacuous — it says something the general case denies. -/
theorem roRedex_not_noLam : ROWit.roField.type.noLam = false := rfl

theorem roRedex_betaHead_ne : VExpr.betaHead ROWit.roField.type ≠ ROWit.roField.type := by decide

theorem roRedex_recog_ne_recArgOf :
    ROWit.roDecl.idRestore.recog ROWit.roDecl.nm 0 ROWit.roField.type
      ≠ ROWit.roDecl.recArgOf 0 ROWit.roField.type := by
  rw [recog_roRedex_none, recArgOf_roRedex]; exact nofun

/-! ### §6.3 The arms are **not** vacuous — and `SurfaceMap.lean` §6's were

**A finding, recorded rather than inherited.**  `SurfaceMap.lean` §6's oracle-dependent conjuncts
are quantified as "for every environment and every *sound* oracle", with the oracle
`InductiveDeclExamples.vtr?`.  That file's docstring already says `vtr?` "is **not** sound on its
own"; `not_oracleSound_vtr?` below makes it exact and machine-checked: `OracleSound (vtr? Us') env Us`
is **false for every `env` and every `Us`**, because `vtr? Us' (.bvar 0) = some (.bvar 0)` while
`TrExprS env Us [] (.bvar 0) (.bvar 0)` needs `VLCtx.find? [] (.inl 0) = some _`, and the empty
`VLCtx` has no entries.  `vtr?` deletes the context lookup that `ctorTr?`'s `.bvar` clause performs,
which is precisely the clause soundness turns on.

Consequence: every conjunct of the form `∀ env Us, OracleSound (vtr? [`u]) env Us → …` — four of
them in `ntreeAux_surfaceMap_witness`, and the three carried over into `ntreeAux_b6_witness` for
continuity — is **vacuously true**.  Their content is the general theorem they instantiate, not the
instance.

So this section supplies the non-vacuous version: a concrete constant table, a concrete
environment where the oracle *is* sound, and the map landing on `ntreeAux` at the **real**
supplier `ctorTr?`. -/

/-- **The refutation.**  `vtr?` is sound at no environment whatever. -/
theorem not_oracleSound_vtr? {env : VEnv} {Us Us' : List Name} :
    ¬ OracleSound (vtr? Us') env Us := by
  intro h
  have H := h (.bvar 0) (.bvar 0) rfl
  cases H with
  | bvar hf => simp [VLCtx.find?] at hf

/-- The two block constants, as a table: both members at `uvars = 1` and stored type
`∀ (α : Type u), Type u`.  `_nested.List_1` is a name Lean never declares, so the table is written
out rather than spliced. -/
def ntreeΓc : Name → Option VConstant := fun n =>
  if n = ``NTree ∨ n = `_nested.List_1 then
    some { uvars := 1, type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))) }
  else none

/-- …and an environment that holds exactly it. -/
def ntreeEnv : VEnv where
  constants := ntreeΓc
  defeqs _ := False

theorem constLookup_ntreeEnv : ConstLookup ntreeΓc ntreeEnv := fun _ _ h => h

/-- …at every *staged* environment too, through `FlipWiring.lean`'s named lemma: every table entry
is already in the pre-block environment, so the block half of the split is never needed.

**VACUOUS at `ntreeEnv`, found 2026-09-04 by `Verify/Inductive/UserBlockR.lean` and confirmed
independently: `example : ntreeEnv.addIndTypesC ntreeAux ntreeK = none := by rfl` elaborates.**  The
antecedent is unsatisfiable because `addConst` fails on a name already present, and
`ntreeAux.typeConstsC ntreeK` re-declares `NTree`, which `ntreeΓc` already holds.  So this statement
is true but says nothing about staging, and it must not be cited as evidence that the staged case is
handled.  The non-vacuous version is `UserBlockR.constLookupU0_staged_witness` (arity 0, cone 515),
stated at the **pre-block** table `ntreeΓcU0` with its antecedent exhibited.  Nothing in `B6` depends
on this lemma; it is kept, marked, as the record of a witness that was not tight. -/
theorem constLookup_staged_ntree {K : List Name} :
    ∀ env₁, ntreeEnv.addIndTypesC ntreeAux K = some env₁ → ConstLookup ntreeΓc env₁ :=
  constLookup_staged_of_split fun _ _ hc => .inr hc

/-- **The oracle really is sound here** — `ClaimB`'s producer at this table.  This is what
`not_oracleSound_vtr?` says `vtr?` can never give. -/
theorem oracleSound_ntree {Us : List Name} : OracleSound (ctorOracle ntreeΓc Us) ntreeEnv Us :=
  oracleSound_of_ctorTr constLookup_ntreeEnv

/-- **…and the two-pass map lands on `ntreeAux` at the real supplier too**, by `rfl`: `ctorTr?`
with this table infers every member and constructor type of the post-elimination block and the
`recArg` reader answers as before.  So `vtr?` was only ever a computational convenience. -/
theorem ntreeRTypes_mapsR_ctorTr :
    surfInductDeclR? (ctorOracle ntreeΓc [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0))
      true ntreeRTypes = some ntreeAux := rfl

/-! ### §6.2 The witness -/

/-- **THE WITNESS — arity 0.**  B6 at `InductiveDeclExamples.ntreeAux`: the parameterised nested
block `inductive NTree (α : Type u) | node : α → List (NTree α) → NTree α` after nested
elimination, `uvars = 1`, two members, one companion.

Everything is reached through the general theorems of §1-§5.  The only block-specific inputs are
three `rfl`s: that the two-pass map succeeds (`ntreeRTypes_mapsR`), that the erasing map lands on
the erasure (`ntreeRTypes_maps`, `SurfaceMap.lean`), and the two negative controls.

Note what has **gone** relative to `SurfaceMap.lean`'s `ntreeAux_surfaceMap_witness`: that witness
had to bridge `eraseRecArgs ntreeAux` and `ntreeAux` by hand at every member, because its map could
only reach the erasure.  Here the map's output **is** `ntreeAux`, so the bridge is not needed and
the arms are quoted at the block itself. -/
theorem ntreeAux_b6_witness :
    -- non-degeneracy: the parameterised nested block, not `nfnAux`
    ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
    ntreeAux.types.length = 2 ∧ ntreeNode.fields.length = 2 ∧
    -- (1) THE TWO-PASS MAP REPRODUCES THE BLOCK EXACTLY, `recArg`s included…
    surfInductDeclR? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
      ntreeRTypes = some ntreeAux ∧
    -- …where the `recArg`-blind map lands strictly short, on the erasure
    surfInductDecl? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
      ntreeRTypes = some (eraseRecArgs ntreeAux) ∧
    -- (2) and the two are genuinely different: the restoration is no longer a no-op
    ntreeNode.recFields.length = 1 ∧
    (((eraseRecArgs ntreeAux).types.getD 0 default).ctors.getD 0 default).recFields.length = 0 ∧
    (((ntreeAux.types.getD 1 default).ctors.getD 1 default)).recFields.length = 2 ∧
    -- (3) PART 1 through the general theorem: the reader pass 2 ran with **is** the finished
    -- block's own reader — so the two passes are well founded, not circular
    (∀ (i : Nat) (S : VExpr),
      (surfHeader 1 [.sort (.succ (.param 0))] ntreeRTypes).recArgOf i S
        = ntreeAux.recArgOf i S) ∧
    -- …and every stored `recArg` is what that reader answers
    (∀ (j : Nat) T, ntreeAux.types[j]? = some T → ∀ (q : Nat) C, T.ctors[q]? = some C →
      ∀ (i : Nat) F, C.fields[i]? = some F → F.recArg = ntreeAux.recArgOf i F.type) ∧
    -- (4) …and the reader is SINGLE-STAGE here: B7's `whnf` gap cannot open on this output
    (∀ (j : Nat) t T, ntreeRTypes[j]? = some t → ntreeAux.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
      ∀ (i : Nat) F, C.fields[i]? = some F →
        F.recArg = ntreeAux.idRestore.recog ntreeAux.nm i F.type) ∧
    -- (5) the skeleton equation survives pass 2, still as an EQUATION
    ntreeAux.nameSkelV = surfNameSkel ntreeRTypes ∧
    SkelPrefix ntreeRTypes ntreeAux ∧ TrCtorsLen ntreeRTypes ntreeAux ∧
    CtorNameOwn ntreeRTypes ntreeAux ∧
    -- (6) PART 2: the collapse at the populated block, and it is `typeR_id`, not `restore_noK`
    (∀ (C : VIndCtor) (j : Nat),
      ((surfHeader 1 [.sort (.succ (.param 0))] ntreeRTypes).setRecArgs C).typeR
        ((surfHeader 1 [.sort (.succ (.param 0))] ntreeRTypes).setRecArgsD (eraseRecArgs ntreeAux))
        ((surfHeader 1 [.sort (.succ (.param 0))] ntreeRTypes).setRecArgsD
          (eraseRecArgs ntreeAux)).idRestore j
        = C.typeR (eraseRecArgs ntreeAux) (eraseRecArgs ntreeAux).idRestore j) ∧
    -- (7) the three arms, at `ntreeAux` itself and at an arbitrary environment and sound oracle
    (∀ (env : VEnv) (Us : List Name), OracleSound (vtr? [`u]) env Us →
      ∀ (j : Nat) t T, ntreeRTypes[j]? = some t → ntreeAux.types[j]? = some T →
        TrIndType env Us t T) ∧
    (∀ (env : VEnv) (Us : List Name), OracleSound (vtr? [`u]) env Us →
      CtorStoresTr env Us ntreeRTypes ntreeAux ntreeAux.idRestore) ∧
    (∀ (env : VEnv) (K Us : List Name),
      (∀ env₁, env.addIndTypesC ntreeAux K = some env₁ → OracleSound (vtr? [`u]) env₁ Us) →
      ∀ env₁, env.addIndTypesC ntreeAux K = some env₁ →
      ∀ (j : Nat) t T, ntreeRTypes[j]? = some t → ntreeAux.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ Us ntreeAux ntreeAux.idRestore j c C) ∧
    -- (8) ANTI-VACUITY.  The three arms above are vacuous as stated, because
    -- `OracleSound (vtr? _) env Us` is false at every environment (`not_oracleSound_vtr?`).
    -- Here is the non-vacuous version: a concrete table, a concrete environment where the oracle
    -- IS sound, the map landing on `ntreeAux` at the real `ctorTr?` supplier, and the three arms
    -- with **no** oracle hypothesis at all.
    (∀ (env : VEnv) (Us : List Name), ¬ OracleSound (vtr? [`u]) env Us) ∧
    surfInductDeclR? (ctorOracle ntreeΓc [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0))
      true ntreeRTypes = some ntreeAux ∧
    (∀ (j : Nat) t T, ntreeRTypes[j]? = some t → ntreeAux.types[j]? = some T →
      TrIndType ntreeEnv [`u] t T) ∧
    CtorStoresTr ntreeEnv [`u] ntreeRTypes ntreeAux ntreeAux.idRestore ∧
    (∀ (K : List Name) env₁, ntreeEnv.addIndTypesC ntreeAux K = some env₁ →
      ∀ (j : Nat) t T, ntreeRTypes[j]? = some t → ntreeAux.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ [`u] ntreeAux ntreeAux.idRestore j c C) ∧
    -- (9) the three negative controls
    ((surfInductDeclR? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
        ntreeRTypesBad).isSome = true ∧
      (((((surfInductDeclR? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
          ntreeRTypesBad).getD default).types.getD 0 default).ctors.getD 0
          default).fields.getD 1 default).recArg = none) ∧
    surfInductDeclR? (vtr? [`u]) 1 [.sort (.succ (.param 0))] (.succ (.param 0)) true
      ntreeRTypesRenamed = none ∧
    ROWit.roField.type.noLam = false ∧
    ROWit.roDecl.idRestore.recog ROWit.roDecl.nm 0 ROWit.roField.type
      ≠ ROWit.roDecl.recArgOf 0 ROWit.roField.type := by
  have hmap := ntreeRTypes_mapsR
  have hskel : ntreeAux.nameSkelV = surfNameSkel ntreeRTypes := nameSkelV_surfInductDeclR? hmap
  have hpre : SkelPrefix ntreeRTypes ntreeAux := skelPrefix_surfInductDeclR? hmap
  exact ⟨rfl, rfl, rfl, rfl, hmap, ntreeRTypes_maps, rfl, rfl, rfl,
    recArgOf_surfHeader hmap,
    fun _ _ hT _ _ hC _ _ hF => recArg_surfInductDeclR? hmap hT hC hF,
    fun _ _ _ ht hT _ _ _ hc hC _ _ hF =>
      recArg_eq_recog_surfInductDeclR? oracleNoLam_vtr? hmap ht hT hc hC hF,
    hskel, hpre, trCtorsLen_of_skelPrefix hpre, ctorNameOwn_of_skelPrefix hpre,
    fun C j => VIndHeader.setRecArgs_typeR _ C _ j,
    fun _ _ hO => trType_surfInductDeclR? hmap hO,
    fun _ _ hO => ctorStoresTr_surfInductDeclR? hmap hO,
    fun _ _ _ hO => trCtors_surfInductDeclR? hmap hO,
    fun _ _ => not_oracleSound_vtr?, ntreeRTypes_mapsR_ctorTr,
    trType_surfInductDeclR? ntreeRTypes_mapsR_ctorTr oracleSound_ntree,
    ctorStoresTr_surfInductDeclR? ntreeRTypes_mapsR_ctorTr oracleSound_ntree,
    fun K => trCtors_surfInductDeclR? (K := K) ntreeRTypes_mapsR_ctorTr
      (fun env₁ hs => oracleSound_of_ctorTr (constLookup_staged_ntree env₁ hs)),
    ntreeRTypesBad_recArg_none, ntreeRTypesRenamed_failsR, roRedex_not_noLam,
    roRedex_recog_ne_recArgOf⟩

end InductiveDeclExamples

/-! ## §7 Axiom checks

Every declaration this file adds, individually, per the process rule: a silently-holed
declaration is caught only by its own `#print axioms` line.  The whitelist is
`propext` / `Quot.sound` / `Classical.choice`; anything else, and `sorryAx` in particular, is a
failure. -/

#print axioms Lean4Lean.VExpr.noLam
#print axioms Lean4Lean.VExpr.noLam_bvar
#print axioms Lean4Lean.VExpr.noLam_sort
#print axioms Lean4Lean.VExpr.noLam_const
#print axioms Lean4Lean.VExpr.noLam_app
#print axioms Lean4Lean.VExpr.noLam_lam
#print axioms Lean4Lean.VExpr.noLam_forallE
#print axioms Lean4Lean.VExpr.ne_lam_of_noLam
#print axioms Lean4Lean.VExpr.noLam_spineFn
#print axioms Lean4Lean.VExpr.betaSpine_eq_mkApp
#print axioms Lean4Lean.VExpr.betaHead_eq_self_of_noLam
#print axioms Lean4Lean.VExpr.noLam_peelPis
#print axioms Lean4Lean.VInductDecl'.recArgOf_eq_recog_of_noLam
#print axioms Lean4Lean.noLam_of_ctorTr
#print axioms Lean4Lean.OracleNoLam
#print axioms Lean4Lean.oracleNoLam_ctorOracle
#print axioms Lean4Lean.VIndHeader.idRestore
#print axioms Lean4Lean.VInductDecl'.header_idRestore
#print axioms Lean4Lean.VIndHeader.recArgOf
#print axioms Lean4Lean.VIndHeader.recArgOf_header
#print axioms Lean4Lean.findSome?_congr
#print axioms Lean4Lean.VIndRestore.recogAt_congr
#print axioms Lean4Lean.VIndRestore.recog_congr
#print axioms Lean4Lean.VIndHeader.recArgOf_congr
#print axioms Lean4Lean.VIndHeader.setRecArgs
#print axioms Lean4Lean.VIndHeader.setRecArgsD
#print axioms Lean4Lean.surfHeader
#print axioms Lean4Lean.surfInductDeclR?
#print axioms Lean4Lean.VIndHeader.setRecArgs_name
#print axioms Lean4Lean.VIndHeader.setRecArgs_params
#print axioms Lean4Lean.VIndHeader.setRecArgs_args
#print axioms Lean4Lean.VIndHeader.setRecArgs_fields_length
#print axioms Lean4Lean.VIndHeader.setRecArgs_fieldTypes
#print axioms Lean4Lean.VIndHeader.setRecArgsD_uvars
#print axioms Lean4Lean.VIndHeader.setRecArgsD_params
#print axioms Lean4Lean.VIndHeader.setRecArgsD_lvl
#print axioms Lean4Lean.VIndHeader.setRecArgsD_isLE
#print axioms Lean4Lean.VIndHeader.setRecArgsD_nm
#print axioms Lean4Lean.VIndHeader.setRecArgsD_types_getElem?
#print axioms Lean4Lean.VIndHeader.setRecArgsD_typeName
#print axioms Lean4Lean.VIndHeader.setRecArgsD_tyApp
#print axioms Lean4Lean.VIndHeader.setRecArgsD_nameSkelV
#print axioms Lean4Lean.VIndHeader.setRecArgs_type
#print axioms Lean4Lean.VIndHeader.setRecArgs_typeR
#print axioms Lean4Lean.VIndHeader.setRecArgs_fields_getElem?
#print axioms Lean4Lean.surfInductDeclR?_eq_some
#print axioms Lean4Lean.names_of_nameSkelV
#print axioms Lean4Lean.getD_map_name
#print axioms Lean4Lean.recArgOf_surfHeader
#print axioms Lean4Lean.recArg_surfInductDeclR?
#print axioms Lean4Lean.noLam_field_surfIndCtor?
#print axioms Lean4Lean.forall₂_getElem?
#print axioms Lean4Lean.mapM_getElem?
#print axioms Lean4Lean.noLam_field_surfInductDeclR?
#print axioms Lean4Lean.recArg_eq_recog_surfInductDeclR?
#print axioms Lean4Lean.surfInductDeclR?_data
#print axioms Lean4Lean.nameSkelV_surfInductDeclR?
#print axioms Lean4Lean.skelPrefix_surfInductDeclR?
#print axioms Lean4Lean.length_surfInductDeclR?
#print axioms Lean4Lean.trType_surfInductDeclR?
#print axioms Lean4Lean.ctorStoresTr_surfInductDeclR?
#print axioms Lean4Lean.trCtors_surfInductDeclR?
#print axioms Lean4Lean.surfInductDeclR?_arms_ctorTr
#print axioms Lean4Lean.ctorStoresTr_of_ctorTr_setRecArgs
#print axioms Lean4Lean.InductiveDeclExamples.noLam_of_vtr?
#print axioms Lean4Lean.InductiveDeclExamples.oracleNoLam_vtr?
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRTypes_mapsR
#print axioms Lean4Lean.InductiveDeclExamples.not_oracleSound_vtr?
#print axioms Lean4Lean.InductiveDeclExamples.ntreeΓc
#print axioms Lean4Lean.InductiveDeclExamples.ntreeEnv
#print axioms Lean4Lean.InductiveDeclExamples.constLookup_ntreeEnv
#print axioms Lean4Lean.InductiveDeclExamples.constLookup_staged_ntree
#print axioms Lean4Lean.InductiveDeclExamples.oracleSound_ntree
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRTypes_mapsR_ctorTr
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNodeBadE
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRTypesBad
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_node_field1_recArg
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRTypesBad_recArg_none
#print axioms Lean4Lean.InductiveDeclExamples.ntreeRTypesRenamed_failsR
#print axioms Lean4Lean.InductiveDeclExamples.roRedex_not_noLam
#print axioms Lean4Lean.InductiveDeclExamples.roRedex_betaHead_ne
#print axioms Lean4Lean.InductiveDeclExamples.roRedex_recog_ne_recArgOf
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_b6_witness

end Lean4Lean
