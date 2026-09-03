import Lean4Lean.Verify.Inductive.SpineTransfer
import Lean4Lean.Theory.Typing.StrengthenAxiom

/-!
# `hproj`, split: the stored half of `projTerm`, and the environment route

`Verify/Inductive/Add.lean`'s `TrExprS.noConsts` and `SpineTransfer.lean`'s `TrExprS.noConstIn`
both carry one undischarged side condition,

    hproj : ∀ Γ s i x y, TrProj env U Γ s i x y → x.NoConstIn P → y.NoConstIn P

and handoff §60.9 recorded it as "the only one nobody has *any* route to", with §60.10 asking for
its **stored half**: a `NoConstIn` fact for everything `VInductDecl'.projTerm` splices in *except*
the parameter/index spine `ps`/`ιs`.  This file has both halves of that and one thing the brief
did not expect:

* §1 the closure library for `VExpr.ConstsIn` at a *predicate* — `mkApp`, `mkPi`, `mkLams`,
  `instAll`, `instAllTele`, `bvars`, `liftTele` — and `NoConstIn P ↔ ConstsIn (¬ P ·)`, so that
  `Theory/SetModel/Consts.lean`'s existing `instL`/`liftN`/`inst`/`mono` are reusable here.
  (The same closure lemmas exist for `VExpr.NoConsts` at a `List Name`
  — `noConsts_instAll`, `noConsts_mkPi_binders` in `Theory/Inductive/NestedBuild.lean`,
  `noConsts_mkApp`, `noConsts_bvars` in `Theory/Inductive/IndexedNested.lean` — and do **not**
  transfer: `IsNestedName` is not `(· ∉ S)` for any finite `S`.)
* §2 **the stored half, proved**: `projTerm_constsIn`, with no environment, no `WF` and no
  typing.  Its residual hypotheses are exactly `ps`, `ιs` and the subject.
* §3 the stored data bounded by an environment invariant, and the invariant reduced: the
  *name* clause is the whole content, because `VEnv.ConstsClosedC` already bounds every declared
  type by the declared names.  So §60.5's `VEnv.NoNestedC` is **derivable**, not a second
  assumption.
* §4 **`hproj` in full, discharged** — not just the stored half.  A `TrProj`'s output is well
  typed (`TrProj.wf`, proved, `Verify/Typing/Lemmas.lean`), a well-typed term mentions only
  declared constants (`VEnv.Ordered.constsIn`), and no declared constant carries the reserved
  prefix (§3's name invariant).  So the `ps`/`ιs` half needs **no** canonical-spine
  strengthening of `TrProj`: it needs the subject to be well typed.  §60.10 item 1 and
  `Add.lean`'s recorded residual are both aimed at the wrong obligation.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars instAll instAllTele liftTele)

/-! ## §1 `ConstsIn` at a predicate: the closure library

`VExpr.ConstsIn : VExpr → (Name → Prop) → Prop` (`Theory/SetModel/Consts.lean`) already has
`mono`, `instL`, `liftN`, `instVar` and `inst`.  What `projCore` needs on top of that is the
telescope algebra of `Theory/Inductive/Telescope.lean`. -/

namespace VExpr

variable {P : Name → Prop}

/-- `NoConstIn` is `ConstsIn` at the complement.  Companion to `noConsts_iff_constsIn`
(`Theory/Inductive/NestedBuild.lean`), which does the same for the `List Name` form. -/
theorem noConstIn_iff_constsIn : ∀ {e : VExpr}, e.NoConstIn P ↔ e.ConstsIn (fun c => ¬ P c)
  | .bvar _ | .sort _ => iff_of_true trivial trivial
  | .const .. => .rfl
  | .app .. | .lam .. | .forallE .. =>
    and_congr noConstIn_iff_constsIn noConstIn_iff_constsIn

theorem constsIn_mkApp {f : VExpr} (hf : f.ConstsIn P) :
    ∀ {as : List VExpr}, (∀ a ∈ as, a.ConstsIn P) → (f.mkApp as).ConstsIn P
  | [], _ => hf
  | a :: as, ha =>
    constsIn_mkApp (f := .app f a) ⟨hf, ha a List.mem_cons_self⟩
      (as := as) fun b hb => ha b (List.mem_cons_of_mem _ hb)

theorem constsIn_mkLams : ∀ {as : List VExpr} {b : VExpr}, (∀ a ∈ as, a.ConstsIn P) →
    b.ConstsIn P → (mkLams as b).ConstsIn P
  | [], _, _, hb => hb
  | _ :: _, _, ha, hb =>
    ⟨ha _ List.mem_cons_self,
     constsIn_mkLams (fun c hc => ha c (List.mem_cons_of_mem _ hc)) hb⟩

theorem constsIn_mkPi : ∀ {as : List VExpr} {b : VExpr}, (∀ a ∈ as, a.ConstsIn P) →
    b.ConstsIn P → (mkPi as b).ConstsIn P
  | [], _, _, hb => hb
  | _ :: _, _, ha, hb =>
    ⟨ha _ List.mem_cons_self,
     constsIn_mkPi (fun c hc => ha c (List.mem_cons_of_mem _ hc)) hb⟩

@[simp] theorem constsIn_bvars : ∀ {lo n : Nat}, ∀ a ∈ bvars lo n, a.ConstsIn P
  | _, 0, _, h => absurd h (by simp [bvars])
  | lo, n+1, a, h => by
    rw [bvars, List.mem_cons] at h
    rcases h with rfl | h
    · trivial
    · exact constsIn_bvars (lo := lo) (n := n) a h

theorem constsIn_instAll : ∀ {as : List VExpr} {e : VExpr} {k : Nat}, e.ConstsIn P →
    (∀ a ∈ as, a.ConstsIn P) → (e.instAll as k).ConstsIn P
  | [], _, _, h, _ => h
  | a :: as, e, k, h, ha => by
    rw [instAll]
    exact constsIn_instAll (as := as) ((ha a List.mem_cons_self).inst h)
      (fun b hb => ha b (List.mem_cons_of_mem _ hb))

theorem constsIn_instAllTele : ∀ {As as : List VExpr} {k : Nat}, (∀ A ∈ As, A.ConstsIn P) →
    (∀ a ∈ as, a.ConstsIn P) → ∀ B ∈ instAllTele As as k, B.ConstsIn P
  | [], _, _, _, _ => nofun
  | A :: As, as, k, hA, ha => by
    intro B hB
    rw [instAllTele, List.mem_cons] at hB
    rcases hB with rfl | hB
    · exact constsIn_instAll (hA A List.mem_cons_self) ha
    · exact constsIn_instAllTele (As := As)
        (fun C hC => hA C (List.mem_cons_of_mem _ hC)) ha B hB

theorem constsIn_liftTele : ∀ {n : Nat} {As : List VExpr} {k : Nat},
    (∀ A ∈ As, A.ConstsIn P) → ∀ B ∈ liftTele n As k, B.ConstsIn P
  | _, [], _, _ => nofun
  | n, A :: As, k, hA => by
    intro B hB
    rw [liftTele, List.mem_cons] at hB
    rcases hB with rfl | hB
    · exact ConstsIn.liftN.2 (hA A List.mem_cons_self)
    · exact constsIn_liftTele (n := n) (As := As)
        (fun C hC => hA C (List.mem_cons_of_mem _ hC)) B hB

/-- …and the entries a telescope read out of range produces are constant-free, which is what
lets `projCore`'s `C.fields.getD i default` be handled without an index side condition. -/
@[simp] theorem constsIn_default : (default : VExpr).ConstsIn P := trivial

/-! ### §1.1 The inverse direction

`§3` reads stored telescopes *out of* a declared type, so it needs each of the three
operations backwards. -/

/-- A pi telescope's binders inherit `ConstsIn` from the telescope.  `ConstsIn` twin of
`noConsts_mkPi_binders` (`Theory/Inductive/NestedBuild.lean`). -/
theorem constsIn_mkPi_binders : ∀ {as : List VExpr} {b : VExpr}, (mkPi as b).ConstsIn P →
    ∀ a ∈ as, a.ConstsIn P
  | [], _, _ => nofun
  | _ :: as, b, h => by
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact constsIn_mkPi_binders (as := as) (b := b) h.2 c hc

/-- `mkApp`, backwards. -/
theorem constsIn_mkApp_inv : ∀ {as : List VExpr} {f : VExpr}, (f.mkApp as).ConstsIn P →
    f.ConstsIn P ∧ ∀ a ∈ as, a.ConstsIn P
  | [], _, h => ⟨h, nofun⟩
  | a :: as, f, h => by
    obtain ⟨⟨hf, ha⟩, has⟩ := constsIn_mkApp_inv (as := as) (f := .app f a) h
    refine ⟨hf, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ha
    · exact has b hb

/-- `liftTele`, backwards: it is not a `map` (the lift depth grows with the index), so
membership has to be traced through the recursion. -/
theorem constsIn_of_liftTele {n : Nat} : ∀ {As : List VExpr} {k : Nat},
    (∀ B ∈ liftTele n As k, B.ConstsIn P) → ∀ A ∈ As, A.ConstsIn P
  | [], _, _ => nofun
  | _ :: As, k, h => by
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · exact ConstsIn.liftN.1 (h _ (by rw [liftTele]; exact List.mem_cons_self ..))
    · exact constsIn_of_liftTele (As := As)
        (fun C hC => h C (by rw [liftTele]; exact List.mem_cons_of_mem _ hC)) B hB

/-- …and `instL` entrywise, backwards, which is `VInductDecl'.atRecTele`. -/
theorem constsIn_of_map_instL {ls : List VLevel} {As : List VExpr}
    (h : ∀ B ∈ As.map (VExpr.instL ls), B.ConstsIn P) : ∀ A ∈ As, A.ConstsIn P :=
  fun _ hA => ConstsIn.instL.1 (h _ (List.mem_map_of_mem hA))

end VExpr


#print axioms Lean4Lean.VExpr.noConstIn_iff_constsIn
#print axioms Lean4Lean.VExpr.constsIn_mkApp
#print axioms Lean4Lean.VExpr.constsIn_instAllTele
#print axioms Lean4Lean.VExpr.constsIn_mkPi_binders
#print axioms Lean4Lean.VExpr.constsIn_of_liftTele

/-! ## §2 The stored half of `hproj`, proved

`VInductDecl'.projTerm` (`Theory/Inductive/Structure.lean`) splices in, besides its explicit
arguments `ps`/`ιs`/`e`:

* the recursor constant `Lean.mkRecName T.name`, as the head;
* the block constant `T.name`, in the motive's major-premise binder;
* the index telescope `T.indices`, as the motive's own binder telescope;
* the field types `C.fields.map (·.type)`, as the minor premise's binder telescope, and field
  `i`'s type as the motive's body;
* `bvars`, and the earlier projections threaded by `projArgs`.

Everything on that list is bounded below.  **No environment, no `WF`, no typing** — the residual
is exactly `ps`, `ιs` and the subject, which is what §60.10 asked the split to isolate. -/

variable {P : Name → Prop}

/-- The field a `getD` reads is either a real field or `default`, and `default`'s type is
constant-free, so `projCore`'s `C.fields.getD i default` needs no index side condition. -/
theorem VIndCtor.constsIn_getD_type {C : VIndCtor} (hfld : ∀ F ∈ C.fields, F.type.ConstsIn P)
    (i : Nat) : ((C.fields.getD i default).type).ConstsIn P := by
  rw [List.getD_eq_getElem?_getD]
  cases h : C.fields[i]? with
  | none => exact VExpr.constsIn_default
  | some F => exact hfld F (List.mem_of_getElem? h)

/-- The motive `projCore` hands the recursor. -/
theorem VIndType.projMotive_constsIn {T : VIndType} {C : VIndCtor} {us : List VLevel}
    {ps is : List VExpr} {i : Nat} {earlier : List VExpr}
    (hT : P T.name) (hidx : ∀ A ∈ T.indices, A.ConstsIn P)
    (hfld : ∀ F ∈ C.fields, F.type.ConstsIn P) (hps : ∀ p ∈ ps, p.ConstsIn P)
    (hearlier : ∀ a ∈ earlier, a.ConstsIn P) :
    (T.projMotive C us ps is i earlier).ConstsIn P := by
  refine VExpr.constsIn_mkLams
    (VExpr.constsIn_instAllTele (fun A₀ hA₀ => ?_) hps) ⟨?_, ?_⟩
  · obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hA₀
    exact VExpr.ConstsIn.instL.2 (hidx A hA)
  · refine VExpr.constsIn_mkApp (f := .const T.name us) hT fun a ha => ?_
    rcases List.mem_append.1 ha with h | h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact VExpr.ConstsIn.liftN.2 (hps p hp)
    · exact VExpr.constsIn_bvars a h
  · refine VExpr.constsIn_instAll
      (VExpr.ConstsIn.instL.2 (VIndCtor.constsIn_getD_type hfld i)) fun a ha => ?_
    rcases List.mem_append.1 ha with h | h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact VExpr.ConstsIn.liftN.2 (hps p hp)
    · exact hearlier a h

/-- The minor premise `projCore` hands the recursor: only the field telescope occurs. -/
theorem VIndCtor.projMinor_constsIn {C : VIndCtor} {us : List VLevel} {ps : List VExpr}
    {i : Nat} (hfld : ∀ F ∈ C.fields, F.type.ConstsIn P) (hps : ∀ p ∈ ps, p.ConstsIn P) :
    (C.projMinor us ps i).ConstsIn P :=
  VExpr.constsIn_mkLams (VExpr.constsIn_instAllTele (fun A₀ hA₀ => by
    obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hA₀
    exact VExpr.ConstsIn.instL.2 (hfld F hF)) hps) trivial

namespace VInductDecl'

variable {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}

/-- **`projCore`, bounded.**  `projCore_eq` presents it as a recursor application, and every
argument is covered by §1. -/
theorem projCore_constsIn (hrec : P (Lean.mkRecName T.name)) (hT : P T.name)
    (hidx : ∀ A ∈ T.indices, A.ConstsIn P) (hfld : ∀ F ∈ C.fields, F.type.ConstsIn P) :
    ∀ {ps is earlier : List VExpr} {i : Nat} {e : VExpr}, (∀ p ∈ ps, p.ConstsIn P) →
      (∀ a ∈ is, a.ConstsIn P) → (∀ a ∈ earlier, a.ConstsIn P) → e.ConstsIn P →
      (D.projCore T C us ps is i earlier e).ConstsIn P := by
  intro ps is earlier i e hps his hearlier he
  rw [projCore_eq]
  refine VExpr.constsIn_mkApp (f := .const _ _) hrec fun a ha => ?_
  rcases List.mem_append.1 ha with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hps a h
      · rcases List.mem_cons.1 h with rfl | h
        · exact VIndType.projMotive_constsIn hT hidx hfld hps hearlier
        · rcases List.mem_cons.1 h with rfl | h
          · exact VIndCtor.projMinor_constsIn hfld hps
          · exact absurd h (by simp)
    · exact his a h
  · rcases List.mem_cons.1 h with rfl | h
    · exact he
    · exact absurd h (by simp)

/-- **`projArgs`, bounded.**  The recursion re-lifts the parameters and replaces the index
arguments by `bvars`, both of which §1 covers, so the induction on `i` goes through with `ps`
and `is` generalised. -/
theorem projArgs_constsIn (hrec : P (Lean.mkRecName T.name)) (hT : P T.name)
    (hidx : ∀ A ∈ T.indices, A.ConstsIn P) (hfld : ∀ F ∈ C.fields, F.type.ConstsIn P) :
    ∀ (i : Nat) {ps is : List VExpr}, (∀ p ∈ ps, p.ConstsIn P) → (∀ a ∈ is, a.ConstsIn P) →
      ∀ a ∈ D.projArgs T C us ps is i, a.ConstsIn P
  | 0, _, _, _, _ => by rw [projArgs]; exact nofun
  | i+1, ps, is, hps, his => by
    rw [projArgs]
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact projArgs_constsIn hrec hT hidx hfld i hps his a h
    · rcases List.mem_cons.1 h with rfl | h
      · exact projCore_constsIn hrec hT hidx hfld hps his
          (projArgs_constsIn hrec hT hidx hfld i
            (fun p hp => by
              obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
              exact VExpr.ConstsIn.liftN.2 (hps q hq))
            (fun b hb => VExpr.constsIn_bvars b hb))
          trivial
      · exact absurd h (by simp)

/-- **The stored half of `hproj`.**  Everything `projTerm` splices in is bounded by the four
stored-data hypotheses; the residual is `ps`, `ιs` and the subject. -/
theorem projTerm_constsIn (hrec : P (Lean.mkRecName T.name)) (hT : P T.name)
    (hidx : ∀ A ∈ T.indices, A.ConstsIn P) (hfld : ∀ F ∈ C.fields, F.type.ConstsIn P)
    {ps is : List VExpr} {i : Nat} {e : VExpr} (hps : ∀ p ∈ ps, p.ConstsIn P)
    (his : ∀ a ∈ is, a.ConstsIn P) (he : e.ConstsIn P) :
    (D.projTerm T C us ps is i e).ConstsIn P := by
  rw [projTerm]
  exact projCore_constsIn hrec hT hidx hfld hps his
    (projArgs_constsIn hrec hT hidx hfld i
      (fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact VExpr.ConstsIn.liftN.2 (hps q hq))
      (fun b hb => VExpr.constsIn_bvars b hb)) he

/-- …and the same at `NoConstIn`, the form `TrExprS.noConstIn`'s `hproj` is stated in. -/
theorem projTerm_noConstIn (hrec : ¬ P (Lean.mkRecName T.name)) (hT : ¬ P T.name)
    (hidx : ∀ A ∈ T.indices, A.NoConstIn P) (hfld : ∀ F ∈ C.fields, F.type.NoConstIn P)
    {ps is : List VExpr} {i : Nat} {e : VExpr} (hps : ∀ p ∈ ps, p.NoConstIn P)
    (his : ∀ a ∈ is, a.NoConstIn P) (he : e.NoConstIn P) :
    (D.projTerm T C us ps is i e).NoConstIn P :=
  VExpr.noConstIn_iff_constsIn.2 <| projTerm_constsIn hrec hT
    (fun A hA => VExpr.noConstIn_iff_constsIn.1 (hidx A hA))
    (fun F hF => VExpr.noConstIn_iff_constsIn.1 (hfld F hF))
    (fun p hp => VExpr.noConstIn_iff_constsIn.1 (hps p hp))
    (fun a ha => VExpr.noConstIn_iff_constsIn.1 (his a ha))
    (VExpr.noConstIn_iff_constsIn.1 he)

/-- **The residual is exactly `ps`, `ιs`, the subject — and the recursor's name.**  The converse
of `projTerm_constsIn` at the four hypotheses a *caller* supplies: none of them is slack, so §2 is
a split rather than a weakening.  (Same shape of lower bound as `SpineTransfer.lean` §5's
`spine_needs_blockK`; the lesson behind it is F7's `ResidualClean`, a clause true of the very
expression that refutes it.) -/
theorem projTerm_constsIn_inv {ps is : List VExpr} {i : Nat} {e : VExpr}
    (h : (D.projTerm T C us ps is i e).ConstsIn P) :
    P (Lean.mkRecName T.name) ∧ (∀ p ∈ ps, p.ConstsIn P) ∧ (∀ a ∈ is, a.ConstsIn P) ∧
      e.ConstsIn P := by
  rw [projTerm, projCore_eq] at h
  obtain ⟨hf, hargs⟩ := VExpr.constsIn_mkApp_inv h
  refine ⟨hf, fun p hp => hargs p ?_, fun a ha => hargs a ?_, hargs e ?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hp))
  · exact List.mem_append_left _ (List.mem_append_right _ ha)
  · exact List.mem_append_right _ List.mem_cons_self

end VInductDecl'

#print axioms Lean4Lean.VIndType.projMotive_constsIn
#print axioms Lean4Lean.VIndCtor.projMinor_constsIn
#print axioms Lean4Lean.VInductDecl'.projCore_constsIn
#print axioms Lean4Lean.VInductDecl'.projArgs_constsIn
#print axioms Lean4Lean.VInductDecl'.projTerm_constsIn
#print axioms Lean4Lean.VInductDecl'.projTerm_noConstIn
#print axioms Lean4Lean.VInductDecl'.projTerm_constsIn_inv


/-! ## §3 The stored data, from an environment invariant — and the invariant reduced

§60.5 measured that a nested declaration leaves **no** `_nested`-named constant behind
(restoration renames the auxiliary family away) and named `VEnv.NoNestedC` — "no declared type
mentions a prefixed name" — for this round to prove preserved.

The first thing to say about that is that it is **the wrong half**.  The primitive invariant is
about *names*:

    NoNestedN env : ∀ n, env.contains n → ¬ IsNestedName n

and `NoNestedC` follows, because `VEnv.ConstsClosedC` — an established hypothesis of this tree,
carried by `mkRestore_built_of_blockK` already — says every declared type mentions only declared
names.  So §60.5 named a *derived* invariant, and there is only one thing to assume.

The second thing is that neither is provable outright, for the reason §60.5 gives:
`inductive _nested.Foo` is accepted by both kernels (`Verify/Inductive/NestedRestore.lean` §8.2's
missing check), so `NoNestedN` fails after one step from an environment where it held.  It is an
*assumption about the environment*, discharged by the missing check, exactly as §8.2 says. -/

namespace VEnv

variable {env env' : VEnv}

/-- **No declared name carries the reserved prefix.**  Measured of the repository's own
environment: 228114 constants, 0 prefixed (§60.5, `SpineTransfer.lean` §6).

~~Not provable without `NestedRestore.lean` §8.2's missing check.~~  **That check landed in PR
#45**, so this is now provable *for the inductive branch*: acceptance by
`Environment.addInductive` implies the gate condition
(`addInductive_WF_noNestedDeclNames`, `Verify/Inductive/RestoreFaithful.lean`), and the invariant
is preserved along the pipeline by `NoNestedN.addInductR` / `.addConstList` / `.addConst`.

It is **still not provable globally**, and that is machine-checked rather than assumed: a `#eval`
in `RestoreFaithful.lean` fails the build if the answer changes, and today `inductive _nested.Zzz`
is REJECTED while `axiom _nested.zzz` and `def _nested.ddd` are **ACCEPTED** -- `checkName`
(`Environment/Basic.lean:54`) tests only already-declared and `primitives`.  So an induction on
`TrEnv'` still has nothing to supply `NoNestedN.addConst`'s name hypothesis in the `axiom`/`defn`/
`opaque`/`quot` cases.  See `docs/decision-nested-prefix-all-decls.md`. -/
def NoNestedN (env : VEnv) : Prop := ∀ {n : Name}, env.contains n → ¬ IsNestedName n

/-- The invariant is **antitone**, so it restricts to every earlier environment. -/
theorem NoNestedN.mono (h : env ≤ env') (H : env'.NoNestedN) : env.NoNestedN :=
  fun hc => H (h.contains hc)

/-- **§60.5's `NoNestedC` is derivable.**  It is not a second assumption: the name invariant
plus `ConstsClosedC` gives it. -/
theorem noNestedC_of_noNestedN (hcc : env.ConstsClosedC) (hn : env.NoNestedN) :
    env.NoNestedC := by
  intro n ci h
  exact VExpr.noConstIn_iff_constsIn.2 ((hcc h).mono fun _ hc => hn hc)

end VEnv

/-- The reserved prefix is stable under `mkRecName`, in both directions: `_nested.X.rec`
carries it and `X.rec` does not.  (So the recursor's name needs no separate assumption, but the
implication is recorded because the `_nested` prefix is tested at *every* component.) -/
theorem isNestedName_mkRecName {n : Name} : IsNestedName (Lean.mkRecName n) ↔ IsNestedName n := by
  show IsNestedName (.str n "rec") ↔ _
  rw [IsNestedName.str_iff]
  simp only [or_iff_right_iff_imp]
  intro h; exact absurd h (by simp)

#print axioms Lean4Lean.VEnv.noNestedC_of_noNestedN
#print axioms Lean4Lean.VEnv.NoNestedN.mono
#print axioms Lean4Lean.isNestedName_mkRecName

/-! ### §3.1 A structure's stored data is clean

Every hypothesis `projTerm_constsIn` asks for is read off a **declared constant** of the
ambient environment, so `ConstsClosedC` and `NoNestedN` bound all four:

* `T.name`, `Lean.mkRecName T.name` — declared, so `NoNestedN` applies directly;
* `C.fields` — the constructor's stored type is `mkPi (C.params ++ fields.map (·.type)) …`
  **on the nose** (`VIndCtor.type`; F2, the kernel walks a constructor's pi-spine without
  `whnf`), so the binder telescope is readable from the declared type;
* `T.indices` — *not* readable from `T.name`'s declared type, which is only **definitionally**
  `mkPi (params ++ indices) (sort lvl)` (F1).  They come from the **recursor's** type instead,
  where they are a syntactic binder block (`VInductDecl'.recType`).  That detour is the whole
  reason this section is not two lines, and it is the same F1 wall
  `VEnv.IsStructure.projClosed` (`Theory/Inductive/StructureClosed.lean`) hits — which takes the
  *other* door, `VIndType.WF.indices` in `env₀`, unavailable here because `ConstsIn`'s
  environment premise is not antitone the way `ClosedN`'s is. -/

variable {env : VEnv} {S : Name} {D : VInductDecl'} {T : VIndType} {C : VIndCtor}

/-- `IsStructure.decl` **is** `VInductDecl'.Declared` plus a `WF` — so
`Theory/Inductive/Lemmas.lean`'s `Declared.constants_type` / `.constants_ctor` and
`addInduct'_recs` apply directly.  (Found after re-deriving all three by hand; the hand
derivations are gone, this is the reuse.) -/
theorem VEnv.IsStructure.declared (H : env.IsStructure S D T C) : D.Declared env :=
  let ⟨_, _, _, hadd, hle⟩ := H.decl; ⟨_, _, hadd, hle⟩

/-- The block's type constant. -/
theorem VEnv.IsStructure.constants_name (H : env.IsStructure S D T C) :
    env.constants T.name = some ⟨D.uvars, T.type⟩ :=
  H.declared.constants_type (by rw [H.types]; exact List.mem_singleton_self _)

/-- The block's constructor constant, at its **stored** type. -/
theorem VEnv.IsStructure.constants_ctor (H : env.IsStructure S D T C) :
    env.constants C.name = some ⟨D.uvars, C.type D 0⟩ :=
  H.declared.constants_ctor (j := 0)
    (by simp [VInductDecl'.ctorsAll, H.types, H.ctors])

/-- The block's recursor constant. -/
theorem VEnv.IsStructure.constants_rec (H : env.IsStructure S D T C) :
    env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType 0⟩ := by
  obtain ⟨_, _, hadd, hle⟩ := H.declared
  exact hle.constants (VEnv.addInduct'_recs hadd (by simp [H.types]))

/-- **The field types are clean**, from the constructor's stored type. -/
theorem VEnv.IsStructure.fields_constsIn {P : Name → Prop} (hcc : env.ConstsClosedC)
    (hn : ∀ n, env.contains n → P n) (H : env.IsStructure S D T C) :
    ∀ F ∈ C.fields, F.type.ConstsIn P := by
  have hcl : (C.type D 0).ConstsIn P := (hcc H.constants_ctor).mono hn
  rw [VIndCtor.type] at hcl
  intro F hF
  exact VExpr.constsIn_mkPi_binders hcl _
    (List.mem_append_right _ (List.mem_map_of_mem hF))

/-- **The index telescope is clean**, from the recursor's type — see §3.1 for why not from the
block's own type. -/
theorem VEnv.IsStructure.indices_constsIn {P : Name → Prop} (hcc : env.ConstsClosedC)
    (hn : ∀ n, env.contains n → P n) (H : env.IsStructure S D T C) :
    ∀ A ∈ T.indices, A.ConstsIn P := by
  have hT0 : D.types.getD 0 default = T := by rw [H.types]; rfl
  have hcl : (D.recType 0).ConstsIn P := (hcc H.constants_rec).mono hn
  rw [VInductDecl'.recType, hT0] at hcl
  have hb := VExpr.constsIn_mkPi_binders hcl
  exact VExpr.constsIn_of_map_instL (ls := D.selfLvls)
    (VExpr.constsIn_of_liftTele (n := D.nm + D.nmin) (k := 0) fun B hB =>
      hb B (List.mem_append_right _ hB))


/-! ### §3.2 The stored half, assembled

`projTerm_constsIn` plus §3.1: the residual is `ps`, `ιs`, the subject — nothing else. -/

/-- **The stored half of `hproj`, at a declared structure.**  No typing, no `VEnv.WF`: only
`ConstsClosedC` and the name invariant. -/
theorem VEnv.IsStructure.projTerm_noConstIn (hcc : env.ConstsClosedC) (hnn : env.NoNestedN)
    (H : env.IsStructure S D T C) {us : List VLevel} {ps is : List VExpr} {i : Nat} {e : VExpr}
    (hps : ∀ p ∈ ps, p.NoConstIn IsNestedName) (his : ∀ a ∈ is, a.NoConstIn IsNestedName)
    (he : e.NoConstIn IsNestedName) :
    (D.projTerm T C us ps is i e).NoConstIn IsNestedName :=
  VExpr.noConstIn_iff_constsIn.2 <|
    VInductDecl'.projTerm_constsIn (hnn ⟨_, H.constants_rec⟩) (hnn ⟨_, H.constants_name⟩)
      (H.indices_constsIn hcc (fun _ hc => hnn hc)) (H.fields_constsIn hcc (fun _ hc => hnn hc))
      (fun p hp => VExpr.noConstIn_iff_constsIn.1 (hps p hp))
      (fun a ha => VExpr.noConstIn_iff_constsIn.1 (his a ha))
      (VExpr.noConstIn_iff_constsIn.1 he)

/-- …and the same at `TrProj`, with the `ps`/`ιs` residual as the one hypothesis.  This is
`hproj` **exactly split**: everything but the spliced parameter/index spine is proved. -/
theorem TrProj.noConstIn_of_spine {U : Nat} {Γ : List VExpr} {x y : VExpr} {i : Nat}
    (hcc : env.ConstsClosedC) (hnn : env.NoNestedN) (H : TrProj env U Γ S i x y)
    (hsp : ∀ (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
      (ps ιs : List VExpr), env.IsStructure S D T C →
      y = D.projTerm T C us ps ιs i x →
      (∀ p ∈ ps, p.NoConstIn IsNestedName) ∧ (∀ a ∈ ιs, a.NoConstIn IsNestedName))
    (hx : x.NoConstIn IsNestedName) : y.NoConstIn IsNestedName := by
  obtain @⟨_, D, T, C, us, ps, ιs, _, _, _, HS, _, _, _, _, _, _, _, _, _⟩ := H
  obtain ⟨hps, hιs⟩ := hsp D T C us ps ιs HS rfl
  exact HS.projTerm_noConstIn hcc hnn hps hιs hx

#print axioms Lean4Lean.VEnv.IsStructure.constants_name
#print axioms Lean4Lean.VEnv.IsStructure.constants_ctor
#print axioms Lean4Lean.VEnv.IsStructure.constants_rec
#print axioms Lean4Lean.VEnv.IsStructure.fields_constsIn
#print axioms Lean4Lean.VEnv.IsStructure.indices_constsIn
#print axioms Lean4Lean.VEnv.IsStructure.projTerm_noConstIn
#print axioms Lean4Lean.TrProj.noConstIn_of_spine

/-! ## §4 `hproj` in **full**: the `ps`/`ιs` half needs no strengthening of `TrProj`

§60.10 item 1 says of the other half: "the `ps`/`ιs` half is `Add.lean`'s recorded residual and
needs a canonical-spine strengthening of `TrProj`; that is a `Theory/` change and a different
stream's.  Do **not** attack it as one obligation."

**It does not need that, and it is one obligation.**  Three facts already in the tree compose:

1. `TrProj.wf` (`Verify/Typing/Lemmas.lean`:1583) — a `TrProj`'s output is well typed, given
   `VEnv.WF env`, `OnCtx Γ (env.IsType U)` and a well-typed subject.  **Measured, not read off:
   it is not sorry-free** — `#print axioms Lean4Lean.TrProj.wf` is
   `[propext, sorryAx, Classical.choice, Quot.sound]`, the hole being `IsDefEqU.weakN_iff` and
   the injectivity family (`Theory/Typing/UniqueTyping.lean`:172), another stream's.  So it is
   taken below as a *hypothesis*, and every declaration in this file stays sorry-free;
2. `VEnv.IsDefEq.constsIn` (`Theory/SetModel/Consts.lean`) with `VEnv.ctxConstsIn_of_onCtx`
   (`Theory/Typing/StrengthenAxiom.lean`) — a well-typed term mentions only **declared**
   constants;
3. the name invariant — no declared name carries the reserved prefix.

So `hproj` at `IsNestedName` is not "the one nobody has any route to" (§60.9): it is
`NoNestedN` plus well-typedness, modulo an *existing* hole that is not `hproj`'s own.  **Both halves of `hproj` rest on the same
missing check** — `NestedRestore.lean` §8.2's, the one that would reject
`inductive _nested.Foo` — and neither needs a canonical spine.

What this route does *not* do is make `hproj` unconditional.  The trade is explicit:

| route | hypotheses | who checks them |
| --- | --- | --- |
| gate (§60.3, `args_of_gate`) | `checkNoNestedAux` on the stored application, `htr`, `hproj` | the *implementation* runs the gate |
| typing (§4 here) | `VEnv.WF env`, `OnCtx Γ`, well-typedness (`TrProj.wf`, which carries `sorryAx`), `NoNestedN` | **nothing** checks `NoNestedN` |

`NoNestedN` is measured (§60.5: 228114 constants, 0 prefixed) and false one `addConst` later at a
hostile declaration — §4.1 exhibits that. -/

/-- **A well-typed term is prefix-free**, under the name invariant.  This is the whole content
of §4: no induction on the term, no gate, no `TrExprS`. -/
theorem VExpr.WF.noConstIn {env : VEnv} {U : Nat} {Γ : List VExpr} {e : VExpr}
    (henv : VEnv.WF env) (hnn : env.NoNestedN) (hΓ : OnCtx Γ (env.IsType U))
    (h : VExpr.WF env U Γ e) : e.NoConstIn IsNestedName := by
  obtain ⟨A, h⟩ := h
  exact VExpr.noConstIn_iff_constsIn.2
    ((h.constsIn henv.ordered.constsIn
      (VEnv.ctxConstsIn_of_onCtx henv.ordered hΓ)).1.mono fun _ hc => hnn hc)

/-- **`hproj`, from `TrProj.wf`'s conclusion.**  `TrProj.wf`'s *statement* is the hypothesis, not
its proof: measured, `#print axioms Lean4Lean.TrProj.wf` is
`[propext, sorryAx, Classical.choice, Quot.sound]`, and the `sorryAx` is
`IsDefEqU.weakN_iff` / the injectivity family (`Theory/Typing/UniqueTyping.lean`:172), an
existing hole owned by another stream (`Verify/Typing/Lemmas.lean`:1120 records the route).  So
this file does not *import* that hole: parameterising keeps every declaration here sorry-free,
and the same parameterisation `Verify/Typing/ProjSpineInv.lean`:214 uses for the same reason.

Note the subject premise is `VExpr.WF`, **not** `NoConstIn`: cleanliness of the subject is not
what the conclusion needs. -/
theorem TrProj.noConstIn_of_wf {env : VEnv} {U : Nat} {Γ : List VExpr} {s : Name} {i : Nat}
    {x y : VExpr} (henv : VEnv.WF env) (hnn : env.NoNestedN)
    (hΓ : OnCtx Γ (env.IsType U))
    (hwf : TrProj env U Γ s i x y → VExpr.WF env U Γ x → VExpr.WF env U Γ y)
    (H : TrProj env U Γ s i x y) (hx : VExpr.WF env U Γ x) :
    y.NoConstIn IsNestedName :=
  (hwf H hx).noConstIn henv hnn hΓ

/-- …hence `TrExprS.noConstIn`'s `hproj`, in the shape that lemma takes it, whenever every
projection subject the translation meets is well typed in its own context.  The hypothesis is
per-derivation because `hproj` quantifies over all `Γ`; at the use site
`hwf` is `TrProj.wf henv hΓ`. -/
theorem hproj_of_noNestedN {env : VEnv} {Us : List Name} (henv : VEnv.WF env)
    (hnn : env.NoNestedN)
    (hwf : ∀ Γ (s : Name) i x y, TrProj env Us.length Γ s i x y →
      OnCtx Γ (env.IsType Us.length) ∧ VExpr.WF env Us.length Γ x ∧
        VExpr.WF env Us.length Γ y) :
    ∀ Γ (s : Name) i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConstIn IsNestedName x → VExpr.NoConstIn IsNestedName y :=
  fun Γ s i x y H _ =>
    let ⟨hΓ, _, hy⟩ := hwf Γ s i x y H
    hy.noConstIn henv hnn hΓ

/-- **A third producer for `RestoreData.args`**, which needs neither the gate nor §60.10's `htr`:
if the abstract spine is well typed, it is prefix-free.  Recorded to show what the agreement
clause is *for* — it is needed to route through the checker's **gate**, not to obtain `args`. -/
theorem ElimNestedInductive.Result.args_of_wf {env : VEnv} {U : Nat} {Γ : List VExpr}
    {as : Nat → List VExpr} (henv : VEnv.WF env) (hnn : env.NoNestedN)
    (hΓ : OnCtx Γ (env.IsType U)) (hwf : ∀ j, ∀ a ∈ as j, VExpr.WF env U Γ a) :
    ∀ j, ∀ a ∈ as j, a.NoConstIn IsNestedName :=
  fun j a ha => (hwf j a ha).noConstIn henv hnn hΓ

#print axioms Lean4Lean.VExpr.WF.noConstIn
#print axioms Lean4Lean.TrProj.noConstIn_of_wf
#print axioms Lean4Lean.hproj_of_noNestedN
#print axioms Lean4Lean.ElimNestedInductive.Result.args_of_wf

/-! ### §4.1 The invariant is a real constraint

`NoNestedN` holds of the empty environment and fails after one hostile `addConst` — which is the
step both kernels accept (`NestedRestore.lean` §8.2).  So §4's route is conditional on something
an implementation would have to *check*, and the two routes above are genuinely different
hypotheses rather than two spellings of one. -/

namespace NestedWit

theorem empty_noNestedN : VEnv.NoNestedN VEnv.empty := fun h => absurd h nofun

/-- One `addConst` at a prefixed name refutes it. -/
theorem noNestedN_not_preserved :
    ∀ env : VEnv, VEnv.empty.addConst `_nested.Foo ⟨0, .sort .zero⟩ = some env →
      ¬ env.NoNestedN := by
  intro env he h
  rw [VEnv.addConst] at he
  simp only [VEnv.empty] at he
  cases he
  exact h (n := `_nested.Foo) ⟨⟨0, .sort .zero⟩, by simp⟩ (by decide)

end NestedWit

#print axioms Lean4Lean.NestedWit.noNestedN_not_preserved


/-! ## §5 `htr`, the agreement clause: measured at the witness, and the environment it lives in

§60.10 item 3 calls `htr` — `∀ j, List.Forall₂ (TrExprS env Us Δ) (r.storedArgs j) (as j)` — "the
next *constructive* piece" and "the only thing between `args_of_source` and a checker-computed
`RestoreData.args`".  Three things about it, one of them a correction.

**(a) It does not exist in the tree — but the *shape* does, and that is prior art the brief did
not name.**  Absence claim, with the predicates *defined* and the tree stated: `TrExprS` is
`Verify/Typing/Expr.lean`:153, `List.Forall₂` is core, `ElimNestedInductive.Result.storedArgs` is
`SpineTransfer.lean`:461.  Measured over **all** of `Lean4Lean/`:
`grep -rn "Forall₂" --include=*.lean Lean4Lean/` has 20-odd files, so the bare name proves
nothing; narrowing to lines carrying both — `grep -rn "Forall₂" … | grep "TrExprS"` — leaves
exactly four sites outside this file: `SpineTransfer.lean`:490/509/521 (§4.5's own producer and
its `htr` parameter) and **`Verify/Environment.lean`:204**, which is a `Forall₂` of `TrExprS` over
a *mutual definition block*'s values against the `VConstant`s the environment stores.  That last
one is the model to copy: same shape, same purpose (a list of stored `Expr`s against a list of
abstract terms), already in the tree, for definitions instead of nested spines.  A floor: a lemma
phrased through `TrExpr` (the `∃`-up-to-defeq version) or through a bespoke inductive rather than
`Forall₂` would evade both greps.

**(b) The environment it has to be stated at is the *post*-step one**, and this is the one place
the implementation's shape is decisive.  `Lean4Lean/Inductive/Add.lean`:1121 type-checks every
`aux2nested` payload — `res.aux2nested.forM fun (_, e) => do _ ← TypeChecker.checkType e` — and
its comment says why it is placed where it is: *"Checked against the final environment, so no
auxiliary declaration is in scope"*.  It must be: the stored application `J Ds` mentions the
**new** block's members (at the witness, `PFn NFn` mentions `NFn`), which the pre-step
environment does not declare, so no `TrExprS` for it exists there at all.  That is not a
circularity: `RestoreData.args` mentions no environment, so proving it through a `TrExprS` in the
post-step environment — the one `mkRestore_AddNested_of_blockK`'s `hadd` produces — is sound.
Anyone who states `htr` at the *step's* environment will find it **false**, at this witness, for
that reason.

**(c) At a concrete block it is a constant lookup, not a translation problem** — §5.2. -/

namespace NestedWit
open InductiveDeclExamples ElimNestedInductive

/-! ### §5.1 `storedArgs` reads what it should, measured

`storedArgs` is `presentedHead`'s sibling and was landed last round with no evaluation check.
At `nfnResult` — whose `aux2nested` is `[(`_nested.PFn_1, PFn NFn)]` — the two `rfl`s below pin
it: the companion member's stored spine is `[NFn]`, the block's own member has none.  (An
off-by-one against `getAppFn`, or a `getAppArgs` reversal, fails here.) -/

example : nfnResult.storedArgs 1 = [.const ``NFn []] := rfl
example : nfnResult.storedArgs 0 = [] := rfl
example : nfnResult.storedArgs 2 = [] := rfl

/-- …and the lengths agree with the abstract spine, at every index.  This is the consequence
`VNestedOcc.Occurs.args_len` forces (`(occ j).args.length = J.np`), so a mismatch here would have
refuted `htr` outright. -/
example : ∀ j, (nfnResult.storedArgs j).length = (nfnAs j).length := by
  rintro (_ | _ | j) <;> rfl

/-! ### §5.2 `htr`, discharged at the witness

One `TrExprS.const`, whose three premises are: the environment declares `NFn`, at zero universe
parameters, and the empty level list translates.  So the agreement clause is not, at a concrete
block, a translation obligation — it is the statement that the post-step environment holds the
nested spine's constants. -/

theorem nfn_htr {env : VEnv} {Us : List Lean.Name} {ci : VConstant}
    (h : env.constants ``NFn = some ci) (hu : ci.uvars = 0) :
    ∀ j, List.Forall₂ (TrExprS env Us []) (nfnResult.storedArgs j) (nfnAs j) := by
  rintro (_ | _ | j)
  · exact .nil
  · exact .cons (.const h rfl (by simp [hu])) .nil
  · exact .nil

/-- **…and it is false at the step's own environment**, which is (b) machine-checked rather than
argued: the stored spine mentions `NFn`, and `env₂ = ∅ + pfnDecl` does not declare it, so no
`TrExprS` for the payload exists there.  `by decide` supplies `` `NFn ∉ pfnDecl.allNames ``. -/
theorem nfn_htr_false_pre {env₂ : VEnv} {Us : List Lean.Name}
    (h : VEnv.empty.addInduct' pfnDecl = some env₂) :
    ¬ ∀ j, List.Forall₂ (TrExprS env₂ Us []) (nfnResult.storedArgs j) (nfnAs j) := by
  intro H
  cases H 1 with
  | cons h1 _ =>
    cases h1 with
    | const hc _ _ =>
      rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc
      exact absurd hc nofun

end NestedWit

#print axioms Lean4Lean.NestedWit.nfn_htr
#print axioms Lean4Lean.NestedWit.nfn_htr_false_pre

end Lean4Lean
