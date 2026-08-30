import Lean4Lean.Verify.Typing.ProjGenMinor

/-!
# Non-vacuity for the real minor premise

`ProjGenMinor.lean` claims two things: that the field-variable lookup goes through the
induction-hypothesis block by a **weakening**, and that `realMinor`'s body index is
`nf + nr - 1 - i` rather than the narrow `nf - 1 - i`.  Neither is testable at the blocks
this cluster already carries: `Rich`, `DepPair`, `Poly` and `MutNonRec.decl2` all have
`nr = 0`, where `liftN nr` is the identity and the two indices coincide.

`RecDep` below is built so that **four** things are simultaneously non-degenerate:

* `nr = 1` — the constructor has a recursive field, so the ih binder is really in the way;
* `nf = 3` with a **dependent** field — field 1's stored type mentions field 0, so the
  substitution the lookup performs actually moves a variable;
* `nm = 2` and the projected type sits at index `j = 1`, so no `j = 0` collapse can hide a
  wrong motive-block index;
* `q = 1`, so the minor accumulator is non-empty.

The `VInductDecl'` here is a **shape** witness: no `WF`, `Ordered` or `IotaCtx` claim is made
about it, exactly as for `MutRec.decl1r`.  What *is* checked against Lean's own elaborator is
the shape data — the `#eval` below fails the build if `RP` stops being recursive, stops being
the second member of its block, or changes arity.
-/

namespace Lean4Lean

namespace RecDep

open VExpr

inductive Q where | mk
inductive Bd : Q → Type where | mk (q : Q) : Bd q

mutual
inductive RA where | mk : RP → RA
inductive RP where | mk : (q : Q) → Bd q → RP → RP
end

/-! **[EV]** `RP` is recursive, is the **second** member of a two-type block, has one
constructor with three fields and no parameters or indices — the shape both
`VEnv.IsStructure.types` and `VEnv.IsStructure.noRec` exclude.  The `#eval` fails the build
if any of that stops holding. -/
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let some (.inductInfo v) := env.find? ``RP | throwError "RecDep.RP is not an inductive"
  unless v.isRec = true do throwError "RecDep.RP.isRec is no longer true"
  unless v.all = [``RA, ``RP] do throwError "RecDep block membership moved"
  unless v.numParams = 0 && v.numIndices = 0 do throwError "RecDep.RP arity moved"
  unless v.ctors = [``RP.mk] do throwError "RecDep.RP.ctors moved"
  let some (.ctorInfo c) := env.find? ``RP.mk | throwError "RecDep.RP.mk is not a constructor"
  unless c.numFields = 3 do throwError "RecDep.RP.mk field count moved"
  if Lean.isNonRecStructure env ``RP then
    throwError "isNonRecStructure now accepts a recursive constructor"

/-- The projected constructor: three fields, the middle one **dependent** on the first, the
last one **recursive** into block member `1`. -/
def rpmk : VIndCtor where
  name := `Lean4Lean.RecDep.RP.mk
  params := []
  fields :=
    [{ type := .const `Lean4Lean.RecDep.Q [], lvl := .succ .zero, recArg := none },
     { type := .app (.const `Lean4Lean.RecDep.Bd []) (.bvar 0), lvl := .succ .zero,
       recArg := none },
     { type := .const `Lean4Lean.RecDep.RP [], lvl := .succ .zero,
       recArg := some { binders := [], idx := 1, args := [] } }]
  args := []

/-- The same constructor with the recursion **dropped** — same fields, same types, same
arity.  Only `recArg` differs, so any check that distinguishes the two is a check on the
induction-hypothesis block and on nothing else. -/
def nrmk : VIndCtor where
  name := `Lean4Lean.RecDep.RP.mk
  params := []
  fields :=
    [{ type := .const `Lean4Lean.RecDep.Q [], lvl := .succ .zero, recArg := none },
     { type := .app (.const `Lean4Lean.RecDep.Bd []) (.bvar 0), lvl := .succ .zero,
       recArg := none },
     { type := .const `Lean4Lean.RecDep.RP [], lvl := .succ .zero, recArg := none }]
  args := []

/-- The other member of the block, at index `0`. -/
def ramk : VIndCtor where
  name := `Lean4Lean.RecDep.RA.mk
  params := []
  fields := [{ type := .const `Lean4Lean.RecDep.RP [], lvl := .succ .zero, recArg := none }]
  args := []

def treal : VIndType where
  name := `Lean4Lean.RecDep.RP
  type := .sort (.succ .zero)
  indices := []
  ctors := [rpmk]

def declRP : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := false
  types :=
    [{ name := `Lean4Lean.RecDep.RA, type := .sort (.succ .zero), indices := [],
       ctors := [ramk] },
     treal]

/-- The block's shape data, all four dimensions non-degenerate. -/
theorem shape :
    declRP.nm = 2 ∧ declRP.np = 0 ∧ declRP.types[1]? = some treal ∧
    rpmk.fields.length = 3 ∧ rpmk.recFields = [(2, { binders := [], idx := 1, args := [] })] ∧
    (declRP.ihTypes 0 rpmk).length = 1 ∧ (declRP.ihTypes 1 rpmk).length = 1 ∧
    nrmk.recFields = [] ∧ (declRP.ihTypes 0 nrmk).length = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The single induction hypothesis: motive `1` (at `.bvar 3`, under the three field binders
and with `nm - 1 - idx = 0` further along) applied to the recursive field `.bvar 0`. -/
theorem ihTypes_at_rpmk : declRP.ihTypes 0 rpmk = [VExpr.app (.bvar 3) (.bvar 0)] := rfl

/-! ## The telescope and the body index -/

/-- **The minor's binder telescope, computed.**  The three fields **and** the induction
hypothesis, the latter with motive `m1` — the *second* motive, read out of the spine.  A
`j = 0` collapse would put `m0` here, and `m0` and `m1` are distinct variables. -/
theorem minorTele_at_rpmk (m0 m1 : VExpr) :
    VExpr.instAllTele ((declRP.minorBinders 0 rpmk).map (VExpr.instL []))
        ([] ++ [m0, m1] ++ [])
      = [VExpr.const `Lean4Lean.RecDep.Q [],
         VExpr.app (.const `Lean4Lean.RecDep.Bd []) (.bvar 0),
         VExpr.const `Lean4Lean.RecDep.RP [],
         VExpr.app (m1.liftN 3) (.bvar 0)] := by
  rw [declRP.minorTele_gen (lvls := []) (us := []) (q := 0) (C := rpmk) (ps := [])
    (mots := [m0, m1]) (acc := []) rfl rfl rfl]
  rfl

/-- **The real minor, computed.**  Four binders, and the body is `.bvar 2` — field `1`. -/
theorem realMinor_at_rpmk (m0 m1 : VExpr) :
    declRP.realMinor [] ([] ++ [m0, m1] ++ []) 1 0 rpmk
      = VExpr.mkLams
          [VExpr.const `Lean4Lean.RecDep.Q [],
           VExpr.app (.const `Lean4Lean.RecDep.Bd []) (.bvar 0),
           VExpr.const `Lean4Lean.RecDep.RP [],
           VExpr.app (m1.liftN 3) (.bvar 0)]
          (.bvar 2) := by
  show VExpr.mkLams (VExpr.instAllTele ((declRP.minorBinders 0 rpmk).map (VExpr.instL []))
      ([] ++ [m0, m1] ++ [])) _ = _
  rw [minorTele_at_rpmk]
  rfl

/-- **Negative control, and not an arity error**: the `nr = 0` reading — the same telescope,
the body index `nf - 1 - i = 1` instead of `nf + nr - 1 - i = 2` — is a *different term*.
Both sides bind four variables, so no length or arity check distinguishes them.

The corresponding control on `minorTele_at_rpmk` — writing `m0` for `m1` in the induction
hypothesis, i.e. the `j = 0` collapse — is rejected too (run outside the tree):

    error: Tactic `rfl` failed: The left-hand side
      instAllTele (List.map (fun F => instL [] F.type) rpmk.fields) [] ++
        instAllTele (List.map (instL []) (declRP.ihTypes 0 rpmk)) ([] ++ [m0, m1] ++ [])
          rpmk.fields.length
    is not definitionally equal to the right-hand side
      [const `Lean4Lean.RecDep.Q [], (const `Lean4Lean.RecDep.Bd []).app (bvar 0),
        const `Lean4Lean.RecDep.RP [], (liftN 3 m0).app (bvar 0)] -/
theorem realMinor_norec_reading_false (m0 m1 : VExpr) :
    declRP.realMinor [] ([] ++ [m0, m1] ++ []) 1 0 rpmk
      ≠ VExpr.mkLams
          [VExpr.const `Lean4Lean.RecDep.Q [],
           VExpr.app (.const `Lean4Lean.RecDep.Bd []) (.bvar 0),
           VExpr.const `Lean4Lean.RecDep.RP [],
           VExpr.app (m1.liftN 3) (.bvar 0)]
          (.bvar 1) := by
  rw [realMinor_at_rpmk]
  simp [VExpr.mkLams]

/-- …and the real minor is not `projMinor` either: `projMinor` binds three variables and
returns `.bvar 1`. -/
theorem realMinor_ne_projMinor (m0 m1 : VExpr) :
    declRP.realMinor [] ([] ++ [m0, m1] ++ []) 1 0 rpmk ≠ rpmk.projMinor [] [] 1 := by
  rw [realMinor_at_rpmk]
  simp [VIndCtor.projMinor, rpmk, VExpr.mkLams]

/-- **The move test.**  `realMinor_norec` fires at `nrmk` — the same three fields with the
recursion dropped — and gives `projMinor` on the nose.  At `rpmk` that equation is **false**
(`realMinor_ne_projMinor`), and the two constructors differ in `recArg` and in nothing
else.

Negative control (run outside the tree; the same call at the **recursive** `rpmk`):

    error: Application type mismatch: The argument
      rfl
    has type
      ?m = ?m
    but is expected to have type
      rpmk.recFields = []
    in the application
      VInductDecl'.realMinor_norec rfl -/
theorem realMinor_norec_fires (m0 m1 : VExpr) :
    declRP.realMinor [] ([] ++ [m0, m1] ++ []) 1 0 nrmk = nrmk.projMinor [] [] 1 :=
  declRP.realMinor_norec (us := []) rfl rfl rfl rfl

/-- **The `hi : i < C.fields.length` bound is exactly saturated, and fails one higher.**
`realMinor_hasType_gen`'s `hbvar` step needs `nf + nr - 1 - i = (nf - 1 - i) + nr`; at
`nf = 3`, `nr = 1` that holds at `i = 2` — the largest legal index — and **fails** at `i = 3`,
where the truncating subtraction on the right bottoms out.  An arithmetic disagreement, not
an arity error. -/
theorem bvar_index_saturated :
    (3 + 1 - 1 - 2 = (3 - 1 - 2) + 1) ∧ ¬ (3 + 1 - 1 - 3 = (3 - 1 - 3) + 1) :=
  ⟨rfl, by decide⟩

/-! ## The head identification at `j = 1`, with a non-empty accumulator

A *different position* from the telescope check above, and the only place `q ≠ 0` is
exercised: minor `1`'s declared body reads motive `1` out of the spine
`ps ++ [m0, m1] ++ [a0]`.  Reading motive `0` — the `j = 0` collapse — is rejected.

Negative control (run outside the tree; `m0` is the `j = 0` reading):

    error: Application type mismatch: The argument
      rfl
    has type
      ?m = ?m
    but is expected to have type
      [m0, m1][1]? = some m0
    in the application
      VInductDecl'.minorBody_instAll_spine declRP rfl -/
theorem minorBody_head_at_rpmk (m0 m1 a0 : VExpr) :
    VExpr.instAll ((declRP.minorBody 1 1 rpmk).instL []) ([] ++ [m0, m1] ++ [a0])
        ((declRP.minorBinders 1 rpmk).map (VExpr.instL [])).length
      = (m1.liftN ((declRP.minorBinders 1 rpmk).map (VExpr.instL [])).length).mkApp
          (declRP.minorBodyArgs [] 1 rpmk ([] ++ [m0, m1] ++ [a0])) :=
  declRP.minorBody_instAll_spine rfl rfl rfl rfl (by decide)

/-! ## The field-variable lookup, fired end to end -/

theorem closedTele_ramk : VExpr.ClosedTele (ramk.fields.map (·.type)) 0 := by
  simp [ramk, VExpr.ClosedTele, VExpr.ClosedN]

theorem closedTele_rpmk : VExpr.ClosedTele (rpmk.fields.map (·.type)) 0 := by
  simp [rpmk, VExpr.ClosedTele, VExpr.ClosedN]

theorem projClosedG : declRP.ProjClosedG where
  params := trivial
  indices := by
    rintro (_ | _ | t) T' h <;> simp [declRP, treal] at h
    · subst h; trivial
    · subst h; trivial
  fields := by
    rintro (_ | _ | t) T' h <;> simp [declRP, treal] at h
    · subst h; intro C' hC; simp at hC; subst hC; exact closedTele_ramk
    · subst h; intro C' hC; simp at hC; subst hC; exact closedTele_rpmk
  recArgs := by
    rintro (_ | _ | t) T' h <;> simp [declRP, treal] at h
    · subst h; intro C' hC; simp at hC; subst hC
      intro i r hr; simp [ramk, VIndCtor.recFields] at hr
    · subst h; intro C' hC; simp at hC; subst hC
      intro i r hr
      simp [rpmk, VIndCtor.recFields] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨trivial, by simp⟩

/-- **`realMinor_field_hasType` at the dependent field, in an arbitrary environment.**
Every premise is discharged — `ProjClosedG` by `projClosedG` above — and the conclusion
computes.  Field `1`'s stored type is `Bd (.bvar 0)`, and after the lookup's substitution it
is `Bd (.bvar 2)`: the substitution **moved** the variable, which is why a block whose field
types are constants (`Rich`) tests nothing here.

Negative control (run outside the tree; the *stored* type `Bd (.bvar 0)` as the conclusion —
same context, same term, same arity):

    error: Type mismatch
      VInductDecl'.realMinor_field_hasType projClosedG rfl _ _ rfl
    has type
      env.HasType U ((instAllTele (List.map (fun F => instL [] F.type) rpmk.fields) []).reverse
          ++ Γ) (bvar (rpmk.fields.length - 1 - 1)) …
    but is expected to have type
      env.HasType U (const `Lean4Lean.RecDep.RP [] :: (const `Lean4Lean.RecDep.Bd []).app (bvar 0)
          :: const `Lean4Lean.RecDep.Q [] :: Γ)
        (bvar 1) ((const `Lean4Lean.RecDep.Bd []).app (bvar 0))

A second control, on the block index: the same call with `j := 0` — which names the *other*
member of the block — is rejected at `hTj`, not at any arity:

    error: Application type mismatch: The argument
      rfl
    has type
      ?m = ?m
    but is expected to have type
      declRP.types[0]? = some treal -/
theorem field_hasType_fires {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U
      (VExpr.const `Lean4Lean.RecDep.RP []
        :: VExpr.app (.const `Lean4Lean.RecDep.Bd []) (.bvar 0)
        :: VExpr.const `Lean4Lean.RecDep.Q [] :: Γ)
      (.bvar 1) (.app (.const `Lean4Lean.RecDep.Bd []) (.bvar 2)) :=
  declRP.realMinor_field_hasType (env := env) (U := U) (T := treal) (C := rpmk)
    (us := []) (Γ := Γ) (ps := []) (j := 1) projClosedG rfl (by simp [treal]) (i := 1)
    (by decide) rfl

/-- The substitution really is not the identity at this field. -/
theorem field_hasType_moves :
    (VExpr.app (.const `Lean4Lean.RecDep.Bd []) (.bvar 2))
      ≠ VExpr.app (.const `Lean4Lean.RecDep.Bd []) (.bvar 0) := by
  simp

/-- **A different position**: at field `0` the substitution list is empty and the variable is
`.bvar 2`.  Same lemma, same block, a different index — so the firing above is not an
accident of `i = 1`. -/
theorem field_hasType_fires_at_0 {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U
      (VExpr.const `Lean4Lean.RecDep.RP []
        :: VExpr.app (.const `Lean4Lean.RecDep.Bd []) (.bvar 0)
        :: VExpr.const `Lean4Lean.RecDep.Q [] :: Γ)
      (.bvar 2) (.const `Lean4Lean.RecDep.Q []) :=
  declRP.realMinor_field_hasType (env := env) (U := U) (T := treal) (C := rpmk)
    (us := []) (Γ := Γ) (ps := []) (j := 1) projClosedG rfl (by simp [treal]) (i := 0)
    (by decide) rfl

/-- …and at field `2`, the **recursive** one, the lookup still fires: the ih block does not
enter the field telescope at all.  All three conclusions are `HasType` of a `.bvar` in the
*same* context and are pairwise distinct, so none of them is an arity discrepancy.

Negative control on the index bound (run outside the tree; `i := 3 = nf`):

    error: Tactic `decide` proved that the proposition
      3 < rpmk.fields.length
    is false -/
theorem field_hasType_fires_at_2 {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U
      (VExpr.const `Lean4Lean.RecDep.RP []
        :: VExpr.app (.const `Lean4Lean.RecDep.Bd []) (.bvar 0)
        :: VExpr.const `Lean4Lean.RecDep.Q [] :: Γ)
      (.bvar 0) (VExpr.const `Lean4Lean.RecDep.RP []) :=
  declRP.realMinor_field_hasType (env := env) (U := U) (T := treal) (C := rpmk)
    (us := []) (Γ := Γ) (ps := []) (j := 1) projClosedG rfl (by simp [treal]) (i := 2)
    (by decide) rfl

end RecDep

end Lean4Lean
