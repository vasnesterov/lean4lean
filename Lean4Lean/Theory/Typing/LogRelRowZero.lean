import Lean4Lean.Theory.MutualDefUnsound

/-!
# Row-zero checks for the logical-relation route

Scoping file for `docs/logrel-scope.md`.  It contains the two checks that had to be run
*before* anything was built, in the discipline that has closed five routes on this project.
Nothing here is a step towards a logical relation; both results are negative or
delimiting, and they are stated so that a future reader can see exactly what was checked.

## Check 1 (§1) — the environment class is not normalising

Every open statement in `Theory/Typing/Injectivity.lean` is quantified over
`henv : VEnv.WF env`.  `VEnv.WF` admits `VDecl.unsafeDef` (`Theory/Typing/Env.lean`), whose
members are typechecked in the environment that *already carries the block's own constants*
— that is the whole content of `Theory/MutualDefUnsound.lean`.  Two members referring to
each other therefore install the definitional-equality rules `f ≡ g` and `g ≡ f`, and
weak-head δ-reduction cycles on them.

`headStep_not_wf` is that statement: **there is a `VEnv.WF` environment whose weak-head
reduction is not well founded**, at two closed terms which are both well typed at
`falseProp`.  So the reduction the logical relation is defined over does not terminate at
the generality the targets are stated at, and no normalisation argument — logical relation,
reducibility candidates, or otherwise — can establish them there.  It is not a defect in
the model of the theory: Lean's own kernel δ-unfolds `partial` definitions, so a faithful
model of the `partial`/`unsafe` layer *has* to carry a circular defining equation
(`Theory/MutualDefUnsound.lean`, "This is not an implementation divergence").

The witness is over the **empty** environment plus one declaration step, so it does not
turn on anything about the prelude.

## Check 2 (§2) — impredicativity and the logical relation's measure

A Kripke logical relation for a predicative hierarchy is defined by well-founded recursion
on the universe level, with the Π case recursing into the domain.  Impredicative `Prop`
breaks that, and the two halves below say exactly where.

* `imax_measure` — if a Π-type is **not** a proposition at a valuation, then both its
  domain's and its codomain's levels are bounded by its own.  So on the relevant fragment
  the hierarchy is predicative and the measure exists.
* `imax_zero_eval`, `imax_domain_unbounded` — if it **is** a proposition, its domain's level
  is unbounded: for every `k` there is a domain at level `k` under a Π-type at level `0`.
  So at a proposition there is no measure at all, and the logical relation's Π case must be
  **non-recursive** there.

Together: proof irrelevance is not an additional obstacle for this route, it is the
*enabling condition* — the only case where the measure fails is the case where proof
irrelevance makes recursion unnecessary.  This is the one place where the two facts that
closed every previous route (`docs/model-interface.md` §6) point the other way.

The check is stated per level valuation (`ls : List Nat`), which is forced: `VLevel` is
symbolic and `VLevel.imax u v` is `0` at some valuations and `max u v` at others whenever
`v` is a parameter.  A logical relation for this theory is therefore a family indexed by a
valuation, exactly as `Theory/SetModel/` is.
-/

namespace Lean4Lean

namespace VEnv

/-- One step of weak-head reduction: a definitional-equality rule of the environment fired
at the head, a β-redex contracted at the head, or either of those under the function
position of an application.

Defined here rather than reused from `Theory/Typing/HeadReduction.lean` on purpose: that
relation sits under `VEnv.Params`, which nothing in the tree instantiates, so a statement
about it would be vacuous.  This one has no side conditions at all, which makes
`headStep_not_wf` a statement about the environment and nothing else. -/
inductive HeadStep (env : VEnv) : VExpr → VExpr → Prop where
  | delta {df ls} : env.defeqs df → ls.length = df.uvars →
      HeadStep env (df.lhs.instL ls) (df.rhs.instL ls)
  | beta {A e a} : HeadStep env (.app (.lam A e) a) (e.inst a)
  | appFn {f f' a} : HeadStep env f f' → HeadStep env (.app f a) (.app f' a)

end VEnv

/-! ## §1  A `VEnv.WF` environment whose weak-head reduction is not well founded -/

/-- A constant of type `∀ p : Prop, p`, at any name.  Generalises
`Theory/MutualDefUnsound.lean`'s `hasType_selfRef`, which is fixed at the name `f`. -/
theorem hasType_constFalse {env : VEnv} {c : Name}
    (h : env.constants c = some ⟨0, falseProp⟩) :
    env.HasType 0 [] (.const c []) falseProp :=
  VEnv.IsDefEq.constDF (ci := ⟨0, falseProp⟩) h nofun nofun rfl .nil

/-- `f : ∀ p : Prop, p`, defined to be `g`. -/
def loopF : VDefVal := ⟨⟨⟨0, falseProp⟩, `f⟩, .const `g []⟩

/-- `g : ∀ p : Prop, p`, defined to be `f`. -/
def loopG : VDefVal := ⟨⟨⟨0, falseProp⟩, `g⟩, .const `f []⟩

/-- The empty environment with `f` added. -/
def loopEnv1 : VEnv :=
  { VEnv.empty with
    constants := fun n => if `f = n then some ⟨0, falseProp⟩ else VEnv.empty.constants n }

/-- …and then `g`. -/
def loopEnv2 : VEnv :=
  { loopEnv1 with
    constants := fun n => if `g = n then some ⟨0, falseProp⟩ else loopEnv1.constants n }

/-- …and then the two circular defining equations. -/
def loopEnv : VEnv := loopEnv2.addDefEqs [loopF, loopG]

theorem loopEnv1_eq : VEnv.empty.addConst `f ⟨0, falseProp⟩ = some loopEnv1 := rfl

theorem loopEnv2_eq : loopEnv1.addConst `g ⟨0, falseProp⟩ = some loopEnv2 := rfl

theorem loopEnv_addConsts : VEnv.empty.addConsts [loopF, loopG] = some loopEnv2 := rfl

theorem loopEnv2_f : loopEnv2.constants `f = some ⟨0, falseProp⟩ := rfl

theorem loopEnv2_g : loopEnv2.constants `g = some ⟨0, falseProp⟩ := rfl

theorem loopEnv_f : loopEnv.constants `f = some ⟨0, falseProp⟩ := loopEnv2_f
theorem loopEnv_g : loopEnv.constants `g = some ⟨0, falseProp⟩ := loopEnv2_g

/-- **The step is well formed.**  Both members typecheck in the environment that already
carries both constants — which is exactly what `VDecl.WF.unsafeDef` permits. -/
theorem loop_wf : VDecl.WF VEnv.empty (.unsafeDef [loopF, loopG]) loopEnv := by
  refine .unsafeDef (fun ci hci ↦ ?_) loopEnv_addConsts (fun ci hci ↦ ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
    obtain rfl | rfl := hci <;> exact falseProp_isType _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
    obtain rfl | rfl := hci
    · exact hasType_constFalse (env := loopEnv2) (c := `g) loopEnv2_g
    · exact hasType_constFalse (env := loopEnv2) (c := `f) loopEnv2_f

theorem loopEnv_wf : loopEnv.WF := ⟨_, .decl loop_wf .empty⟩

theorem loopEnv_defeqs_F : loopEnv.defeqs loopF.toDefEq := .inr (.inl rfl)

theorem loopEnv_defeqs_G : loopEnv.defeqs loopG.toDefEq := .inl rfl

/-- `f` δ-reduces to `g`. -/
theorem loop_step_fg : loopEnv.HeadStep (.const `f []) (.const `g []) :=
  .delta (ls := []) loopEnv_defeqs_F rfl

/-- …and `g` δ-reduces back to `f`. -/
theorem loop_step_gf : loopEnv.HeadStep (.const `g []) (.const `f []) :=
  .delta (ls := []) loopEnv_defeqs_G rfl

/-- Both terms are genuinely well typed, so this is not a junk witness. -/
theorem loop_hasType :
    loopEnv.HasType 0 [] (.const `f []) falseProp ∧
    loopEnv.HasType 0 [] (.const `g []) falseProp :=
  ⟨hasType_constFalse loopEnv_f, hasType_constFalse loopEnv_g⟩

/-- **Row zero, check 1 — machine-checked.**  Weak-head reduction is *not* well founded on
`VEnv.WF` environments: there is one, reachable from the empty environment in a single
declaration step, carrying a two-cycle between closed terms that are both well typed.

Every open statement in `Theory/Typing/Injectivity.lean` is quantified over exactly this
class of environments, so no logical relation / reducibility-candidate / normalisation
argument can establish them as stated. -/
theorem headStep_not_wf : ¬ WellFounded (fun a b => loopEnv.HeadStep b a) := by
  intro h
  suffices H : ∀ x : VExpr, Acc (fun a b => loopEnv.HeadStep b a) x →
      x ≠ .const `f [] ∧ x ≠ .const `g [] from (H _ (h.apply _)).1 rfl
  intro x hx
  induction hx with
  | intro y _ ih =>
    refine ⟨?_, ?_⟩ <;> rintro rfl
    · exact (ih _ loop_step_fg).2 rfl
    · exact (ih _ loop_step_gf).1 rfl

theorem loop_ne : (VExpr.const `f [] : VExpr) ≠ .const `g [] := by
  intro h; injection h with h1 _; exact absurd h1 (by decide)

/-- The same, packaged so that a reader need not unfold the definitions: **some**
`VEnv.WF` environment has a well-typed weak-head reduction cycle. -/
theorem exists_wf_env_headStep_cycle :
    ∃ (env : VEnv) (e₁ e₂ : VExpr), env.WF ∧ e₁ ≠ e₂ ∧
      env.HeadStep e₁ e₂ ∧ env.HeadStep e₂ e₁ ∧
      env.HasType 0 [] e₁ falseProp ∧ env.HasType 0 [] e₂ falseProp :=
  ⟨loopEnv, _, _, loopEnv_wf, loop_ne, loop_step_fg, loop_step_gf,
    loop_hasType.1, loop_hasType.2⟩

/-! ## §2  Impredicativity and the logical relation's measure -/

theorem imax_eval (u v : VLevel) (ls : List Nat) :
    (VLevel.imax u v).eval ls =
      if v.eval ls = 0 then 0 else Nat.max (u.eval ls) (v.eval ls) := rfl

/-- **Row zero, check 2a — machine-checked.**  Where a Π-type is *not* a proposition, the
hierarchy is predicative: both component levels are bounded by the Π's own level, so a
logical relation may recurse into the domain and the codomain on a decreasing measure. -/
theorem imax_measure {u v : VLevel} {ls : List Nat} (h : (VLevel.imax u v).eval ls ≠ 0) :
    u.eval ls ≤ (VLevel.imax u v).eval ls ∧ v.eval ls ≤ (VLevel.imax u v).eval ls := by
  have key : (VLevel.imax u v).eval ls = Nat.max (u.eval ls) (v.eval ls) := by
    rw [imax_eval, if_neg]
    intro hv; rw [imax_eval, if_pos hv] at h; exact h rfl
  rw [key]; exact ⟨Nat.le_max_left .., Nat.le_max_right ..⟩

/-- A Π-type into `Prop` is a proposition whatever its domain's level. -/
theorem imax_zero_eval (u : VLevel) (ls : List Nat) :
    (VLevel.imax u .zero).eval ls = 0 := by rw [imax_eval]; rfl

private def natLevel : Nat → VLevel
  | 0 => .zero
  | n + 1 => .succ (natLevel n)

private theorem natLevel_eval : ∀ (k : Nat) (ls : List Nat), (natLevel k).eval ls = k
  | 0, _ => rfl
  | k + 1, ls => congrArg (· + 1) (natLevel_eval k ls)

/-- **Row zero, check 2b — machine-checked.**  At a proposition the measure fails
completely: for every `k` there is a Π-type at level `0` whose domain sits at level `k`.
So the logical relation's Π case cannot recurse into the domain at a proposition — which
is precisely the case where proof irrelevance makes recursion unnecessary. -/
theorem imax_domain_unbounded (k : Nat) (ls : List Nat) :
    ∃ u : VLevel, u.eval ls = k ∧ (VLevel.imax u .zero).eval ls = 0 :=
  ⟨natLevel k, natLevel_eval k ls, imax_zero_eval _ _⟩

end Lean4Lean
