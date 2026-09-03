import Lean4Lean.Theory.Typing.ShapeIndepFresh

/-!
# `ShapeIndep`: are the three variable-spine rows a rename of the constant-spine rows?

**The question.**  `docs/handoff-spinevar.md` §1.3 grades `Theory/Typing/SpineVar.lean` as a
*localisation* on the strength of `spineVar_grade`:

    RigidShapeVSUniq  ↔  RigidShapeUniq ∧ SpineVarPiDisj ∧ SpineVarSortDisj ∧ SpineVarAppDisj

and flags, as the one grading question it could not close, whether **the three rows follow from
`RigidShapeUniq` alone** — because if they do, the extension is a rename.  §4.1 of that handoff
asks for a separating witness or a derivation.

**The answer, in three parts.**

1. §1 — the fixed-environment reading of the question is **degenerate**, and no witness can settle
   it.  `Injectivity.WF.rigidShapeUniq` asserts `RigidShapeUniq` at *every* `VEnv.WF` environment,
   so over `VEnv.WF` "follows from `RigidShapeUniq`" and "is a theorem" are the same predicate:
   `rowsFromBridge_iff_rows` proves the two readings equivalent outright.  A `VEnv.WF` separating
   witness would refute the corner's central node, and a non-`WF` one would have to *prove*
   `RigidShapeUniq` at a concrete environment, which nothing in this tree does at any environment.
   So the question is a **derivability** question, and §2-§3 answer it as one.

2. §2 — **two of the three rows are renames.**  `SpineVarPiDisj` and `SpineVarSortDisj` are the
   constant-spine rows `RigidConstPiDisj` and `RigidConstSortDisj` — conjuncts 2 and 5 of
   `RigidNodeCircle.rigidShapeUniqNS_iff_family` — transported along "replace the outermost context
   variable by a fresh axiom".  Nothing about variables is used: the rows are the constant rows
   read in a context.

3. §3 — **the third row is a rename of a different, already-named node.**  The same transport turns
   `SpineVarAppDisj` into constant no-confusion for **distinct** rule-free heads.  That is *not* a
   conjunct of `RigidShapeUniq` — `RigidShape.Compat`'s `app`/`app` entry is guarded by `c = c'`, and
   `rigidShapeUniq_says_nothing_distinct` machine-checks that the guard makes the entry vacuous at
   distinct heads — but it *is* in the tree, as `VEnv.ConstNoConf`
   (`Verify/Typing/Rigidity.lean:151`), with the **same `IsType` guard** this file arrived at
   independently, and it is proved there at every `VEnv.WF` environment via `PatWF` and
   `IsDefEq.church_rosser`.  `Theory` may not import `Verify`, so the identification is
   machine-checked in a scratch probe rather than here; `docs/handoff-shapeindep.md` §3 records it.

**Net grading.**  All four rows of the two variable entries are a **relabelling**: rows 1 and 2 of
the shared node's own constant conjuncts, rows 3 (and `ShapeVar.VarAppDisj`) of the corner's
declined "fourth fact", which exists.  The single residue is a **guard**, not a shape: nothing in
the tree has constant no-confusion under `¬ IsProof` rather than `IsType`, and §3.1 names the open
node that would bridge them.  See `docs/handoff-shapeindep.md`.

## The two side conditions, stated up front

* **`VEnv.FreshNames`** — every `VEnv.WF` environment has an undeclared name.  Carried as a
  hypothesis by §2-§4, and **proved** in `ShapeIndepFresh.lean` (`VEnv.freshNames`, hole-free), so
  §6 discharges it and the verdict has no freshness side condition.  `ShapeIndepStep.lean`'s
  docstring predicted this would need a "names added" bound for every `VDecl.WF` arm and that none
  existed; that was wrong — `addInduct'`, the arm that looked worst, already has one
  (`VEnv.addInduct'_constants_of_not_mem`).
* **the `¬ IsProof` guard does not transport.**  §3 therefore reduces the `IsType`-guarded form of
  row 3, not the `¬ IsProof`-guarded one.  `IsType` transports forward along the translation;
  `¬ IsProof` transports *backwards*, and turning it round is exactly `ConstVar.lean`'s
  `AxiomConservativity`, an open node.  §3.3 records this as the gap it is.

## Holes

§1's `rowsFromBridge_iff_rows` and `rows_of_bridge_all` carry `sorryAx` through
`WF.rigidShapeUniqNS`, deliberately: their whole content is that the tree already asserts the node.
§2 and §3 are **hole-free** — they are implications with the const-row hypothesis explicit, so no
hole is reachable.  Composing them with `RigidNodeCircle`'s `RigidShapeUniqNS.constPiDisj` (§4) is
what puts the rows downstream of the shared node, and that composition is hole-free too.
-/

namespace Lean4Lean
namespace VEnv

variable {U : Nat}

/-! ## §1 The fixed-environment reading is degenerate

Both readings of the handoff's question are stated here as closed propositions, and proved
equivalent.  The equivalence needs the tree's own `WF.rigidShapeUniq`, which is exactly the point:
the hypothesis `RigidShapeUniq` cannot be load-bearing in a question asked over `VEnv.WF`
environments, because the tree asserts it there. -/

/-- The three rows, at one environment. -/
def SpineVarRows (env : VEnv) (U : Nat) : Prop :=
  SpineVarPiDisj env U ∧ SpineVarSortDisj env U ∧ SpineVarAppDisj env U

/-- "The rows follow from the bridge" — the handoff's question, read at every `VEnv.WF`
environment. -/
def RowsFromBridge : Prop :=
  ∀ (env : VEnv) (U : Nat), env.WF → env.RigidShapeUniq U → SpineVarRows env U

/-- "The rows are theorems" — the same statement with the bridge hypothesis deleted. -/
def RowsHold : Prop := ∀ (env : VEnv) (U : Nat), env.WF → SpineVarRows env U

/-- **The two readings are the same question.**  `←` is free (delete a hypothesis); `→` feeds the
hypothesis from `WF.rigidShapeUniq`, which `Injectivity.lean` asserts at every `VEnv.WF`
environment.

So no witness can separate the rows from the bridge, and `docs/handoff-spinevar.md` §4.1's
"a `VEnv.WF` environment satisfying `RigidShapeUniq` and violating one of the three rows would
settle it" describes an object whose existence would refute `WF.rigidShapeUniqNS`.  Carries
`sorryAx` through that theorem *by design*: the content is the tree's own assertion. -/
theorem rowsFromBridge_iff_rows : RowsFromBridge ↔ RowsHold :=
  ⟨fun H env U henv => H env U henv (WF.rigidShapeUniq henv),
   fun H env U henv _ => H env U henv⟩

/-! ## §2 The two unguarded rows are the constant rows in a context

The transport is `ShapeIndepStep.axiomize_step` iterated: replace the outermost context variable by
a fresh axiom, shortening the context by one, until either the spine head *is* the fresh constant
(and the constant row fires) or the context is empty (and `SpineVar.lean` §7.1 fires).

The two rows are proved by the same induction with `.forallE A B` / `.sort u` on the right; the
right-hand side is substituted too, and both shapes are stable under substitution, which is the
only thing the two proofs need to know about it. -/

/-- **Row 1 is `RigidConstPiDisj`.**  A variable-headed spine is not convertible to a Π, given that
no *constant*-headed rule-free spine is, at every well-formed environment.

Note what the hypothesis quantifies over: environments, not contexts.  The transport leaves the
environment one axiom bigger at each step, so the constant row is needed at the extensions —
which is what `WF.rigidShapeUniqNS`, a statement about every `VEnv.WF` environment, supplies. -/
theorem spineVarPiDisj_of_constPiDisj (hfresh : FreshNames)
    (Hc : ∀ (env : VEnv), env.WF → env.RigidConstPiDisj U) :
    ∀ (env : VEnv), env.WF → SpineVarPiDisj env U := by
  suffices H : ∀ (n : Nat) (env : VEnv), env.WF → ∀ (Γ : List VExpr), Γ.length = n →
      OnCtx Γ (env.IsType U) → ∀ (e A B : VExpr) (i : Nat), e.spineHead = .bvar i →
      ¬ env.IsDefEqU U Γ e (.forallE A B) by
    intro env henv Γ e A B i hΓ hsh hc
    exact H Γ.length env henv Γ rfl hΓ e A B i hsh hc
  intro n
  induction n with
  | zero =>
    intro env henv Γ hn hΓ e A B i hsh hc
    cases List.length_eq_zero_iff.1 hn
    exact spineVarPiDisj_nil henv.ordered hsh hc
  | succ n ih =>
    intro env henv Γ hn hΓ e A B i hsh hc
    obtain rfl | ⟨Γ₀, T, rfl⟩ := List.eq_nil_or_concat Γ
    · simp at hn
    simp only [List.concat_eq_append] at hn hΓ hc
    have hn' : Γ₀.length = n := by simpa using hn
    obtain ⟨c, hcfr⟩ := hfresh env henv
    obtain ⟨env', Γ', hle, henv', hlen, hΓ', hrf, hrf', hct, W⟩ := axiomize_step henv hΓ hcfr
    obtain ⟨T', hd⟩ := hc
    have hi : i < Γ₀.length + 1 := by
      have h := (hd.closedN henv.ordered (CtxWF.closed henv.ordered hΓ)).spineHead
      rw [hsh] at h; simpa [VExpr.ClosedN] using h
    have hc' := IsDefEqU.instN henv'.ordered W (IsDefEqU.mono hle ⟨T', hd⟩) hct
    rcases Nat.lt_or_ge i Γ₀.length with hlt | hge
    · exact ih env' henv' Γ' (hlen.trans hn') hΓ' _ _ _ i
        (VExpr.spineHead_inst_lt hsh hlt) hc'
    · have hieq : i = Γ₀.length := Nat.le_antisymm (Nat.lt_succ_iff.1 hi) hge
      rw [hieq] at hsh
      have hsh' : (e.inst (.const c (VLevel.params U)) Γ₀.length).spineHead
          = .const c (VLevel.params U) := by rw [VExpr.spineHead_inst_eq hsh]; rfl
      have key := VExpr.eq_spineHead_mkApp (e.inst (.const c (VLevel.params U)) Γ₀.length)
      rw [hsh'] at key
      exact Hc env' henv' hΓ' hrf (key ▸ hc')

/-- **Row 2 is `RigidConstSortDisj`**, by the same induction. -/
theorem spineVarSortDisj_of_constSortDisj (hfresh : FreshNames)
    (Hc : ∀ (env : VEnv), env.WF → env.RigidConstSortDisj U) :
    ∀ (env : VEnv), env.WF → SpineVarSortDisj env U := by
  suffices H : ∀ (n : Nat) (env : VEnv), env.WF → ∀ (Γ : List VExpr), Γ.length = n →
      OnCtx Γ (env.IsType U) → ∀ (e : VExpr) (u : VLevel) (i : Nat), e.spineHead = .bvar i →
      ¬ env.IsDefEqU U Γ e (.sort u) by
    intro env henv Γ e u i hΓ hsh hc
    exact H Γ.length env henv Γ rfl hΓ e u i hsh hc
  intro n
  induction n with
  | zero =>
    intro env henv Γ hn hΓ e u i hsh hc
    cases List.length_eq_zero_iff.1 hn
    exact spineVarSortDisj_nil henv.ordered hsh hc
  | succ n ih =>
    intro env henv Γ hn hΓ e u i hsh hc
    obtain rfl | ⟨Γ₀, T, rfl⟩ := List.eq_nil_or_concat Γ
    · simp at hn
    simp only [List.concat_eq_append] at hn hΓ hc
    have hn' : Γ₀.length = n := by simpa using hn
    obtain ⟨c, hcfr⟩ := hfresh env henv
    obtain ⟨env', Γ', hle, henv', hlen, hΓ', hrf, hrf', hct, W⟩ := axiomize_step henv hΓ hcfr
    obtain ⟨T', hd⟩ := hc
    have hi : i < Γ₀.length + 1 := by
      have h := (hd.closedN henv.ordered (CtxWF.closed henv.ordered hΓ)).spineHead
      rw [hsh] at h; simpa [VExpr.ClosedN] using h
    have hc' := IsDefEqU.instN henv'.ordered W (IsDefEqU.mono hle ⟨T', hd⟩) hct
    rcases Nat.lt_or_ge i Γ₀.length with hlt | hge
    · exact ih env' henv' Γ' (hlen.trans hn') hΓ' _ _ i
        (VExpr.spineHead_inst_lt hsh hlt) hc'
    · have hieq : i = Γ₀.length := Nat.le_antisymm (Nat.lt_succ_iff.1 hi) hge
      rw [hieq] at hsh
      have hsh' : (e.inst (.const c (VLevel.params U)) Γ₀.length).spineHead
          = .const c (VLevel.params U) := by rw [VExpr.spineHead_inst_eq hsh]; rfl
      have key := VExpr.eq_spineHead_mkApp (e.inst (.const c (VLevel.params U)) Γ₀.length)
      rw [hsh'] at key
      exact Hc env' henv' hΓ' hrf (key ▸ hc')

/-! ## §3 The third row is **not** a constant row of the shared node

The same transport applies, and it lands on a statement `RigidShapeUniq` does not contain: two
rule-free constant spines with **distinct** heads are not convertible.  `RigidShape.Compat`'s
`app`/`app` entry is guarded by `c = c'` — `Injectivity.lean`'s own docstring calls that "the
no-confusion fact the module docstring says no consumer has asked for" — and
`rigidShapeUniq_says_nothing_distinct` below is that guard's consequence, machine-checked.

So row 3 is the one place where `SpineVar.lean` buys something, and what it buys is not a fact
about variables: it is the corner's declined no-confusion row.

### §3.1 Two guards that do not transport, and the form that does

`SpineVarAppDisj`'s `¬ IsProof` guard is on the **left** endpoint, the variable spine.  The
translation pushes judgements *up* (to a bigger environment), so it transports `IsProof` forwards
and `¬ IsProof` backwards — the wrong way.  Turning it round is `ConstVar.lean`'s
`AxiomConservativity`, which `axiomConservativityWF_iff_target` shows *is* the strengthening
target: an open node.  So the row reduced here carries `IsType` instead, which transports forwards
(`IsType.instN`), and is strictly stronger than `¬ IsProof` at a `VEnv.WF` environment
(`IsType.not_isProof`).  The reduction is therefore of a **weaker row**, and this is the honest
statement of the gap rather than a claim about the row as `SpineVar.lean` states it. -/

/-- Row 3 with the `¬ IsProof` guard replaced by `IsType` (§3.1), and with the constant head
required to be declared — which any conversion at a constant spine forces, but which the
translation needs stated because it must know the fresh axiom is a *different* constant. -/
def SpineVarAppDisjT (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e : VExpr} {i : Nat} {c : Lean.Name} {ls : List VLevel} {as : List VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c → env.contains c → env.IsType U Γ e →
    e.spineHead = .bvar i → ¬ env.IsDefEqU U Γ e ((VExpr.const c ls).mkApp as)

/-- **Constant no-confusion for distinct rule-free heads** — what row 3 transports to, and what
`RigidShapeUniq` declines to claim.  Same guard shape as `SpineVarAppDisjT`. -/
def RigidConstNoConf (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c → env.RuleFreeHead c' → c ≠ c' →
    env.IsType U Γ ((VExpr.const c ls).mkApp as) →
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as')

/-- The `Γ = []` base case, as for the other two rows: a closed term's spine head is not a
variable. -/
theorem spineVarAppDisj_nil {env : VEnv} (hord : Ordered env) {e : VExpr} {i : Nat} {f : VExpr}
    (hsh : e.spineHead = .bvar i) : ¬ env.IsDefEqU U [] e f := by
  rintro ⟨T, h⟩
  exact VExpr.spineHead_ne_bvar_of_closed (h.closedN hord trivial) hsh

/-- **Row 3 is constant no-confusion.**  Same induction as §2; the constant side is substituted
too, and `VExpr.mkApp_inst` says a constant spine stays a constant spine with the same head. -/
theorem spineVarAppDisjT_of_constNoConf (hfresh : FreshNames)
    (Hc : ∀ (env : VEnv), env.WF → env.RigidConstNoConf U) :
    ∀ (env : VEnv), env.WF → SpineVarAppDisjT env U := by
  suffices H : ∀ (n : Nat) (env : VEnv), env.WF → ∀ (Γ : List VExpr), Γ.length = n →
      OnCtx Γ (env.IsType U) → ∀ (e : VExpr) (i : Nat) (c : Lean.Name) (ls : List VLevel)
        (as : List VExpr), env.RuleFreeHead c → env.contains c → env.IsType U Γ e →
      e.spineHead = .bvar i → ¬ env.IsDefEqU U Γ e ((VExpr.const c ls).mkApp as) by
    intro env henv Γ e i c ls as hΓ hrf hct hIT hsh hc
    exact H Γ.length env henv Γ rfl hΓ e i c ls as hrf hct hIT hsh hc
  intro n
  induction n with
  | zero =>
    intro env henv Γ hn hΓ e i c ls as _ _ _ hsh hc
    cases List.length_eq_zero_iff.1 hn
    exact spineVarAppDisj_nil henv.ordered hsh hc
  | succ n ih =>
    intro env henv Γ hn hΓ e i c ls as hrfc hcont hIT hsh hc
    obtain rfl | ⟨Γ₀, T, rfl⟩ := List.eq_nil_or_concat Γ
    · simp at hn
    simp only [List.concat_eq_append] at hn hΓ hc hIT
    have hn' : Γ₀.length = n := by simpa using hn
    obtain ⟨cn, hcfr⟩ := hfresh env henv
    obtain ⟨env', Γ', hle, henv', hlen, hΓ', hrf, hrf', hct, W⟩ := axiomize_step henv hΓ hcfr
    obtain ⟨T', hd⟩ := hc
    have hi : i < Γ₀.length + 1 := by
      have h := (hd.closedN henv.ordered (CtxWF.closed henv.ordered hΓ)).spineHead
      rw [hsh] at h; simpa [VExpr.ClosedN] using h
    have hc' := IsDefEqU.instN henv'.ordered W (IsDefEqU.mono hle ⟨T', hd⟩) hct
    rw [VExpr.mkApp_inst] at hc'
    have hIT' : env'.IsType U Γ' (e.inst (.const cn (VLevel.params U)) Γ₀.length) :=
      (hIT.mono hle).instN henv'.ordered W hct
    rcases Nat.lt_or_ge i Γ₀.length with hlt | hge
    · exact ih env' henv' Γ' (hlen.trans hn') hΓ' _ i c ls _ (hrf' _ hrfc)
        (VEnv.LE.contains hle hcont) hIT' (VExpr.spineHead_inst_lt hsh hlt) hc'
    · have hieq : i = Γ₀.length := Nat.le_antisymm (Nat.lt_succ_iff.1 hi) hge
      rw [hieq] at hsh
      have hsh' : (e.inst (.const cn (VLevel.params U)) Γ₀.length).spineHead
          = .const cn (VLevel.params U) := by rw [VExpr.spineHead_inst_eq hsh]; rfl
      have hne : cn ≠ c := fun h => by
        obtain ⟨ci, hci⟩ := hcont; rw [h] at hcfr; exact absurd hci (hcfr ▸ nofun)
      have key := VExpr.eq_spineHead_mkApp (e.inst (.const cn (VLevel.params U)) Γ₀.length)
      rw [hsh'] at key
      exact Hc env' henv' hΓ' hrf (hrf' _ hrfc) hne (key ▸ hIT') (key ▸ hc')

/-- **`RigidShapeUniq` says nothing about two rule-free spines with distinct heads.**  Its
`app`/`app` entry is the implication `c = c' → …`, so at `c ≠ c'` it is satisfied by *every* pair
of spines: the entry is vacuous exactly where row 3 needs it.

This is the machine-checked form of the claim that §3's reduction does not land inside the shared
node — not an unprovability claim, a claim about what the node's statement contains. -/
theorem rigidShapeUniq_says_nothing_distinct {env : VEnv} {Γ : List VExpr}
    {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr} (h : c ≠ c') :
    RigidShape.Compat env U Γ (.app c ls as) (.app c' ls' as') := fun hcc => absurd hcc h

/-- …and the extended vocabulary declines the same fact in the same place: the `varApp`/`varApp`
diagonal is `True` (`SpineVar.lean` §7.3 refutes `i = j`), which is the *image* of the `c = c'`
guard under §3's translation.  The two vocabularies decline no-confusion at corresponding
entries — a coherence check on the translation, stated so it is on the record. -/
theorem rigidShapeVSUniq_says_nothing_distinct {env : VEnv} {Γ : List VExpr}
    {i j : Nat} {as as' : List VExpr} :
    RigidShapeVS.Compat env U Γ (.varApp i as) (.varApp j as') := trivial

/-! ## §4 The two rows are downstream of the shared node

`RigidNodeCircle.RigidShapeUniqNS.constPiDisj` and `.constSortDisj` already read the two constant
rows off the (narrowed) bridge, at the price of `SortUniq` and `ProofTransport`.  Composing them
with §2 puts rows 1 and 2 downstream of the shared node.

**A correction to this file's first draft.**  It claimed the `SortUniq`/`ProofTransport` tax was
avoidable off the *full* `RigidShapeUniq`, because the middle term can be taken to be the constant
spine itself and `not_isProof_of_defeqU_forallE` then discharges the `¬ IsProof` guard from
`VEnv.WF` alone.  That route compiles, but it is **not hole-free**:
`not_isProof_of_defeqU_forallE` goes through `WF.sortUniq'` and `IsProof.defeqU`, both of which
carry `sorryAx`, while `RigidNodeCircle`'s `not_isProof_of_forallE'` is hole-free *because* it takes
`SortUniq` and `ProofTransport` as hypotheses.  Measured, not assumed; the tax is what buys the
hole-freeness, and the draft docstring had it backwards. -/

/-- The bridge implies its own narrowing — one deleted premise. -/
theorem RigidShapeUniq.ns {env : VEnv} (h : env.RigidShapeUniq U) : env.RigidShapeUniqNS U :=
  fun hΓ hnp hr₁ hr₂ _ h₁ h₂ => h hΓ hnp hr₁ hr₂ h₁ h₂

/-- **Rows 1 and 2 are a rename.**  Given `FreshNames` and the corner's shared node at every
well-formed environment (with `RigidNodeCircle`'s two side nodes, which that file already charges
for the constant rows), both unguarded variable-spine rows are theorems.

**Hole-free** — every node is a hypothesis here, so nothing in the cone can reach the tree's
`sorry`.  `rows12_hold` below is the unconditional corollary, and it is *not* hole-free; the two
must not be confused. -/
theorem rows12_of_rigidShapeUniqNS_all (hfresh : FreshNames)
    (hsu : ∀ env : VEnv, env.WF → env.SortUniq U)
    (htr : ∀ env : VEnv, env.WF → env.ProofTransport U)
    (H : ∀ env : VEnv, env.WF → env.RigidShapeUniqNS U) :
    ∀ (env : VEnv), env.WF → SpineVarPiDisj env U ∧ SpineVarSortDisj env U := fun env henv =>
  ⟨spineVarPiDisj_of_constPiDisj hfresh
      (fun e he => RigidShapeUniqNS.constPiDisj (hsu e he) he.ordered (htr e he) (H e he)) env henv,
   spineVarSortDisj_of_constSortDisj hfresh
      (fun e he => RigidShapeUniqNS.constSortDisj (hsu e he) he.ordered (htr e he) (H e he)) env henv⟩

/-- **The price after this round: one row, not three.**  `spineVar_grade` charges `RigidShapeUniq`
plus three rows for the extended bridge.  Two of the three come free from the node itself, so the
extension's actual cost over the shared node is `SpineVarAppDisj` alone — and §3 says what *that*
is.  Hole-free, and this is the file's headline. -/
theorem rigidShapeVSUniq_of_bridge_all_and_row3 (hfresh : FreshNames)
    (hsu : ∀ env : VEnv, env.WF → env.SortUniq U)
    (htr : ∀ env : VEnv, env.WF → env.ProofTransport U)
    (H : ∀ env : VEnv, env.WF → env.RigidShapeUniqNS U) {env : VEnv} (henv : env.WF)
    (hsu0 : env.SortUniq U) (h3 : SpineVarAppDisj env U) : env.RigidShapeVSUniq U :=
  let ⟨h1, h2⟩ := rows12_of_rigidShapeUniqNS_all hfresh hsu htr H env henv
  rigidShapeVSUniq_of_family (htr env henv)
    (rigidShapeUniq_of_sortUniq henv hsu0 (H env henv)) h1 h2 h3

/-- **…and rows 1 and 2 unconditionally, from the tree's own assertions.**  Carries `sorryAx`
through `WF.rigidShapeUniqNS`, `WF.sortUniq'` and `WF.proofTransport`; kept separate from the
hypothesised form above so the two strengths are not confused (`docs/vacuity-ledger.md` §0's second
instrument).  Modulo `FreshNames`, this is the answer to the handoff's question for rows 1 and 2:
**yes, they follow.** -/
theorem rows12_hold (hfresh : FreshNames) :
    ∀ (env : VEnv), env.WF → SpineVarPiDisj env U ∧ SpineVarSortDisj env U :=
  rows12_of_rigidShapeUniqNS_all hfresh (fun _ he => WF.sortUniq' he)
    (fun _ he => WF.proofTransport he) (fun _ he => WF.rigidShapeUniqNS he)

/-! ## §5 Anti-vacuity, in the order `docs/vacuity-ledger.md` §0 asks for them

The failure mode this corner has already produced twice is a reduction that compiles, prints a
clean axiom line, and never fires.  §2 and §3 are implications, so the risks are: the transport's
load-bearing branch is unreachable; the hypothesis is never appealed to; the reduced row's guard set
is empty.  All three are checked at witnesses below.

### §5.1 Does the entry constrain a `trans` midpoint?  **No** — and it cannot

The mandatory question (ledger rows 94/94a, 100-103; eleven collapses).  Nothing in this file
mentions a midpoint: §2 and §3 do not open a conversion derivation at all.  The `IsDefEqStrong`
induction that `SpineVar.lean` §4 runs is *replaced* here by a substitution, and substitution acts
on the two **endpoints** of `IsDefEqU` (`IsDefEq.instN` is proved by induction over the whole
derivation, midpoints included, and imposes no condition on any of them).  The recursion in §2 is on
the **length of the context**, not on the derivation.  So this file is not the twelfth collapse, and
the reason is structural rather than a read-off. -/

/-- **The transport's load-bearing branch fires**, at a concrete environment.  `VEnv.empty` with a
one-entry context `[Prop]`: every name is fresh there (`rfl`), so `axiomize_step` runs, and the
variable `.bvar 0` — index `0 = Γ₀.length` — becomes the fresh **constant**, which is the branch
where the constant row, and nothing else, closes the goal.

Seven conjuncts: the step's output environment is `WF` and above `VEnv.empty`, the context has
shrunk to `[]`, the axiom is typed, it heads no rule, and the substituted variable's spine head is
the new constant. -/
theorem axiomize_step_fires (c : Lean.Name) :
    ∃ (env' : VEnv) (Γ' : List VExpr),
      (∅ : VEnv) ≤ env' ∧ env'.WF ∧ Γ' = [] ∧
      env'.HasType 0 [] (.const c (VLevel.params 0)) (.sort .zero) ∧
      env'.RuleFreeHead c ∧
      ((VExpr.bvar 0).inst (.const c (VLevel.params 0)) 0).spineHead
        = .const c (VLevel.params 0) := by
  have hΓ : OnCtx ([] ++ [VExpr.sort .zero]) ((∅ : VEnv).IsType 0) := ⟨trivial, _, .sort trivial⟩
  obtain ⟨env', Γ', hle, henv', hlen, hΓ', hrf, _, hct, _⟩ :=
    axiomize_step (U := 0) ⟨[], .empty⟩ hΓ (c := c) rfl
  exact ⟨env', Γ', hle, henv', List.length_eq_zero_iff.1 hlen, hct, hrf,
    by rw [VExpr.spineHead_inst_eq (rfl : (VExpr.bvar 0).spineHead = .bvar 0)]; rfl⟩

/-- **…and so does the recursive branch.**  At index `0 < 1` the substituted term keeps a *variable*
spine head, which is the branch that recurses on the shorter context.  Both branches of §2's
`rcases` are therefore reachable, so neither the constant row nor the induction hypothesis is
decoration. -/
theorem axiomize_step_recurses (c : Lean.Name) :
    ((VExpr.bvar 0).inst (.const c (VLevel.params 0)) 1).spineHead = .bvar 0 :=
  VExpr.spineHead_inst_lt (rfl : (VExpr.bvar 0).spineHead = .bvar 0) Nat.one_pos

/-! ### §5.2 The reduced row's guard set is inhabited

`SpineVarAppDisjT` carries five premises, and if they cannot hold together the §3 reduction is a
reduction of nothing.  They can, and at a **non-empty** spine: over `svEnv` (`ShapeVar.lean` §9 —
`VEnv.empty` plus the single propositional axiom `svC`), in `SpineVar.lean` §7.2's three-entry
context, the type `.app (.bvar 2) (.bvar 1)` is a variable-headed spine that **is a type**, and
`svC` is a declared rule-free constant.

`svEnv` is **inconsistent** — `SpineVarVacuity.svEnv_every_prop_inhabited` proves every proposition
is inhabited there — and that is disclosed separately from this claim: what is used here is only
that `svEnv` is `VEnv.WF` and declares one constant, and the statement below is a *conjunction of
premises*, not a refutation, so inconsistency neither helps nor hurts it. -/

/-- `VEnv.empty ≤ svEnv`, so `SpineVar.lean` §7.2's witnesses transport to `svEnv`. -/
theorem empty_le_svEnv : (∅ : VEnv) ≤ svEnv := addConst_le addConst_svEnv

/-- **All five premises of `SpineVarAppDisjT` hold at once**, at a spine of length one. -/
theorem spineVarAppDisjT_guards_inhabited :
    svEnv.WF ∧ OnCtx spCtx (svEnv.IsType 0) ∧ svEnv.RuleFreeHead svC ∧ svEnv.contains svC ∧
      svEnv.IsType 0 spCtx (.app (.bvar 2) (.bvar 1)) ∧
      (VExpr.app (.bvar 2) (.bvar 1)).spineHead = .bvar 2 :=
  ⟨wf_svEnv, spCtx_onCtx.mono fun h => h.mono empty_le_svEnv, ruleFreeHead_svEnv svC,
   ⟨_, svEnv_constants⟩,
   spineVar_row_reachable.2.2.1.mono empty_le_svEnv, rfl⟩

/-! ### §5.3 Refutation attempts, per new definition

Two definitions are new here, and both were attacked before being used.

* **`RigidConstNoConf`** — the fact §3 lands on.  The two mechanisms that killed draft rows in this
  corner are δ and proof irrelevance.  δ is blocked by `RuleFreeHead` on **both** heads, which the
  statement asks for on both.  Proof irrelevance needs the left endpoint to be a proof, and the
  `IsType` guard excludes that (`IsType.not_isProof`, which is in the tree but tainted — so this is
  a blocked-mechanism claim resting on a tainted lemma, not a theorem here).  **Not refuted.**  Note
  the *unguarded* form would be refutable by the same shape as `SpineVar.lean` §7.4, and that the
  `IsType` guard is exactly the price §3.1 charges.
* **`SpineVarAppDisjT`** — the reduced row.  It is `SpineVarAppDisj` with a *stronger* guard, so it
  is implied by the row `SpineVar.lean` states and cannot be stronger than it; §5.2 shows the guard
  still admits a non-empty variable spine, so it is not the empty statement.  What is **not** proved
  here is the converse — that is the `¬ IsProof`/`IsType` gap, and §3.1 names the open node
  (`AxiomConservativity`) that would close it.

### §5.4 What would refute this file

A `VEnv.WF` environment with a variable-headed spine convertible to a Π would, by §2 plus
`FreshNames`, refute `RigidConstPiDisj` at some one-axiom extension of it — i.e. refute the
*constant* row, which is a conjunct of the corner's shared node
(`RigidNodeCircle.rigidShapeUniqNS_iff_family`).  So a refutation of row 1 is now a refutation of
the shared node, not of a variable-specific entry.  That is the substance of the rename verdict, and
it is the contrapositive of §4, not a further claim. -/

/-! ## §6 …and the freshness side condition is discharged

`ShapeIndepFresh.freshNames` proves `FreshNames` outright, so the hypothesised results above
become unconditional.  What remains in their cones is only what was already open in this corner:
`WF.rigidShapeUniqNS`, `WF.sortUniq'`, `WF.proofTransport`. -/

/-- **Rows 1 and 2 are theorems**, at every well-formed environment, with no side condition beyond
the corner's existing nodes.  This is the answer to `docs/handoff-spinevar.md` §4.1 for the two
unguarded rows: **they do follow**, so for them `SpineVar.lean`'s entry is a rename. -/
theorem rows12_theorem : ∀ (env : VEnv), env.WF → SpineVarPiDisj env U ∧ SpineVarSortDisj env U :=
  rows12_hold freshNames

/-- **The practical payoff.**  `SpineVar.lean` §5's row deletion no longer needs a hypothesis:
`PiDescend`'s residual with the whole variable slice removed is an equivalence outright, not
modulo `SpineVarPiDisj`.  Compare `piDescend_iff_neutralNVS_sortConv`, which takes that row. -/
theorem piDescend_iff_neutralNVS_sortConv' {env : VEnv} (henv : env.WF) :
    PiDescend env U ↔ PiCodLiftNeutralNVS env U ∧ SortConvStrengthening env U :=
  piDescend_iff_neutralNVS_sortConv henv (rows12_theorem env henv).1

/-- **Row 3's reduction, unconditional in freshness**: the extended bridge's whole cost over the
shared node is constant no-confusion for distinct rule-free heads, in its `IsType`-guarded form. -/
theorem spineVarAppDisjT_theorem (Hc : ∀ (env : VEnv), env.WF → env.RigidConstNoConf U) :
    ∀ (env : VEnv), env.WF → SpineVarAppDisjT env U :=
  spineVarAppDisjT_of_constNoConf freshNames Hc

/-- **`ShapeVar.lean`'s bare-variable rows are renamed too.**  Its `VarPiDisj` and `VarSortDisj`
are the empty-spine instances of rows 1 and 2 (`(VExpr.bvar i).spineHead = .bvar i` by `rfl`), so
the *previous* round's entry falls to the same argument.  Its `VarAppDisj` is row 3's bare case and
inherits row 3's guard gap (§3.1). -/
theorem varRows_theorem : ∀ (env : VEnv), env.WF → VarPiDisj env U ∧ VarSortDisj env U :=
  fun env henv =>
    let ⟨h1, h2⟩ := rows12_theorem env henv
    ⟨fun hΓ hc => h1 hΓ rfl hc, fun hΓ hc => h2 hΓ rfl hc⟩

/-- …and so `ShapeVar.lean` §6's row deletion is unconditional as well. -/
theorem piDescend_iff_neutralNV_sortConv' {env : VEnv} (henv : env.WF) :
    PiDescend env U ↔ PiCodLiftNeutralNV env U ∧ SortConvStrengthening env U :=
  piDescend_iff_neutralNV_sortConv henv (varRows_theorem env henv).1

end VEnv

section Audit
#print axioms Lean4Lean.VEnv.rowsFromBridge_iff_rows
#print axioms Lean4Lean.VEnv.spineVarPiDisj_of_constPiDisj
#print axioms Lean4Lean.VEnv.spineVarSortDisj_of_constSortDisj
#print axioms Lean4Lean.VEnv.spineVarAppDisj_nil
#print axioms Lean4Lean.VEnv.spineVarAppDisjT_of_constNoConf
#print axioms Lean4Lean.VEnv.rigidShapeUniq_says_nothing_distinct
#print axioms Lean4Lean.VEnv.rigidShapeVSUniq_says_nothing_distinct
#print axioms Lean4Lean.VEnv.RigidShapeUniq.ns
#print axioms Lean4Lean.VEnv.rows12_of_rigidShapeUniqNS_all
#print axioms Lean4Lean.VEnv.rigidShapeVSUniq_of_bridge_all_and_row3
#print axioms Lean4Lean.VEnv.rows12_hold
-- §5 anti-vacuity
#print axioms Lean4Lean.VEnv.axiomize_step_fires
#print axioms Lean4Lean.VEnv.axiomize_step_recurses
#print axioms Lean4Lean.VEnv.empty_le_svEnv
#print axioms Lean4Lean.VEnv.spineVarAppDisjT_guards_inhabited
-- §6 with freshness discharged
#print axioms Lean4Lean.VEnv.rows12_theorem
#print axioms Lean4Lean.VEnv.piDescend_iff_neutralNVS_sortConv'
#print axioms Lean4Lean.VEnv.spineVarAppDisjT_theorem
#print axioms Lean4Lean.VEnv.varRows_theorem
#print axioms Lean4Lean.VEnv.piDescend_iff_neutralNV_sortConv'
-- the theorems this file re-grades, for the side-by-side
#print axioms Lean4Lean.VEnv.piDescend_iff_neutralNVS_sortConv
#print axioms Lean4Lean.VEnv.rigidShapeVSUniq_iff
end Audit

end Lean4Lean
