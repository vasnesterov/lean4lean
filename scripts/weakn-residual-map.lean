import Lean4Lean.Experimental.ConeJoin
import Lean4Lean.Theory.Typing.ConstSubst
import Lean4Lean.Verify.Typing.ConstSpineWF

/-!
# The residual map for `VEnv.IsDefEqU.weakN_iff`

Three questions, all answered by the *same* walker `scripts/hole-cone.lean` uses
(`deps` with `allowOpaque := true`, walking type AND value, so `.thmInfo` values are not
silently empty):

1. **Direct users** of the hole, and for each of a chosen set of seeds, the *routes*: the
   members of the seed's cone whose own direct dependencies contain the hole.
2. **Supplies**: for each candidate sub-statement / lemma, whether its cone reaches the hole
   (circular) and which named holes it does reach.
3. **`parRedK_weakN_invP`'s four appeals**: enumerate them, and print which of them are the
   *typing gates* (`StrengthenNarrow.lean` §5 reproves those from `TypingStrengthening`) and
   which are genuine two-endpoint conversions.

    ~/.elan/bin/lake env lean scripts/weakn-residual-map.lean
-/
open Lean

def deps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => s.union v.getUsedConstantsAsSet
  | none => s

partial def go (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then go env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | some ci => go env ((deps ci).toList ++ rest) seen
    | none => go env rest seen

def cone (env : Environment) (seed : Name) : NameSet := go env [seed] {}

def directDeps (env : Environment) (n : Name) : NameSet :=
  match env.find? n with | some ci => deps ci | none => {}

/-- The named holes (declarations directly containing `sorryAx`) in a cone. -/
def holesIn (env : Environment) (c : NameSet) : List Name :=
  c.toList.filter fun n =>
    n != ``sorryAx && !n.isInternal && (directDeps env n).contains ``sorryAx

def hole : Name := ``Lean4Lean.VEnv.IsDefEqU.weakN_iff

/-- Members of `c` that depend on `hole` directly (the "routes" to the hole). -/
def routes (env : Environment) (c : NameSet) : List Name :=
  c.toList.filter fun n => n != hole && (directDeps env n).contains hole

/-- Seeds whose *routes* we want enumerated. -/
def routeSeeds : List Name :=
  [``Lean4Lean.VEnv.ParRed.weakN_inv,
   ``Lean4Lean.VEnv.parRedK_weakN_invP,
   ``Lean4Lean.VEnv.parRedK_weakN_invPS,
   ``Lean4Lean.VEnv.IsDefEq.church_rosser]

/-- Candidate supplies: does the cone reach the hole? -/
def supplies : List Name :=
  [-- the reduction chain (must be hole-free, else the reduction is circular)
   ``Lean4Lean.VEnv.StrengtheningTarget.iff_piDescend_narrow,
   ``Lean4Lean.VEnv.Strengthening.of_typing_narrow,
   ``Lean4Lean.VEnv.TypingStrengthening.iff_piDescend,
   ``Lean4Lean.VEnv.TypingStrengthening.hasType_inv,
   ``Lean4Lean.VEnv.TypingStrengthening.onCtx_inv,
   ``Lean4Lean.VEnv.TypingStrengthening.wf_inv,
   ``Lean4Lean.VEnv.TypingStrengthening.typed,
   ``Lean4Lean.VEnv.SortConvStrengthening.of_typing,
   ``Lean4Lean.VEnv.TransStrengtheningNarrow.at_sort,
   ``Lean4Lean.VEnv.StrengtheningTarget.of_normalEqComplete,
   ``Lean4Lean.VEnv.checkStrengthening_iff_target,
   -- the lemmas a Π/Prop-slice argument would consume
   ``Lean4Lean.VEnv.IsDefEqU.of_l,
   ``Lean4Lean.VEnv.IsDefEq.uniq,
   ``Lean4Lean.VEnv.IsDefEqU.forallE_inv,
   ``Lean4Lean.VEnv.IsType.forallE_inv,
   ``Lean4Lean.VEnv.IsDefEq.isType,
   ``Lean4Lean.VEnv.IsDefEq.weakN,
   ``Lean4Lean.VExpr.instN_bvar0,
   -- the claimed-clean supplies
   ``Lean4Lean.VEnv.patWF,
   ``Lean4Lean.VEnv.patWF_iota,
   ``Lean4Lean.VEnv.patWF_quot,
   ``Lean4Lean.VEnv.patWF_of_wf,
   ``Lean4Lean.VEnv.piInv_axiom,
   -- the const-injectivity family (claimed circular)
   ``Lean4Lean.VEnv.constApp_inv_of_patWF,
   ``Lean4Lean.VEnv.constApp_inv_of_wf,
   ``Lean4Lean.VEnv.const_app_inv_of_wf]

def typingGates : List Name :=
  [``Lean4Lean.VEnv.HasType.weakN_iff, ``Lean4Lean.VEnv.IsType.weakN_iff,
   ``Lean4Lean.VExpr.WF.weakN_iff, ``Lean4Lean.OnCtx.weakN_inv,
   ``Lean4Lean.OnCtx.weak'_inv, ``Lean4Lean.VEnv.HasType.weak'_iff,
   ``Lean4Lean.VEnv.IsType.weak'_iff, ``Lean4Lean.VExpr.WF.weak'_iff,
   ``Lean4Lean.VEnv.HasType.skips]

def gateTag (n : Name) : String :=
  if typingGates.contains n then "   [typing gate]" else ""

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Lean4Lean.Experimental.ConeJoin},
                            {module := `Lean4Lean.Theory.Typing.ConstSubst},
                            {module := `Lean4Lean.Verify.Typing.ConstSpineWF}] {}
  -- (1) direct users of the hole, across all of Lean4Lean
  let mut direct : Array Name := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    unless (`Lean4Lean).isPrefixOf n do continue
    if n == hole then continue
    if (directDeps env n).contains hole then direct := direct.push n
  IO.println s!"== (1) direct users of {hole}: {direct.size}"
  for n in direct.qsort (·.toString < ·.toString) do
    IO.println s!"    {n}{gateTag n}"
  -- (2) routes per seed
  IO.println "== (2) routes to the hole inside each seed's cone"
  for s in routeSeeds do
    let c := cone env s
    IO.println s!"  {s}: cone {c.size}"
    for r in (routes env c).toArray.qsort (·.toString < ·.toString) do
      IO.println s!"      route: {r}{gateTag r}"
  -- (3) supplies
  IO.println "== (3) supplies: cone size, reaches-the-hole, named holes"
  for s in supplies do
    match env.find? s with
    | none => IO.println s!"  {s}: MISSING"
    | some _ =>
      let c := cone env s
      let hs := (holesIn env c).filter (· != hole)
      IO.println s!"  {s}: cone {c.size}, reaches hole {c.contains hole}, other holes {hs}"

#eval! main
