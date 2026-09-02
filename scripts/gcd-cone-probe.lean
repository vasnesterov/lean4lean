/-
**Which of the fuel-bound lemmas are in `Nat.gcd`'s and `Nat.bitwise`'s constant cones?**

`docs/handoff-primitive-natle.md` §1 and ledger row 121b say the six constants `f743c46`'s
recognizer used — `Nat.pos_of_ne_zero`, `Nat.mod_lt`, `Nat.lt_of_lt_of_le`, `Nat.le_of_lt_succ`,
`Nat.div_lt_self`, `Nat.le.refl` — are **all absent from both cones**, and that this is why the
constructed fuel-bound proof had to be replaced by a variable.

Measured here against the pinned toolchain's own environment, that is not what happens.  Only
`Nat.pos_of_ne_zero` is missing, and `Nat.zero_lt_of_ne_zero` — same statement, same
implicit/explicit split — is present in both.  See `docs/handoff-primitive-natle.md` §5.5.

The cone is the transitive `getUsedConstants` closure of type-and-value, i.e. what a replay that
adds a declaration's dependencies has to add.

Run: `lake env lean scripts/gcd-cone-probe.lean`
-/
import Lean
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

/-- The six constants `f743c46` used, the drop-in replacement for the one that is missing, and
the `Condition.natLE` machinery for comparison. -/
def probes : List Name :=
  [-- the six of row 121b
   ``Nat.pos_of_ne_zero, ``Nat.mod_lt, ``Nat.lt_of_lt_of_le, ``Nat.le_of_lt_succ,
   ``Nat.div_lt_self, ``Nat.le.refl,
   -- the replacement
   ``Nat.zero_lt_of_ne_zero,
   -- what the `Nat.mod` / `Nat.div` branches use, and the `Condition.natLE` machinery
   ``Nat.div_rec_fuel_lemma, ``Nat.decLe, ``Nat.ble, ``Nat.le_of_ble_eq_true,
   ``Nat.not_le_of_not_ble_eq_true, ``Bool.noConfusion, ``instDecidableEqBool, ``ite, ``dite,
   -- ex falso, for the "bind an implication" option
   ``False.elim, ``absurd, ``Not]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for seed in [``Nat.gcd, ``Nat.bitwise, ``Nat.div, ``Nat.modCore] do
    let c := cone env seed
    logInfo m!"{seed}: cone size {c.size}"
    logInfo m!"  PRESENT {probes.filter c.contains}"
    logInfo m!"  ABSENT  {probes.filter fun n => !c.contains n}"

-- the replacement really is a drop-in: same statement, same binder kinds
#check @Nat.pos_of_ne_zero       -- ∀ {n : Nat}, n ≠ 0 → 0 < n
#check @Nat.zero_lt_of_ne_zero   -- ∀ {a : Nat}, a ≠ 0 → 0 < a
