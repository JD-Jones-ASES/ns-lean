import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Walks every constant in the environment whose name begins with `NS.` (every declaration of this
development, `Challenge.lean` excluded since it is not imported), `_private.NS.` (private
auxiliaries of the `NS.*` modules) or `_private.Solution.`, and collects the axioms each depends
on. Anything outside `propext`, `Classical.choice`, `Quot.sound` is reported with `logError`, which
fails `lake build`. The audit also fails if it matched fewer than the floor below (so a renamed
namespace cannot make it pass vacuously) or if any of the six compared theorems is missing from
the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "NS." || label.startsWith "_private.NS." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 100 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 100"
  for n in [`NS.D3_8_ge_810, `NS.conjecture13_fails_3_2_8, `NS.D3_8e_ge, `NS.D3_8e4_ge,
      `NS.conjecture13_fails_3_2_all, `NS.liminf_ge] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
