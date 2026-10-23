import Erdos357

/-!
Axiom audit of EVERY declaration in the six 357 modules, not only the headline theorems.

For each constant whose home module is one of the six, `Lean.collectAxioms` walks the full
dependency graph (through Mathlib) and returns the axioms it uses. The audit fails if any
constant uses an axiom other than `propext`, `Classical.choice`, `Quot.sound`; this catches
`sorryAx` (an unfinished proof), `Lean.ofReduceBool` / `Lean.trustCompiler` (`native_decide`,
which trusts the compiler instead of the kernel), and any new `axiom` declaration.
Run from `lean/`:  lake env lean ../verification/AxiomAudit.lean
-/

open Lean Elab Command

def auditModules : Array Name := #[`Erdos.Proofs.P0357, `Erdos.Proofs.P0357Skip,
  `Erdos.Proofs.P0357Upper, `Erdos.Proofs.P0357Upper2, `Erdos.Proofs.P0357Upper4Gen,
  `Erdos.Proofs.P0357Upper4]

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut total := 0
  let mut nThm := 0
  let mut axiomDecls : Array Name := #[]
  let mut offenders : Array (Name × Array Name) := #[]
  let mut used : NameSet := {}
  let mut lines : Array String := #[]
  for mod in auditModules do
    let some idx := env.header.moduleNames.findIdx? (· == mod)
      | throwError "module {mod} is not loaded"
    let data := env.header.moduleData[idx]!
    let mut modThm := 0
    for ci in data.constants do
      let n := ci.name
      if ci matches .axiomInfo _ then axiomDecls := axiomDecls.push n
      if ci matches .thmInfo _ then modThm := modThm + 1
      let axs ← collectAxioms n
      for a in axs do used := used.insert a
      if axs.any (fun a => !standardAxioms.contains a) then
        offenders := offenders.push (n, axs)
    total := total + data.constants.size
    nThm := nThm + modThm
    lines := lines.push s!"{mod}: {data.constants.size} constants, {modThm} theorems"
  for l in lines do logInfo m!"{l}"
  let usedList := used.toList.map toString
  logInfo m!"TOTAL: {total} constants ({nThm} theorems) in {auditModules.size} modules"
  logInfo m!"axioms used by any of them: {usedList}"
  logInfo m!"axiom declarations inside these modules: {axiomDecls.size}"
  if offenders.isEmpty && axiomDecls.isEmpty then
    logInfo m!"AXIOM AUDIT PASSED: every constant depends only on propext, Classical.choice, Quot.sound"
  else
    for (n, axs) in offenders do
      logError m!"non-standard axioms in {n}: {axs}"
    throwError "AXIOM AUDIT FAILED"
