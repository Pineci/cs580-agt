import DatingAlgo

/-!
# Axiom check

For every declaration in the `DatingAlgo` library, reports one of:
- `OPEN`: its own proof contains `sorry`, so it is an open target;
- `DEPENDS`: it has no `sorry` of its own but relies, possibly through other
  lemmas, on an open target;
- `AXIOM`: it uses an axiom beyond Lean's standard three (`propext`,
  `Classical.choice`, `Quot.sound`).

Grepping for `sorry` can't see the `DEPENDS` case.

Run from `lean/` with `lake env lean scripts/AxiomCheck.lean`; `lean/check.sh` does
this and summarizes the output.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for modName in env.header.moduleNames, modData in env.header.moduleData do
    unless (`DatingAlgo).isPrefixOf modName do continue
    for c in modData.constNames do
      if c.isInternal then continue
      -- Only theorems carry proofs worth reporting; definitions are data.
      let isThm := match env.find? c with
        | some (.thmInfo _) => true
        | _ => false
      unless isThm do continue
      checked := checked + 1
      let axs ← collectAxioms c
      if axs.contains ``sorryAx then
        let direct : Bool := match env.find? c with
          | some ci => match ci.value? (allowOpaque := true) with
            | some v => v.getUsedConstants.contains ``sorryAx
            | none => false
          | none => false
        IO.println s!"{if direct then "OPEN" else "DEPENDS"} {c} {modName}"
      let other := axs.filter fun a => a != ``sorryAx && !standard.contains a
      unless other.isEmpty do
        IO.println s!"AXIOM {c} {modName} {other}"
  IO.println s!"CHECKED {checked}"
