import DatingAlgo

/-!
# Axiom check

Lists every declaration in the `DatingAlgo` library that depends on `sorry`, or on an
axiom beyond Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`).

This catches a proof that looks finished but relies, possibly through other lemmas,
on an open target in `DatingAlgo/Targets.lean`. Grepping for `sorry` can't see that.

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
      checked := checked + 1
      let axs ← collectAxioms c
      if axs.contains ``sorryAx then
        IO.println s!"SORRY {c} {modName}"
      let other := axs.filter fun a => a != ``sorryAx && !standard.contains a
      unless other.isEmpty do
        IO.println s!"AXIOM {c} {modName} {other}"
  IO.println s!"CHECKED {checked}"
