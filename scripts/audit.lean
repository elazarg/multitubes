/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Maths

/-!
# Environment audit

Dumps the compiled environment for the two checks that the build itself cannot make: that no
declaration depends on `sorryAx`, and that every name a `## Main ...` docstring section promises
actually exists.  Run through `scripts/check.sh`, which reads the files written here.
-/

open Lean Elab Command

run_cmd Command.liftCoreM do
  let env ← getEnv
  let mut names := #[]
  let mut axioms : NameSet := {}
  let mut sorries := #[]
  for (n, _) in env.constants.toList do
    unless (`Maths).isPrefixOf n do continue
    unless n.isInternal do
      names := names.push n
      for a in (← Lean.collectAxioms n) do
        axioms := axioms.insert a
        if a == ``sorryAx then sorries := sorries.push n
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  IO.FS.writeFile "scripts/.decls" (String.intercalate "\n" (sorted.toList.map toString))
  IO.FS.writeFile "scripts/.axioms"
    (String.intercalate "\n" (axioms.toList.map toString))
  IO.FS.writeFile "scripts/.sorries"
    (String.intercalate "\n" (sorries.toList.map toString))
  logInfo s!"declarations {names.size}, sorry-dependent {sorries.size}"
