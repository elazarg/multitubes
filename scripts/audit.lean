/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
import Maths

/-!
# Environment audit

Audits declarations below the namespace selected by `AUDIT_NAMESPACE`. The output file stem is
selected by `AUDIT_OUTPUT`; both default to `Maths`. Application packages run a generated copy
whose import is changed to their library root module.
-/

open Lean Elab Command

run_cmd Command.liftCoreM do
  let env ← getEnv
  let namespaceName := (← IO.getEnv "AUDIT_NAMESPACE").getD "Maths"
  let output := (← IO.getEnv "AUDIT_OUTPUT").getD "scripts/.audit-Maths"
  let auditRoot := Name.mkSimple namespaceName
  let allowed : NameSet := {``propext, ``Classical.choice, ``Quot.sound}
  let mut names := #[]
  let mut axioms : NameSet := {}
  let mut sorries := #[]
  let mut forbidden := #[]
  for (n, _) in env.constants.toList do
    unless auditRoot.isPrefixOf n do continue
    unless n.isInternal do
      names := names.push n
      for a in (← Lean.collectAxioms n) do
        axioms := axioms.insert a
        if a == ``sorryAx then sorries := sorries.push n
        unless allowed.contains a do forbidden := forbidden.push (n, a)
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then
    throwError "no declarations found below audit namespace {namespaceName}"
  IO.FS.writeFile (output ++ ".decls")
    (String.intercalate "\n" (sorted.toList.map toString))
  IO.FS.writeFile (output ++ ".axioms")
    (String.intercalate "\n" (axioms.toList.map toString))
  IO.FS.writeFile (output ++ ".sorries")
    (String.intercalate "\n" (sorries.toList.map toString))
  IO.FS.writeFile (output ++ ".forbidden")
    (String.intercalate "\n" (forbidden.toList.map fun (n, a) => s!"{n}: {a}"))
  logInfo (s!"{namespaceName}: declarations {names.size}, sorry-dependent {sorries.size}, " ++
    s!"forbidden-axiom dependencies {forbidden.size}")
