# CLAUDE.md

Project guidance for `directed-transport`.

## What this is

A standalone, mathlib-idiomatic Lean library for the theory of **directed transport**:
operator-labelled transition graphs, their walks, holonomy, sections and lax sections, and
the exact, additive, finite-inequality, join-semidirect, and max-affine specializations.

It is extracted from the `MathUE/DirectedTransport` subtree of the `UniformEquilibrium`
research repository (`~/UniformEquilibrium`), which remains the reference for the original
proofs. That repository is pinned to Lean `v4.32.2`; this one targets `v4.33.1`, so ported
proofs occasionally need small repairs.

## Conventions

- Toolchain: `leanprover/lean4:v4.33.1`, mathlib pinned to `v4.33.1`.
- Root namespace is `DirectedTransport`. The source's `Math.*` namespaces are dropped:
  `Math.EdgeGraph` becomes `DirectedTransport.EdgeGraph`, `Math.TransferSummary.X` becomes
  `DirectedTransport.TransferSummary.X`, and so on.
- License is Apache 2.0. Every file starts with the mathlib copyright header, verbatim:

  ```
  /-
  Copyright (c) 2026 Elazar Gershuni. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Elazar Gershuni
  -/
  ```

- Every file uses the module system: `module`, then `public import` for imports needed in a
  *public declaration's signature* and plain `import` otherwise, then either
  `@[expose] public section` (mostly-public files) or per-declaration `public def`/
  `public theorem`.
- Every file has a `/-! ... -/` module docstring with `# Title`, prose, and `## Main
  definitions` / `## Main results` sections naming fully-qualified declarations.
- Structure fields and all public declarations need doc comments.

## Style is enforced by mathlib's own linters

`lakefile.toml` turns on the real linters from `Mathlib.Tactic.Linter.*` (`linter.style.*`)
project-wide, so there is no bespoke lint script. They cover the copyright header, 100-char
lines, 1500-line files, `fun` over `λ`, `<|` over `$`, `open Classical` scoping, `·` usage,
`cases`/`induction`/`refine`/`show` forms, whitespace, doc strings, and name checks.

**The tree must build with zero warnings.** `lake build` output containing `warning:` is a
failure, not a pass. Do not silence a linter with `set_option ... false` to get a file
through; fix the code instead.

## Working rules

- Never introduce `sorry`. The source library is entirely sorry-free and axiom-free, and so
  is this one; a port that needs a `sorry` is an unfinished port — say so rather than
  committing it.
- Do not weaken a theorem statement to make a v4.33.1 proof go through. If a proof cannot be
  repaired, report it rather than restating the theorem.
- Prefer fixing a broken proof idiomatically over patching around it. When a proof breaks
  because of a transparency or dependent-argument change, restating the lemma in a form that
  avoids the dependency (e.g. `List.head?` instead of `List.head` with a nonemptiness proof)
  is usually better than forcing the original.
