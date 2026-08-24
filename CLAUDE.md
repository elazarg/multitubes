# CLAUDE.md

Project guidance for `directed-transport`.

## What this is

A standalone, mathlib-idiomatic Lean library for the theory of **directed transport**:
operator-labelled transition graphs, their walks, holonomy, sections and lax sections, and
the exact, additive, finite-inequality, join-semidirect, and max-affine specializations.

## Conventions

- Toolchain: `leanprover/lean4:v4.33.1`, mathlib pinned to `v4.33.1`.
- Root namespace is `DirectedTransport`.
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
- Section headings come from mathlib's own vocabulary and nothing else: `Main definitions`,
  `Main results`, `Implementation notes`, `TODO`, `References`, `Tags`. A census of the pinned
  snapshot found the alternatives this library once used (`Scope`, `Vocabulary`, and the rest)
  occur zero times in mathlib.
- Docstrings state mathematics, not history. No mention of porting, extraction, provenance, this
  repository's own development, or other project documents; and "this file", never "this
  library".

## Style is enforced by mathlib's own linters

`lakefile.toml` turns on the real linters from `Mathlib.Tactic.Linter.*` (`linter.style.*`)
project-wide, so there is no bespoke lint script. They cover the copyright header, 100-char
lines, 1500-line files, `fun` over `λ`, `<|` over `$`, `open Classical` scoping, `·` usage,
`cases`/`induction`/`refine`/`show` forms, whitespace, doc strings, and name checks.

**The tree must build with zero warnings.** `lake build` output containing `warning:` is a
failure, not a pass. Do not silence a linter with `set_option ... false` to get a file
through; fix the code instead.

## Invariants

Four properties are checked and must hold before anything is committed. They are what the
project's claims rest on, so treat a regression in any of them as a build failure:

1. **A rebuild from clean** ends at zero errors and zero
   warnings. An incremental build is not evidence; nor is a build that does not reach the file
   you changed - a new file absent from `DirectedTransport/All.lean` is not compiled at all.
2. **Zero docstring drift**: every declaration named in a `## Main ...` section resolves against
   the compiled environment.
3. **Zero declarations depend on `sorryAx`**, checked at the kernel by `Lean.collectAxioms`. The
   only axioms used anywhere are `propext`, `Classical.choice` and `Quot.sound`.
4. **No line exceeds 100 characters**, and no `set_option` survives in a committed file.

## Working rules

- Never introduce `sorry`. Work that needs one is unfinished - say so rather than committing it.
- Never weaken a theorem to make it provable, and never present a weaker result under a stronger
  name. If a statement will not go through, report where it fails; a quietly weakened theorem is
  worse than an absent one, because the library's value is that its claims are checkable.
- State the hypotheses a proof actually uses, not the ones the textbook assumes. Several results
  here hold under strictly weaker assumptions than their classical statements, and each says so.
- Prefer fixing a proof idiomatically over patching around it. When one breaks on a transparency
  or dependent-argument issue, restating the lemma to avoid the dependency (`List.head?` rather
  than `List.head` with a nonemptiness proof) usually beats forcing the original.
- Put a declaration where a reader would look for it, not where it was first needed. A statement
  mentioning only walks belongs in the walk calculus even if only one specialization uses it.
