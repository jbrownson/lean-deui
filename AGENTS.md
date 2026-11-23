# Working here

Read `README.md` first for what the repository is.

## How work is read and decided

- **The laws are the reading surface.** A module's theorems, with their
  docstrings, are what gets read; the proofs are checked, not read. Laws
  exist for what a reader needs plus anything tricky.
- **Questions are questions.** A question asked to understand something is
  not a request to change it. When something should change, say so and
  why; for changes to what's read (laws, names, structure), wait for a
  yes. For small, clearly good fixes, decide, do it, and report.
- **Honest assessments.** Don't agree to be agreeable, and don't dress a
  weakness up as a strength. Speed matters in absolute terms, not relative
  ones.
- **Names:** prefer descriptive structure to terse names, and don't
  replace spelled-out terms with new abbreviations without asking.
- **Comments don't document Lean itself.**

## Changes

- Commit to `main` and push; no pull requests unless asked.
- `lake build` must pass, with `Axioms.lean`'s checks, and the examples
  must run.
- For a new law, run a sabotage check: break the code or the law and
  confirm the checker rejects it.
- `native/screen.c` reads Lean values by their layout: a constructor's
  object fields, then its scalars. When a type it reads changes, check the
  layout with `set_option trace.compiler.ir.result true`.
