# A complete characterization of conditional entropies

This repository contains the two auxiliary documents for the canonical
manuscript [*A Complete Characterisation of Conditional
Entropies*](https://arxiv.org/abs/2601.23213), together with the accompanying
Lean 4 development. The main manuscript is maintained on arXiv and its source
and PDF are intentionally not duplicated here. Sections 4 and 5 now appear
directly in that manuscript; there is no separate concise Sections 4--5 note.

The two terminal Lean declarations are:

- `ConditionalEntropy.mainClassification`, the assumption-free four-branch
  necessary-and-sufficient parameter classification; and
- `ConditionalEntropy.allConditionalEntropyAxioms`, the five-law package for
  every admissible candidate family.

The development contains no `sorry`, `admit`, project-defined `axiom`, or
project-defined `opaque`. Its public declarations use only Lean and Mathlib's
standard logical foundations.

## Paper supplements

The manuscript on arXiv determines the statement numbering. GitHub hosts the
following two supplements:

1. **Complete proof supplement.**
   [`sections-4-5-full-details.tex`](paper/three-document-release/sections-4-5-full-details.tex)
   supplies the endpoint calculus, signed-measure arguments, common
   discretization, localized counterexamples, tropical corrections, and
   semiring/channel lift supporting Sections 4 and 5. Download the
   compile-verified
   [`sections-4-5-full-details.pdf`](paper/three-document-release/pdf/sections-4-5-full-details.pdf).
2. **Lean formalization supplement.**
   [`lean-formalization-note.tex`](paper/three-document-release/lean-formalization-note.tex)
   contains the theorem-facing proof map, trust audit, reproducibility
   instructions, and statement-by-statement correspondence table through
   manuscript statement 5.10. Download the compile-verified
   [`lean-formalization-note.pdf`](paper/three-document-release/pdf/lean-formalization-note.pdf).

Both sources use the shared
[`bibliography.bib`](paper/three-document-release/bibliography.bib) and
[`ultimate.bst`](paper/three-document-release/ultimate.bst) files. The
self-contained
[`conditional-entropies-supplements.zip`](paper/conditional-entropies-supplements.zip)
contains both sources, both PDFs, and their compile dependencies. See the
supplements [`README`](paper/three-document-release/README.md) for build
instructions.

## Lean development

- [`CompleteCharacterization.lean`](CompleteCharacterization.lean) is the
  integrated project entry point.
- [`ConditionalEntropy/MainClassification.lean`](ConditionalEntropy/MainClassification.lean)
  assembles `necessityBundle` with the four sufficiency directions into the
  closed predicate `Classifies tau`.
- [`ConditionalEntropy/AllConditionalEntropyAxioms.lean`](ConditionalEntropy/AllConditionalEntropyAxioms.lean)
  assembles nonnegativity, embedding invariance, tensor additivity, fair-bit
  normalization, and monotonicity under embedded conditional majorization.
- [`paper/BLUEPRINT_STATEMENT_STATUS.md`](paper/BLUEPRINT_STATEMENT_STATUS.md)
  is the exhaustive three-column formalization ledger: **Manuscript
  statement**, **Lean declaration**, and **Status**. Its LaTeX counterpart is
  [`paper/blueprint-statement-correspondence.tex`](paper/blueprint-statement-correspondence.tex).
- [`paper/blueprint-sections-4-5.tex`](paper/blueprint-sections-4-5.tex) is the
  dependency-closed specification consumed by the correspondence audit. It is
  an internal formalization artifact, not a separate concise paper supplement.

The classification branch has the following high-level dependency path:

```text
finite data and endpoint-aware parameter measures
  -> Renyi/real-power calculus and signed integration
  -> two-block, three-block, and Shannon localization
  -> temperate, tropical, and derivation necessity
  -> necessityBundle
  -> mainClassification
```

In parallel, the channel-law branch formalizes the finite conditional
semiring, its quotient order, concrete channel comparison, `embeddingLift`,
and the candidate-law packages consumed by `allConditionalEntropyAxioms`.

## Two complementary dependency views

- The detailed **Lean implementation dependency graph** is maintained in
  [`paper/dependency-graph.dot`](paper/dependency-graph.dot) and rendered as
  [`SVG`](paper/dependency-graph.svg) and
  [`PNG`](paper/dependency-graph.png). It groups concrete Lean modules, uses
  prerequisite-to-dependent arrows, and colors boxes by technical subsystem.
- The **theorem-facing proof map** in the
  [Lean formalization supplement](paper/three-document-release/lean-formalization-note.tex)
  connects the public conclusions and the manuscript's numbered 4.x/5.x
  statements to reusable proof ingredients. Its arrows run from a result to
  the ingredients used to establish it.

These diagrams answer different questions and intentionally use opposite
arrow conventions. [`DEPENDENCIES.md`](DEPENDENCIES.md) documents the
distinction and the module groups in the implementation graph.

## Reproduce the checks

The project is pinned to **Lean 4.32.2** by
[`lean-toolchain`](lean-toolchain) and **Mathlib 4.32.2** by
[`lakefile.toml`](lakefile.toml). On Windows, run from the repository root:

```powershell
powershell -File scripts/check.ps1
```

The script scans the project Lean sources for forbidden proof-gap tokens,
builds `CompleteCharacterization` with warnings treated as errors, runs the
kernel dependency audit in [`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean),
and validates the three-column correspondence ledger. See
[`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md) for the audited scope.

To refresh the detailed implementation graph after editing its DOT source:

```powershell
npm install
npm run render:graph
```

## License

Apache License 2.0; see [LICENSE](LICENSE).
