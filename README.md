# A complete characterization of conditional entropies

This repository contains the journal manuscript, its proof and formalization
supplements, and the accompanying Lean 4 development. The document hierarchy
was reorganized on 26 August 2026 so that the journal paper is the canonical,
46-page presentation: the definitions needed for the results are introduced
in the flow of its introduction, Sections 4 and 5 present the sufficiency and
necessity arguments, and omitted technical steps point to the
complete-proof and Lean supplements.

The two terminal Lean declarations are:

- `ConditionalEntropy.mainClassification`, the assumption-free four-branch
  necessary-and-sufficient parameter classification; and
- `ConditionalEntropy.allConditionalEntropyAxioms`, the five-law package for
  every admissible candidate family.

The development contains no `sorry`, `admit`, project-defined `axiom`, or
project-defined `opaque`. Its public declarations use only Lean and Mathlib's
standard logical foundations.

## Paper and supplements

The three compile targets use the same bibliography and
`ultimate.bst` style:

1. **Canonical journal manuscript.**
   [`main-paper.tex`](paper/three-document-release/main-paper.tex) contains
   Sections 4 and 5 directly and fixes the statement numbering
   used by every supplement. A compile-verified copy is available as
   [`main-paper.pdf`](paper/three-document-release/pdf/main-paper.pdf).
2. **Complete proof supplement.**
   [`sections-4-5-full-details.tex`](paper/three-document-release/sections-4-5-full-details.tex)
   gives the endpoint calculus, signed-measure arguments, discretization,
   localized counterexamples, tropical corrections, and semiring/channel lift
   omitted from the journal manuscript. It mirrors the manuscript's 4.x/5.x
   numbering. Download the compile-verified
   [`sections-4-5-full-details.pdf`](paper/three-document-release/pdf/sections-4-5-full-details.pdf).
3. **Lean formalization supplement.**
   [`lean-formalization-note.tex`](paper/three-document-release/lean-formalization-note.tex)
   contains the theorem-facing proof map, trust audit, and statement-by-statement
   correspondence table through manuscript statement 5.10. Download the
   compile-verified
   [`lean-formalization-note.pdf`](paper/three-document-release/pdf/lean-formalization-note.pdf).

The complete Overleaf-ready package is
[`paper/three-document-latex-release.zip`](paper/three-document-latex-release.zip),
and [`paper/three-document-release/README.md`](paper/three-document-release/README.md)
explains how to compile each document.

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
  is the exhaustive three-column ledger: **Manuscript statement**, **Lean
  declaration**, and **Status**. Its LaTeX counterpart is
  [`paper/blueprint-statement-correspondence.tex`](paper/blueprint-statement-correspondence.tex).

The classification branch has the following high-level dependency path:

```text
finite data and endpoint-aware parameter measures
  -> Renyi/real-power calculus and signed integration
  -> two-block, three-block, and Shannon localization
  -> temperate, tropical, and derivation necessity
  -> necessityBundle
  -> mainClassification
```

In parallel, the channel-law branch formalizes the finite conditional semiring,
its quotient order, concrete channel comparison, `embeddingLift`, and the
candidate-law packages consumed by `allConditionalEntropyAxioms`.

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

These diagrams answer different questions and intentionally use opposite arrow
conventions. [`DEPENDENCIES.md`](DEPENDENCIES.md) documents the distinction and
the module groups in the implementation graph.

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
