# A complete characterization of conditional entropies

This repository accompanies the canonical manuscript [*A Complete
Characterisation of Conditional
Entropies*](https://arxiv.org/abs/2601.23213) with a Lean 4 development and two
auxiliary documents: a complete-proof account of Sections 4 and 5 and a
Lean-formalization note.

The two terminal Lean declarations are:

- `ConditionalEntropy.mainClassification`, the assumption-free four-branch
  necessary-and-sufficient parameter classification; and
- `ConditionalEntropy.allConditionalEntropyAxioms`, the five-law package for
  every admissible candidate family.

Both use the natural-log convention of the complete-proof paper; an
independent fair bit therefore has value `Real.log 2`.

The Lean development begins with the four concrete candidate families and
proves their exact parameter classification and five-law package.

The development contains no `sorry`, `admit`, project-defined `axiom`, or
project-defined `opaque`. Its public declarations use only Lean and Mathlib's
standard logical foundations.

## Auxiliary documents

The complete-proof auxiliary document determines the numbering used by the
Lean correspondence. GitHub hosts the following two auxiliary documents:

1. **Complete-proof auxiliary document.**
   [`sections-4-5-full-details.tex`](paper/auxiliary-files/sections-4-5-full-details.tex)
   supplies the endpoint calculus, signed-measure arguments, common
   discretization, localized counterexamples, tropical corrections, and
   semiring/channel lift supporting Sections 4 and 5. Download the
   compile-verified
   [`sections-4-5-full-details.pdf`](paper/auxiliary-files/pdf/sections-4-5-full-details.pdf).
2. **Lean-formalization auxiliary document.**
   [`lean-formalization-note.tex`](paper/auxiliary-files/lean-formalization-note.tex)
   contains the theorem-facing proof map, trust audit, reproducibility
   instructions, a one-to-one public-declaration table for the sixteen
   numbered main-text statements 4.1--5.9, and a separate Appendix A audit.
   Download the compile-verified
   [`lean-formalization-note.pdf`](paper/auxiliary-files/pdf/lean-formalization-note.pdf).

Both sources use the shared
[`bibliography.bib`](paper/auxiliary-files/bibliography.bib) and
[`ultimate.bst`](paper/auxiliary-files/ultimate.bst) files. The
self-contained
[`conditional-entropies-auxiliary-files.zip`](paper/conditional-entropies-auxiliary-files.zip)
contains both sources, both PDFs, and their compile dependencies. See the
auxiliary-files [`README`](paper/auxiliary-files/README.md) for build
instructions.

## Lean development

- [`CompleteCharacterization.lean`](CompleteCharacterization.lean) is the
  integrated project entry point.
- [`ConditionalEntropy/FullDetailsStatements.lean`](ConditionalEntropy/FullDetailsStatements.lean)
  is the stable paper-facing interface: each of the sixteen numbered
  main-text environments 4.1--5.9 has one distinct canonical Lean theorem.
  Lower-level implementation lemmas remain many-to-many dependencies beneath
  that interface.
- [`ConditionalEntropy/MainClassification.lean`](ConditionalEntropy/MainClassification.lean)
  assembles `necessityBundle` with the four sufficiency directions into the
  closed predicate `Classifies tau`.
- [`ConditionalEntropy/AllConditionalEntropyAxioms.lean`](ConditionalEntropy/AllConditionalEntropyAxioms.lean)
  assembles nonnegativity, embedding invariance, tensor additivity, fair-bit
  normalization, and monotonicity under embedded conditional majorization.
- [`paper/BLUEPRINT_STATEMENT_STATUS.md`](paper/BLUEPRINT_STATEMENT_STATUS.md)
  is the exhaustive three-column internal-blueprint ledger. It uses the
  headings **Manuscript statement**, **Lean declaration**, and **Status**. Its
  LaTeX counterpart is
  [`paper/blueprint-statement-correspondence.tex`](paper/blueprint-statement-correspondence.tex).
- [`paper/blueprint-sections-4-5.tex`](paper/blueprint-sections-4-5.tex) is the
  dependency-closed internal specification consumed by the structural ledger
  audit.
- [`paper/full-details-correspondence.json`](paper/full-details-correspondence.json)
  is the machine-readable 31-row audit for all numbered main-text and Appendix
  environments in the complete-proof document. It records one exact canonical
  declaration per row.
- [`paper/FULL_DETAILS_CORRESPONDENCE.md`](paper/FULL_DETAILS_CORRESPONDENCE.md)
  is the GitHub-readable three-column rendering of that one-to-one index.

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
  [Lean-formalization auxiliary document](paper/auxiliary-files/lean-formalization-note.tex)
  connects the public conclusions and the complete-proof paper's numbered
  4.x/5.x statements to reusable proof ingredients. Its arrows run from a
  result to the ingredients used to establish it.

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
validates the separate 152-row internal-blueprint ledger, and runs the
full-details numbering/declaration audit in
[`scripts/check-full-details-correspondence.ps1`](scripts/check-full-details-correspondence.ps1).
See
[`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md) for the audited scope.

To refresh the detailed implementation graph after editing its DOT source:

```powershell
npm install
npm run render:graph
```

## License

Apache License 2.0; see [LICENSE](LICENSE).
