# A complete characterization of conditional entropies

This repository contains the Lean 4 development accompanying Sections 4 and
5 of the manuscript. The current source tree contains the complete vertical
architecture: endpoint-aware Rényi parameters and integrals, positive-base
real-power calculus, signed-measure differentiation and discretization,
two-block, three-block, and Shannon localization, all necessity and
sufficiency branches, and the original conditional-semiring/channel lift.

The two terminal source declarations are:

- `ConditionalEntropy.mainClassification`, the assumption-free four-branch
  necessary-and-sufficient parameter classification; and
- `ConditionalEntropy.allConditionalEntropyAxioms`, the literal five-law
  package for every admissible candidate family.

The complete release audit passed on 25 August 2026. The root target built with
warnings treated as errors (2,864 jobs), the forbidden-token and exact
152-row correspondence scans passed, and the 21 audited public declarations
depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`
foundations. No project-specific axiom is used.

## Repository contents

- [`paper/four-document-release`](paper/four-document-release) is the
  self-contained four-paper LaTeX/Overleaf release. The main paper has numbered
  placeholders for Sections 4 and 5; the concise and full-detail companions use
  the same explicit finite counterexamples (including both tropical branches);
  and the Lean note contains the matching dependency graph and correspondence
  table through Proposition 2.10. Every number in that graph and table is the
  number in the full-details paper, while the concise paper deliberately uses
  the identical numbering. The upload-ready archive is
  [`paper/four-document-latex-release.zip`](paper/four-document-latex-release.zip).
- [`CompleteCharacterization.lean`](CompleteCharacterization.lean) is the
  project entry point. It imports `mainClassification`,
  `allConditionalEntropyAxioms`, the conditional-semiring order, and the
  independently checked boundary-kernel bundle. It also imports the standalone
  Hessian criterion and parameterized removable-Shannon quotient, so the root
  build checks the complete declaration-bearing release dependency tree.
- [`ConditionalEntropy/MainClassification.lean`](ConditionalEntropy/MainClassification.lean)
  assembles `necessityBundle` with the four sufficiency directions into the
  closed predicate `Classifies tau`.
- [`ConditionalEntropy/AllConditionalEntropyAxioms.lean`](ConditionalEntropy/AllConditionalEntropyAxioms.lean)
  assembles nonnegativity, embedding invariance, tensor additivity, fair-bit
  normalization, and monotonicity under embedded conditional majorization.
- [`paper/BLUEPRINT_STATEMENT_STATUS.md`](paper/BLUEPRINT_STATEMENT_STATUS.md)
  is the exhaustive 152-row correspondence table with exactly the columns
  **Manuscript statement**, **Lean declaration**, and **Status**. Its LaTeX
  counterpart is
  [`paper/blueprint-statement-correspondence.tex`](paper/blueprint-statement-correspondence.tex).
- [`paper/dependency-graph.dot`](paper/dependency-graph.dot) is the authoritative
  condensed dependency graph. [`DEPENDENCIES.md`](DEPENDENCIES.md) explains its
  layers, and [`paper/DECLARATION_INDEX.md`](paper/DECLARATION_INDEX.md) records
  paper-facing declaration dependencies. The checked-in SVG and PNG are
  renderings of the DOT source.
- [`paper/lean-formalization-appendix.tex`](paper/lean-formalization-appendix.tex)
  is the LaTeX appendix containing the dependency graph, exact terminal
  signatures, trust-boundary protocol, and three-column correspondence table.
  [`paper/main-with-lean-appendix.tex`](paper/main-with-lean-appendix.tex) is the
  supplied main paper with that appendix included.
- [`paper/blueprint-sections-4-5.tex`](paper/blueprint-sections-4-5.tex) is the
  repository copy of the supplied self-contained blueprint used to order the
  statement audit.

## Main proof layers

The classification branch follows this dependency path:

```text
finite data and endpoint-aware parameter measures
  → Rényi/real-power calculus and signed integration
  → two-block and three-block localization
  → Shannon log-mass, expansion, and localization
  → temperate, tropical, and derivation necessity
  → necessityBundle
  → mainClassification
```

In parallel, the channel-law branch formalizes the finite conditional
semiring, its quotient order, concrete channel comparison, `embeddingLift`,
and the normalization/tensor/embedding packages consumed by
`allConditionalEntropyAxioms`.

## Reading the correspondence table

The ledger uses two status forms:

- **Formalized**: a matching declaration is present and covered by the strict
  root build.
- **Formalized (split API)**: the manuscript package is represented by the
  listed smaller declarations, all covered by the strict root build.

## Reproduce the checks

The project is pinned to **Lean 4.32.2** by
[`lean-toolchain`](lean-toolchain) and **Mathlib 4.32.2** by
[`lakefile.toml`](lakefile.toml). On Windows, run from the repository root:

```powershell
powershell -File scripts/check.ps1
```

The script scans project Lean sources for `sorry`, `admit`, project-defined
`axiom`, and project-defined `opaque`; builds `CompleteCharacterization` with
warnings treated as errors; runs the kernel dependency audit in
[`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean); and checks the exact
152-row, three-column correspondence invariant. Standard Lean and Mathlib
logical dependencies reported by `#print axioms` are part of the trusted
foundation, not project-specific axioms.

To refresh the graph renderings after editing the DOT source:

```powershell
npm install
npm run render:graph
```

## License

Apache License 2.0; see [LICENSE](LICENSE).
