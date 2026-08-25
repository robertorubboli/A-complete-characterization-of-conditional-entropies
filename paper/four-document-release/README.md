# Four-document LaTeX release

This folder is a self-contained companion release for *A complete characterisation of conditional entropies*. It uses the same RevTeX layout and the shared `ultimate.bst` bibliography style throughout.

The four standalone documents are:

1. `main-paper.tex` - the main paper with numbered placeholders for Sections 4 and 5. The placeholders point to the three companion documents, preserve the later numbering, and make clear where the sufficient and necessary parameter proofs live.
2. `sections-4-5-concise.tex` - the concise, human-readable paper containing the statements and main ideas from Sections 4 and 5. Its necessity section displays every Shannon and rounded two-/three-block initial point and direction as a parenthesized finite vector. The tropical proofs state the exact midpoint and max-quasiconcavity inequalities used by the counterexamples. The formalization note is cited once at the beginning and is not mentioned inside the mathematical exposition.
3. `sections-4-5-full-details.tex` - the detailed proof paper, organized as the proof layer above the concise note. It includes the endpoint calculations, signed-measure differentiation, common discretization, exact localized counterexamples, tropical correction, and semiring/channel lift. Expectation, variance, covariance, escort weights, total variation, asymptotic notation, and the other technical symbols are defined before use.
4. `lean-formalization-note.tex` - the human-readable Lean correspondence note, updated dependency graph, complete full-details-numbered statement table through Proposition 2.10, trust boundary, and reproducibility information. Its introduction, graph caption, table caption, and continuation headings all state that their numbering comes from the full-details Sections 4 and 5 paper; the concise companion intentionally uses the same numbers. The note is self-contained and does not use another formalization paper as a presentation template or citation.

All four documents share `bibliography.bib` and `ultimate.bst` and have no other source-file dependencies.

## Overleaf

Upload this entire folder to one Overleaf project. Choose any one of the four `.tex` files as the project's **Main document**, select **pdfLaTeX**, and compile. Overleaf runs BibTeX automatically when needed. To build another document, change the Main document setting to the corresponding `.tex` file.

## Local compilation

For a document named `DOCUMENT.tex`, run:

```text
pdflatex DOCUMENT.tex
bibtex DOCUMENT
pdflatex DOCUMENT.tex
pdflatex DOCUMENT.tex
```

The `pdf` subfolder contains the four compile-verified PDFs from release tag
`four-document-release-v3-2026-08-25`. The source, PDFs, and packaged ZIP are
kept together so the GitHub release and the Overleaf folder describe the same
document state.
