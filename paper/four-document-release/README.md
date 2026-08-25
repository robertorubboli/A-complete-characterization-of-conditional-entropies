# Four-document LaTeX release

This folder is a self-contained companion release for *A complete characterisation of conditional entropies*. It uses the same RevTeX layout and the shared `ultimate.bst` bibliography style throughout.

The four standalone documents are:

1. `main-paper.tex` - the main paper with Sections 4 and 5 and the Lean appendix removed. It preserves the later section and theorem numbering and cites the three companion documents as separate works.
2. `sections-4-5-concise.tex` - the concise, human-readable paper containing the main ideas and statements from Sections 4 and 5.
3. `sections-4-5-full-details.tex` - the detailed proof paper, including the analytic calculations, endpoint arguments, localization arguments, discretization, and the semiring/channel lift.
4. `lean-formalization-note.tex` - the human-readable Lean correspondence note, dependency graph, statement table, trust boundary, and reproducibility information.

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

The `pdf` subfolder contains the four compile-verified PDFs from this release.
