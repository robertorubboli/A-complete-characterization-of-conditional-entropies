# Conditional-entropy auxiliary files

This folder is the self-contained source release for the two auxiliary
documents accompanying
[*A Complete Characterisation of Conditional
Entropies*](https://arxiv.org/abs/2601.23213). The canonical main manuscript is
maintained on arXiv and is intentionally not included in this repository. This
directory contains only the two auxiliary documents and their shared build
dependencies.

The two auxiliary documents have distinct roles:

1. `sections-4-5-full-details.tex` supplies the complete analytic proofs behind
   Sections 4 and 5, including endpoint calculations, signed-measure
   differentiation, common discretization, two-block, three-block, and Shannon
   localization, temperate and tropical counterexamples, and the
   semiring/channel lift.
2. `lean-formalization-note.tex` records the theorem-facing proof map, trust
   boundary, reproducibility instructions, a one-to-one canonical Lean
   declaration for every numbered main-text statement 4.1--5.9, and a
   separate audit of the numbered Appendix A statements.

The complete-proof paper's 4.1--5.9 and A.1--A.15 numbering and natural-log
convention are the sole specification for the organization of the Lean
correspondence. The public one-to-one table is deliberately separate from the
many-to-many implementation dependency graph.

There is no separate concise Sections 4--5 document. Both auxiliary documents
use the shared `bibliography.bib` database and `ultimate.bst` bibliography
style.

## Overleaf

Upload this folder to one Overleaf project. Select either auxiliary `.tex`
file as the project's **Main document**, choose **pdfLaTeX**, and compile. To
build the other document, change the Main document setting to the other
`.tex` file.

## Local compilation

For an auxiliary document named `DOCUMENT.tex`, run:

```text
pdflatex DOCUMENT.tex
bibtex DOCUMENT
pdflatex DOCUMENT.tex
pdflatex DOCUMENT.tex
```

The `pdf` subfolder contains compile-verified copies of both auxiliary
documents: the complete-proof document is 47 pages and the Lean document is 6
pages. A self-contained ZIP containing the sources, PDFs, and compile
dependencies is available one directory above as
`conditional-entropies-auxiliary-files.zip`.
