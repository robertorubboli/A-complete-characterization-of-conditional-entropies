# Conditional-entropy paper supplements

This folder is the self-contained source release for the two supplements to
[*A Complete Characterisation of Conditional
Entropies*](https://arxiv.org/abs/2601.23213). The canonical main manuscript is
maintained on arXiv and is intentionally not included in this repository. The
legacy directory path is retained so that links cited by the manuscript remain
stable.

The two supplements have distinct roles:

1. `sections-4-5-full-details.tex` supplies the complete analytic proofs behind
   Sections 4 and 5, including endpoint calculations, signed-measure
   differentiation, common discretization, two-block, three-block, and Shannon
   localization, temperate and tropical counterexamples, and the
   semiring/channel lift.
2. `lean-formalization-note.tex` records the theorem-facing proof map, trust
   boundary, reproducibility instructions, and statement-by-statement Lean
   correspondence through manuscript statement 5.10.

There is no separate concise Sections 4--5 document. Both supplements use the
shared `bibliography.bib` database and `ultimate.bst` bibliography style.

## Overleaf

Upload this folder to one Overleaf project. Select either supplement `.tex`
file as the project's **Main document**, choose **pdfLaTeX**, and compile. To
build the other supplement, change the Main document setting to the other
`.tex` file.

## Local compilation

For a supplement named `DOCUMENT.tex`, run:

```text
pdflatex DOCUMENT.tex
bibtex DOCUMENT
pdflatex DOCUMENT.tex
pdflatex DOCUMENT.tex
```

The `pdf` subfolder contains compile-verified copies of both supplements: the
complete-proof supplement is 47 pages and the Lean supplement is 4 pages. A
self-contained ZIP containing the sources, PDFs, and compile dependencies is
available one directory above as `conditional-entropies-supplements.zip`.
