# Three-document LaTeX release

This folder is the self-contained paper release for *A complete
characterisation of conditional entropies*. The hierarchy was revised on
26 August 2026. All three documents use the same RevTeX layout, shared
`bibliography.bib`, and `ultimate.bst` bibliography style.

The documents have distinct roles:

1. `main-paper.tex` is the canonical 46-page journal manuscript. It
   introduces the formal definitions in the flow of the introduction, treats
   the former preliminary material on the entropy set as its own section, and
   contains Sections 4 and 5 directly. Those sections give the
   principal inequalities and finite counterexamples, while referring to the
   proof and Lean supplements when only a proof sketch fits.
2. `sections-4-5-full-details.tex` is the complete proof supplement. It expands
   the endpoint calculations, signed-measure differentiation, common
   discretization, two-block, three-block, and Shannon localization,
   temperate and tropical counterexamples, and semiring/channel lift. Its
   statement numbers mirror the canonical manuscript's 4.x/5.x numbering.
3. `lean-formalization-note.tex` is the Lean formalization supplement. It
   contains the theorem-facing proof map, trust boundary, reproducibility
   instructions, and statement-by-statement correspondence table through
   manuscript statement 5.10. The theorem-facing map uses result-to-ingredient
   arrows and is intentionally distinct from the repository's detailed Lean
   module graph, whose arrows run from prerequisite to dependent.

The canonical manuscript determines all statement numbering, and the
complete-proof and Lean supplements mirror it.

## Overleaf

Upload this entire folder to one Overleaf project. Choose any one of the three
`.tex` files as the project's **Main document**, select **pdfLaTeX**, and
compile. Overleaf runs BibTeX automatically when needed. To build another
document, change the Main document setting to the corresponding `.tex` file.

## Local compilation

For a document named `DOCUMENT.tex`, run:

```text
pdflatex DOCUMENT.tex
bibtex DOCUMENT
pdflatex DOCUMENT.tex
pdflatex DOCUMENT.tex
```

The `pdf` subfolder contains compile-verified PDFs of the three documents: the
main manuscript is 46 pages, the complete-proof supplement is 47 pages, and
the Lean supplement is 4 pages. The
sources, PDFs, and packaged ZIP are kept together so that GitHub and the
Overleaf-ready release describe the same document hierarchy.
