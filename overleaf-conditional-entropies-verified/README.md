# LaTeX bundle: main paper with Lean appendix

This folder is self-contained with respect to the manuscript's local file
dependencies. Compile from this folder so that the `paper/...` input paths and
the bibliography paths resolve correctly.

## Entry points

- `main.tex` builds the complete paper with the Lean formalization appendix.
- `appendix-only.tex` builds only the Lean appendix and correspondence table.

These are the only `.tex` files in the folder, and both are independently
compilable. Files ending in `.inc` are internal fragments included by those
entry points; they should not be selected as Overleaf's main document.

This bundle contains two distinct graph views. The appendix draws the
**condensed two-branch architecture overview** directly with TikZ. The DOT,
SVG, and PNG files in `paper/` are three formats of the more detailed **Lean
implementation dependency graph** at module-group level; they are reference
artifacts and are not needed by TeX during compilation. Both views use arrows
from prerequisite to dependent. The Lean formalization supplement contains
the **theorem-facing proof map**, whose arrows deliberately run from result to
proof ingredient.

## Recommended compilation

With a current TeX Live or MiKTeX installation containing REVTeX 4.2, BibTeX,
TikZ/PGF, and the standard science-publishing packages, run:

```text
latexmk -pdf main.tex
```

If `latexmk` is unavailable, use:

```text
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

To compile only the appendix:

```text
latexmk -pdf appendix-only.tex
```

or run `pdflatex appendix-only.tex` twice.

## Included local dependencies

```text
main.tex
appendix-only.tex
bibliography.bib
ultimate.bst
paper/
  lean-formalization-appendix.inc
  blueprint-statement-correspondence.inc
  dependency-graph.dot
  dependency-graph.svg
  dependency-graph.png
```

The bibliography includes all citation keys used by `main.tex`, including the
`bhatia1997matrix` entry that was absent from the archived bibliography source.

## TeX packages

The main file uses `revtex4-2` and packages including AMS math/fonts,
`mathrsfs`, `dsfont`, `graphicx`, `hyperref`, `xurl`, `natbib`, `tikz`, `longtable`,
`booktabs`, `array`, `multirow`, `forest`, `bm`, `empheq`, and `enumitem`. A
full TeX Live installation is the simplest option; MiKTeX can install missing
packages on demand.

Do not add `caption` or `subcaption` to `main.tex`: REVTeX supplies its own
caption and `longtable*` support, and those packages cause the Overleaf error
`Command \longtable* already defined.` The appendix uses only ordinary REVTeX
captions and does not need either package.

The correspondence table deliberately uses plain `l` columns containing
fixed-width minipages. This avoids the current REVTeX 4.2 `Extra \or` failure
for `p{...}` table columns while preserving a wrapped, multipage table.

## Verified builds

Both entry points were compiled from this exact folder with MiKTeX 25.12 and
pdfLaTeX. `main.tex` completed the full pdfLaTeX--BibTeX--pdfLaTeX--pdfLaTeX
sequence and produced a 60-page PDF; `appendix-only.tex` produced a 10-page
PDF. The final logs contain no LaTeX errors, undefined references, undefined
citations, or overfull horizontal boxes. All appendix pages were also rendered
to images and visually checked.
