# Formalization status

The repository contains a verified vertical formalization of the parameter
classification in the complete-proof Sections 4--5 auxiliary paper,
including the original semiring/channel realization. The terminal declarations
and their paper-facing signatures are present, and the integrated
warning-as-error build, axiom audit, forbidden-token scan, and correspondence
audit pass on the current release state.

The paper hierarchy described here was revised on 30 August 2026. The canonical
manuscript is maintained on arXiv and is not duplicated in this repository.
GitHub hosts only the complete-proof and Lean auxiliary documents. The
complete-proof paper's statements 4.1--5.10 and natural-log convention are the
specification used by the Lean note and declaration correspondence. The public
facade in `ConditionalEntropy/FullDetailsStatements.lean` assigns one unique
Lean declaration to each of the seventeen numbered main-text environments.
Appendix A is tracked separately in the 32-row correspondence manifest so that
technical results are not silently conflated with the main classification
statements.

The project is pinned to Lean 4.32.2 and Mathlib 4.32.2. Its integrated entry
point is [`CompleteCharacterization.lean`](CompleteCharacterization.lean),
whose imports transitively cover the declaration-bearing dependency tree.

The verified terminal theorem classifies the four concrete candidate families.
It does not formalize the upstream universal representation theorem asserting
that every abstract conditional entropy has that candidate representation.
That scope boundary is explicit in the Lean auxiliary document.

## Status at a glance

| Artifact or target | Verified status |
|---|---|
| Endpoint-aware Rényi parameter, entropy, and line calculus | Strict root build passed |
| Signed-measure differentiation, compact-uniform DCT, and discretization | Strict root build passed |
| Exact two-block and three-block localization | Strict root build passed |
| `uniformShannonExpansion`, `shannonNeighbourhood`, and `shannonLogMass` | Strict root build passed |
| `shannonLocalization` | Exact four-limit declaration; strict root build passed |
| Temperate, tropical, and derivation necessity | Strict root build passed |
| Human-readable counterexample correspondence | Shannon, rounded block, tropical correction, binary-face, and derivation witnesses audited against Lean |
| `necessityBundle` | Exact four-part declaration; axiom audit passed |
| `mainClassification` | Assumption-free declaration; axiom audit passed |
| Original conditional semiring, channel order, and `embeddingLift` | Strict root build passed |
| `allConditionalEntropyAxioms` | Exact four-family declaration; axiom audit passed |
| Main-text 4.1--5.10 correspondence | One unique paper-facing facade per numbered environment; Proposition 5.10 is explicitly scoped to supplied representations |
| Full-details 32-row manifest | 32 unique canonical names: 31 exact rows and 1 explicit scope qualification (5.10) |
| Three-column internal-blueprint ledger | Structural correspondence audit passed |
| `scripts/check.ps1` | Passes on the current release state |

## Classification branch

The source tree formalizes:

1. the compactified parameter type `Param`, probability/finite/signed
   parameter measures, endpoint-aware Rényi entropy, and extended-real moment
   predicates;
2. positive-base real-power differentiation, the exact first and second
   entropy-line derivatives, the removable Shannon quotient, and continuity at
   the top endpoint;
3. signed differentiation through parameter integrals, compact-uniform
   dominated convergence, finite-support approximation, and discretization;
4. exact two-block and three-block logarithmic and G-kernel localization;
5. the dedicated Shannon escort estimates, rounded `C²` expansion,
   logarithmic-mass decay, near-order-one bounds, and four-limit Shannon
   localization;
6. positive and negative temperate necessity, positive and negative tropical
   necessity, and derivation necessity; and
7. `necessityBundle` and the closed natural-log theorem
   `mainClassification (tau : ProbabilityMeasure Param) : Classifies tau`.

The canonical manuscript and its auxiliary documents use the same finite witnesses. In
particular, negative tropical necessity records the three formal correction
directions, positive tropical necessity uses the binary pair `(1/3, 2/3)` and
`(1/2, 1/2)`, and derivation necessity uses the formalized upper-tail two-block
direction `(0, 1)`.

The final declaration has no auxiliary theorem hypothesis. Unfolding
`Classifies` gives the four equivalences for finite nonzero temperature,
negative tropical, positive tropical, and derivation candidates.

## Semiring/channel and candidate-law branch

The parallel algebraic branch contains the finite conditional direct-sum and
tensor semiring, its quotient by relabeling/zero extension, concrete channel
composition, the generated quotient preorder, and `embeddingLift`. Candidate
normalization, nonnegativity, tensor additivity, and embedding invariance are
assembled with the four sufficiency branches in
`allConditionalEntropyAxioms`.

This theorem is separate from `mainClassification`: it verifies the original
five-law package for admissible candidates and is not an assumed premise of the
classification.

## Paper hierarchy and correspondence

- The canonical manuscript, [*A Complete Characterisation of Conditional
  Entropies*](https://arxiv.org/abs/2601.23213), is maintained on arXiv. No
  main-manuscript copy or separate concise Sections 4--5 note is hosted here.
- [`paper/auxiliary-files/sections-4-5-full-details.tex`](paper/auxiliary-files/sections-4-5-full-details.tex)
  is the complete-proof auxiliary document. Its 4.1--5.10 numbering and
  natural-log convention determine the Lean correspondence.
- [`paper/auxiliary-files/lean-formalization-note.tex`](paper/auxiliary-files/lean-formalization-note.tex)
  is the Lean auxiliary document, with its theorem-facing proof map, trust audit,
  one-to-one main-text statement table, and separate Appendix audit.

[`paper/full-details-correspondence.json`](paper/full-details-correspondence.json)
is the single machine-readable inventory of all 32 numbered environments
(4.1--5.10 and A.1--A.15). Its companion checker reconstructs the numbering
from the LaTeX source, verifies the ordered labels and unique canonical names,
and asks Lean to elaborate every row marked exact or qualified.

[`paper/BLUEPRINT_STATEMENT_STATUS.md`](paper/BLUEPRINT_STATEMENT_STATUS.md)
contains one source-ordered row for every audited labeled internal-blueprint
statement. It retains the requested column headings **Manuscript statement**,
**Lean declaration**, and
**Status**. Each row is marked **Formalized** or **Formalized (split API)** and
is covered by the strict root build. The matching LaTeX table is
[`paper/blueprint-statement-correspondence.tex`](paper/blueprint-statement-correspondence.tex).

The detailed module-group implementation architecture is recorded in
[`paper/dependency-graph.dot`](paper/dependency-graph.dot), its
[`SVG`](paper/dependency-graph.svg) and [`PNG`](paper/dependency-graph.png)
renderings, [`DEPENDENCIES.md`](DEPENDENCIES.md), and
[`paper/DECLARATION_INDEX.md`](paper/DECLARATION_INDEX.md). This implementation
graph is distinct from the theorem-facing proof map in the Lean auxiliary document:
the first uses prerequisite-to-dependent arrows between module groups, while
the second uses result-to-ingredient arrows between complete-proof conclusions and
proof ingredients.

## Trust boundary and reproducibility

The project trust boundary excludes `sorry`, `admit`, project-defined `axiom`,
and project-defined `opaque` declarations. Standard logical dependencies
reported by Lean or Mathlib, such as propositional extensionality, classical
choice, and quotient soundness, remain part of the trusted foundation.

Run the complete Windows audit from the repository root:

```powershell
powershell -File scripts/check.ps1
```

The script performs the forbidden-token scan, builds
`CompleteCharacterization` with warnings treated as errors, runs
[`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean), and validates the
internal-blueprint and full-details correspondence invariants.
