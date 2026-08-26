# Formalization status

The repository contains a verified vertical formalization of the parameter
classification in Sections 4 and 5 of the canonical journal manuscript,
including the original semiring/channel realization. The terminal declarations
and their paper-facing signatures are present, and the integrated
warning-as-error build, axiom audit, forbidden-token scan, and correspondence
audit pass on the current release state.

The paper hierarchy described here was revised on 26 August 2026. Statement
numbers in the complete-proof and Lean supplements now refer to the canonical
manuscript's Sections 4 and 5; the Lean correspondence runs through statement
5.10.

The project is pinned to Lean 4.32.2 and Mathlib 4.32.2. Its integrated entry
point is [`CompleteCharacterization.lean`](CompleteCharacterization.lean),
whose imports transitively cover the declaration-bearing dependency tree.

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
| Three-column manuscript correspondence ledger | Correspondence audit passed |
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
7. `necessityBundle` and the closed theorem
   `mainClassification (tau : ProbabilityMeasure Param) : Classifies tau`.

The journal manuscript and its supplements use the same finite witnesses. In
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

- [`paper/three-document-release/main-paper.tex`](paper/three-document-release/main-paper.tex)
  is the canonical 46-page journal manuscript. Its Sections 4 and 5 are part
  of the paper and determine the statement numbering.
- [`paper/three-document-release/sections-4-5-full-details.tex`](paper/three-document-release/sections-4-5-full-details.tex)
  is the complete proof supplement and mirrors the manuscript's 4.x/5.x
  numbering.
- [`paper/three-document-release/lean-formalization-note.tex`](paper/three-document-release/lean-formalization-note.tex)
  is the Lean supplement, with its theorem-facing proof map, trust audit, and
  statement table through 5.10.

[`paper/BLUEPRINT_STATEMENT_STATUS.md`](paper/BLUEPRINT_STATEMENT_STATUS.md)
contains one source-ordered row for every audited labeled manuscript statement.
Its columns are exactly **Manuscript statement**, **Lean declaration**, and
**Status**. Each row is marked **Formalized** or **Formalized (split API)** and
is covered by the strict root build. The matching LaTeX table is
[`paper/blueprint-statement-correspondence.tex`](paper/blueprint-statement-correspondence.tex).

The detailed module-group implementation architecture is recorded in
[`paper/dependency-graph.dot`](paper/dependency-graph.dot), its
[`SVG`](paper/dependency-graph.svg) and [`PNG`](paper/dependency-graph.png)
renderings, [`DEPENDENCIES.md`](DEPENDENCIES.md), and
[`paper/DECLARATION_INDEX.md`](paper/DECLARATION_INDEX.md). This implementation
graph is distinct from the theorem-facing proof map in the Lean supplement:
the first uses prerequisite-to-dependent arrows between module groups, while
the second uses result-to-ingredient arrows between manuscript conclusions and
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
three-column correspondence invariant.
