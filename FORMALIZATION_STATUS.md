# Formalization status

The repository contains a verified vertical formalization of the
characterization in Sections 4 and 5, including the original
semiring/channel realization. The terminal declarations and their exact
paper-facing signatures are present. The integrated warning-as-error build,
axiom audit, forbidden-token scan, and correspondence audit all pass.

The project is pinned to Lean 4.32.2 and Mathlib 4.32.2. Its integrated entry
point is [`CompleteCharacterization.lean`](CompleteCharacterization.lean),
whose imports transitively cover the complete declaration-bearing release
dependency tree.

## Status at a glance

| Artifact or target | Verified status |
|---|---|
| Endpoint-aware Rényi parameter, entropy, and line calculus | Strict root build passed |
| Signed-measure differentiation, compact-uniform DCT, and discretization | Strict root build passed |
| Exact two-block and three-block localization | Strict root build passed |
| `uniformShannonExpansion`, `shannonNeighbourhood`, and `shannonLogMass` | Strict root build passed |
| `shannonLocalization` | Exact four-limit declaration; strict root build passed |
| Temperate, tropical, and derivation necessity | Strict root build passed |
| `necessityBundle` | Exact four-part declaration; axiom audit passed |
| `mainClassification` | Assumption-free declaration; axiom audit passed |
| Original conditional semiring, channel order, and `embeddingLift` | Strict root build passed |
| `allConditionalEntropyAxioms` | Exact four-family declaration; axiom audit passed |
| 152-row, three-column manuscript correspondence ledger | Correspondence audit passed |
| Final `scripts/check.ps1` release audit | Passed on 24 August 2026 |

## Classification branch

The source tree formalizes:

1. the compactified parameter type `Param`, probability/finite/signed
   parameter measures, endpoint-aware Rényi entropy, and extended-real moment
   predicates;
2. positive-base real-power differentiation, the exact first and second
   entropy-line derivatives, the removable Shannon quotient, and continuity
   at the top endpoint;
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

The final declaration has no auxiliary theorem hypothesis. Unfolding
`Classifies` gives the four manuscript equivalences for finite nonzero
temperature, negative tropical, positive tropical, and derivation candidates.

## Semiring/channel and candidate-law branch

The parallel algebraic branch contains the finite conditional direct-sum and
tensor semiring, its quotient by relabeling/zero extension, concrete channel
composition, the generated quotient preorder, and `embeddingLift`. Candidate
normalization, nonnegativity, tensor additivity, and embedding invariance are
assembled with the four sufficiency branches in
`allConditionalEntropyAxioms`.

This theorem is separate from `mainClassification`: it verifies the original
five-law package for admissible candidates and does not serve as an assumed
premise of the classification.

## Correspondence and paper artifacts

[`paper/BLUEPRINT_STATEMENT_STATUS.md`](paper/BLUEPRINT_STATEMENT_STATUS.md)
contains exactly one source-ordered row for each of the 152 labeled manuscript
statements. Its columns are exactly **Manuscript statement**, **Lean
declaration**, and **Status**. Every row is marked **Formalized** or
**Formalized (split API)** and is covered by the strict root build.

The matching LaTeX table is
[`paper/blueprint-statement-correspondence.tex`](paper/blueprint-statement-correspondence.tex).
The dependency architecture is recorded in
[`paper/dependency-graph.dot`](paper/dependency-graph.dot),
[`DEPENDENCIES.md`](DEPENDENCIES.md), and
[`paper/DECLARATION_INDEX.md`](paper/DECLARATION_INDEX.md). The paper appendix
is [`paper/lean-formalization-appendix.tex`](paper/lean-formalization-appendix.tex).

## Trust boundary and release audit

The project trust boundary excludes `sorry`, `admit`,
project-defined `axiom`, and project-defined `opaque` declarations. Standard
logical dependencies reported by Lean or Mathlib, such as propositional
extensionality, classical choice, and quotient soundness, remain part of the
trusted foundation.

Run the complete Windows audit from the repository root:

```powershell
powershell -File scripts/check.ps1
```

The script performs the forbidden-token scan, builds
`CompleteCharacterization` with warnings treated as errors, runs
[`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean), and validates the exact
152-row correspondence invariant. All four steps pass on the audited release
state. The strict build checked 2,864 jobs; the 21 declarations in the axiom
audit depend exactly on `propext`, `Classical.choice`, and `Quot.sound`, with no
project-defined axiom.
