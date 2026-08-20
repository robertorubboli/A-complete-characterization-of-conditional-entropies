# Formalization status

The repository is a **partial, kernel-checked formalization**, not yet a
complete Lean formalization of the characterization proved in the manuscript.
It is pinned to Lean 4.32.2 and Mathlib 4.32.2, and its current build entry
point is
[`CompleteCharacterization.lean`](CompleteCharacterization.lean).

## Status at a glance

| Artifact or target | Status |
|---|---|
| `CompleteCharacterization` build target | Checked |
| `ConditionalEntropy.verifiedKernelBundle` | Checked bundle of partial finite kernels |
| First four Section 4 cone lemmas | Proved and kernel checked |
| 152-row manuscript correspondence ledger | Complete as a coverage audit, not as a proof ledger |
| Condensed graph and declaration-level dependency index | Present |
| `necessityBundle` | Not declared |
| `mainClassification` | Not declared |
| `ConditionalEntropyAxioms` and `embeddingLift` | Not declared |
| `allConditionalEntropyAxioms` | Not declared |
| Full manuscript classification | Not formalized |

Leaving the genuine final names undeclared is intentional. Declaring a theorem
with additional localization, differentiability, or measure-theoretic
hypotheses would not meet the manuscript target. The existing intermediate
declarations expose their ordinary mathematical premises explicitly; those
premises are not project axioms, but the resulting implications are not a
replacement for the missing final theorems.

## What has been checked

The entry point collects proofs of finite components that are independently
useful in the eventual classification:

- a proof-carrying nonnegative cone, extension from its punctured part,
  punctured-cone convexity, and the concave/convex composition rules;
- reduction from concavity or convexity plus positive homogeneity to
  monotonicity or antitonicity under finite row-stochastic conditioning maps;
- the affine-monomial curvature identity, coefficient-sign consequences, and
  explicit stationary witnesses;
- scalar Shannon-atom, upper-tail, and lower-moment obstructions;
- exact finite-dimensional stationarity correction and its convergence;
- strict-midpoint criteria contradicting concavity, convexity, or
  quasi-convexity;
- dominant-block remainder bounds; and
- preservation of concavity, convexity, quasi-convexity, and strong
  quasi-concavity under pointwise limits.

[`BoundaryProofs/VerifiedKernelBundle.lean`](BoundaryProofs/VerifiedKernelBundle.lean)
packages the principal boundary implications as
`ConditionalEntropy.verifiedKernelBundle`. The declaration has no top-level
arguments, but its individual conjuncts universally quantify the data and
premises appropriate to each lemma. It certifies those kernels only.

[`ConditionalEntropy/MainTheorem.lean`](ConditionalEntropy/MainTheorem.lean)
contains assembled finite-profile implications such as
`positiveTemperate_necessary`, `negativeTemperate_exceptional_moment`,
`negativeTropical_exceptional_moment`, and `derivation_necessary`. Their
statements assume explicit coefficient, curvature, or sign premises because
the manuscript's analytic localization layer has not yet been translated.
Accordingly, their paper-facing names and comments do not make them complete
versions of the manuscript's necessity bundle.

## Partial kernel versus full manuscript theorem

The source of truth is the three-column table in
[`paper/BLUEPRINT_STATEMENT_STATUS.md`](paper/BLUEPRINT_STATEMENT_STATUS.md).
It has one row for each of the 152 labeled definitions, lemmas, propositions,
corollaries, and theorems in the supplied Sections 4--5 blueprint and final
assembly.

- **Partial algebraic kernel**: Lean checks a real subcalculation or implication
  used by the row, but the full conclusion of that manuscript statement is not
  available.
- **Proved and kernel checked**: the Lean declaration proves the blueprint
  row's full conclusion.
- **Not formalized**: no current declaration justifiably corresponds to the
  manuscript conclusion.
- A declaration named in a partial row must not be cited as a proof of the
  whole row.

The LaTeX version is
[`paper/blueprint-statement-correspondence.tex`](paper/blueprint-statement-correspondence.tex).
The condensed dependency graph is available as
[`SVG`](paper/dependency-graph.svg), [`PNG`](paper/dependency-graph.png), and
[`DOT`](paper/dependency-graph.dot); its colors report translation status, not
mathematical truth. Exact dependencies among checked declarations are listed
separately in [`paper/DECLARATION_INDEX.md`](paper/DECLARATION_INDEX.md).

## Why the full classification is still open in Lean

The remaining work is structural, not a single missing algebraic identity:

1. Define the compactified Rényi parameter, probability and signed measures,
   endpoint-aware Rényi entropy, and the manuscript's candidate functionals.
2. Formalize positive-base real-power calculus, power-mean curvature, and the
   first and second differentiated entropy formulas, including the removable
   Shannon singularity and endpoint limits.
3. Prove common push-forward discretization, dominated convergence, and twice
   differentiation under the signed parameter integral.
4. Construct the two-block, three-block, and Shannon families and prove the
   uniform localization limits that connect measure data to the checked finite
   curvature and midpoint kernels.
5. Formalize the original matrix semiring, arbitrary conditionally mixing
   channels, the embedded relation, and the final axiom-bundle lift.

Until those bridges are proved, the abstract moment/support profiles in
[`ConditionalEntropy/ParameterConditions.lean`](ConditionalEntropy/ParameterConditions.lean)
record only the finite data consumed by the checked kernels. They do not derive
that data from the manuscript's parameter measures. The open module layers and
their dependencies are catalogued in [`DEPENDENCIES.md`](DEPENDENCIES.md).

## Paper artifacts

- [`paper/lean-formalization-appendix.tex`](paper/lean-formalization-appendix.tex)
  contains the scope statement, dependency graph, and correspondence table.
- [`paper/main-with-lean-appendix.tex`](paper/main-with-lean-appendix.tex)
  includes that appendix in the main-paper wrapper.
- [`paper/lean-correspondence-standalone.tex`](paper/lean-correspondence-standalone.tex)
  wraps the appendix without the main paper's external bibliography files.
- [`paper/blueprint-sections-4-5.tex`](paper/blueprint-sections-4-5.tex) is the
  repository copy of the supplied self-contained blueprint around which the
  ledger is organized.

These documents describe both proved and open statements. Their inclusion is
not evidence that every displayed theorem has a Lean declaration.

## Trust and reproducibility

Run the full Windows check from the repository root:

```powershell
powershell -File scripts/check.ps1
```

The script scans `.lean` sources (excluding the scratch `tmp` directory),
builds `CompleteCharacterization` with `--wfail`, and runs
[`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean). The checked project source
contains no `sorry`, `admit`, project-defined `axiom`, or project-defined
`opaque` declaration. The audit may report standard logical infrastructure
from Lean or Mathlib, such as propositional extensionality, classical choice,
or quotient soundness; these are not axioms introduced by this project.
