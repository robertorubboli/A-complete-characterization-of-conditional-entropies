# Lean implementation dependency graph

The current release contains two complementary diagrams. They describe the
same formal development at different levels and are not alternative renderings
of one graph.

| Diagram | What it represents | Arrow convention | Source |
|---|---|---|---|
| **Lean implementation dependency graph (module-group view)** | The detailed source architecture. Each box groups concrete Lean modules. | Prerequisite to dependent: `A -> B` means declarations in `B` use declarations in `A`. | [`paper/dependency-graph.dot`](paper/dependency-graph.dot), rendered as [`SVG`](paper/dependency-graph.svg) and [`PNG`](paper/dependency-graph.png) |
| **Theorem-facing proof map (Lean auxiliary document)** | The two public conclusions, the complete-proof paper's numbered 4.x/5.x statements, and their reusable proof ingredients. | Result to ingredient, deliberately the reverse of the implementation graph. | [`paper/auxiliary-files/lean-formalization-note.tex`](paper/auxiliary-files/lean-formalization-note.tex), with a compiled [`PDF`](paper/auxiliary-files/pdf/lean-formalization-note.pdf) |

The editable source of the detailed implementation graph is
[`paper/dependency-graph.dot`](paper/dependency-graph.dot). It records the
current final vertical architecture, condensed from Lean imports and explicit
uses of project declarations. An arrow `A -> B` means that declarations in the
group `B` use the group `A`, directly or through the displayed condensation;
routine Mathlib dependencies and most intra-group edges are suppressed. Colors
identify technical subsystem families, not proof status or confidence: blue is
the foundation; cyan is semiring and channel algebra; teal is analysis and
shape reduction; green is sufficiency; purple is block localization; orange is
Shannon localization; rose/red is necessity and classification; and gray is
candidate-law assembly.
Gold boxes are the stable paper-facing facade modules used by the one-to-one
correspondence table.

The checked-in SVG and PNG previews are generated from the DOT source. After
editing the graph, run `npm install` and `npm run render:graph` to refresh both
previews. The proof map is maintained in the Lean-formalization auxiliary document;
changing the DOT graph does not regenerate or alter it.

## Vertical module groups

| Graph node | Lean modules | Role and representative declarations |
|---|---|---|
| Foundation | `FiniteData`, `ParamMeasure`, `Renyi`, `Moments` | Finite probability data, the endpoint-aware parameter type, finite/signed measures, support, and moments. |
| Semiring | `FiniteSemiring`, `FiniteSemiringQuotient` | Conditional direct-sum/tensor semiring and the quotient `CommSemiring` instance `conditionalSemiringCommSemiring`. |
| Channels and order | `FiniteChannels`, `FiniteChannelAlgebra`, `ConditionalSemiringOrder` | Channel composition, `CMRelCone`, the quotient preorder, concrete comparison, and `embeddingLift`. |
| Endpoint calculus and integration | `RenyiProperties`, `LineData`, `LineCalculus`, `EndpointLineCalculus`, `EndpointParameterContinuity`, `IntegratedEntropy`, `SignedWitnesses`, `SignedLineCalculus`, `CompactUniform`, `UniformSignedDCT` | Endpoint-aware Rényi formulas, real-power derivatives, signed differentiation under the integral, and compact-uniform passage. Key declarations include `exactEntropyDerivativeFormulas`, `exactDerivatives`, `signedLogPhiLineDerivativesOfIntegral`, and `uniformDCTSigned`. |
| Shape reductions | `ColumnFunctions`, `ShapeReduction`, `TropicalShapeReduction`, `ULiftInvariance` | Transports conditional monotonicity to the one-column concavity/convexity/quasiconvexity predicates used by necessity. |
| Sufficiency | `FiniteSupportSufficiency`, `GeneralSufficiency`, `Section4Sufficiency` | Finite-support proofs, discretization and closure, and the four final sufficient-condition branches. |
| Block localization | `BlockData`, `BlockEstimates`, `BlockCurves`, `BlockLimitPassage`, `BlockLocalization` | Dominant-block estimates and exact two-/three-block signed-integral limits, including `blockLimitPassage`, `twoBlockLimitIntegralEval`, and `threeBlockLimitIntegralEval`. |
| Localization interfaces | `BlockLocalizationInterfaces`, `LocalizationStationarity` | Exact paper-facing `twoBlockLocalization`, `threeBlockLocalization`, `blockLocalization`, kernel bridges, and `threeBlockGStationarityPackage`. |
| Shannon localization core | `ShannonData`, `ShannonAlgebra`, `ShannonCurves`, `ShannonAtoms`, `ShannonWitnessBridge`, `ShannonKernelRegularity`, `ShannonEscortCalculus`, `ShannonDominance`, `ShannonDedicatedEscort`, `ShannonLocalizationTargets`, `ShannonKernelBridges`, `ShannonKernelRegularityBridge`, `ShannonCurveKernelBridge` | Shannon block data, witness atoms, dedicated escort estimates, kernel regularity, curve bridge, and the four limit targets. |
| Shannon asymptotics | `ShannonLogMass`, `ShannonExpansion` | `shannonLogMass`, `uniformShannonExpansion`, and `shannonNeighbourhood`: the logarithmic-mass decay, rounded three-block expansion, and punctured-neighborhood control consumed by the final localization proof. |
| Shannon localization | `ShannonLocalization` | Final `shannonLocalization` interface: compact-uniform log-kernel and G-kernel convergence for derivative orders one and two. This named integration module is the interface imported by the positive, negative, and negative-tropical Shannon arguments. |
| Necessity measure algebra | `NullThresholds`, `NecessityMeasureAlgebra`, `NecessitySupportAlgebra`, `NecessityMomentPassage`, `NecessityExceptionalMeasureAlgebra`, `NegativeMomentPositivity` | Null-threshold selection, support isolation, truncated moments, monotone-convergence passage, and the exceptional upper atom package. |
| Temperate necessity | `PositiveTemperateNecessity`, `PositiveNecessity`, `NegativeTemperateNecessity`, `NegativeNecessity` | Positive and negative finite-measure arguments, Shannon atom cases, and transport to probability parameters. |
| Tropical necessity | `PositiveTropicalNecessity`, `NegativeTropicalShannonNecessity`, `NegativeTropicalNecessity` | The binary-face Dirac conclusion `positiveTropicalNecessity`; the Shannon obstruction `negativeTropicalUpperAtomZero`; the corrected stationary witnesses `twoUpperSupportPointsTropicalObstruction` and `tropicalTruncatedMoment_of_exceptional`; and the assembled negative conclusion `negativeTropicalNecessity`. |
| Derivation necessity | `DerivationNecessity` | The two-block second-derivative obstruction and support-below-one conclusion. |
| Necessity assembly | `NecessityBundle` | `necessityBundle`, combining all temperate, tropical, and derivation necessity branches. |
| Classification | `MainClassification` | `mainClassification`, combining `necessityBundle` with `Section4Sufficiency`. |
| Candidate law packages | `ConditionalEntropyAxioms`, `CandidateNormalization`, `JointTensorCandidates`, `CandidateEmbeddingInvariance` | Normalization, embedding invariance, tensor additivity, and conditional-monotonicity records for the four candidate families. |
| Full candidate-law assembly | `AllConditionalEntropyAxioms` | `allConditionalEntropyAxioms`, combining the candidate packages, sufficiency, and the original channel lift `embeddingLift`. |
| Paper-facing correspondence | `FullDetailsStatements` | Sixteen unique canonical facades `fullDetailsLemma4_1` through `fullDetailsProposition5_9`, one for each numbered main-text environment in the complete-proof document. |
| Appendix-facing correspondence | `FullDetailsAppendixStatements`, `FullDetailsAppendixA3A6`, `FullDetailsAppendixA11` | Fifteen unique exact canonical facades for A.1--A.15, including the entropy-specific Shannon cancellation theorem A.9. |

## Critical paths

The proof of classification follows the main vertical path

```text
endpoint calculus and signed integration
  → block localization
  → Shannon core, log-mass, and expansion
  → block/Shannon localization interfaces
  → temperate, tropical, and derivation necessity
  → necessityBundle
  → mainClassification.
```

The algebraic/channel realization follows the parallel path

```text
finite semiring and quotient
  → finite channels and conditional-semiring order
  → candidate normalization/tensor/embedding packages
  → allConditionalEntropyAxioms.
```

`mainClassification` and `allConditionalEntropyAxioms` are intentionally
separate terminal declarations: the former is the necessary-and-sufficient
parameter classification, while the latter verifies the original law package
for each admissible candidate and uses the semiring/channel lift.

For the internal-blueprint statement correspondence, see
[`paper/DECLARATION_INDEX.md`](paper/DECLARATION_INDEX.md) and the larger
[`paper/BLUEPRINT_STATEMENT_STATUS.md`](paper/BLUEPRINT_STATEMENT_STATUS.md).
The theorem-facing proof map and three-column correspondence table are in
[`paper/auxiliary-files/lean-formalization-note.tex`](paper/auxiliary-files/lean-formalization-note.tex).
The displayed 4.1--5.9 numbers belong to the complete-proof auxiliary
document, which also fixes the natural-log convention used throughout Lean.
The ordered 31-row source/declaration inventory, including Appendix A, is
[`paper/full-details-correspondence.json`](paper/full-details-correspondence.json);
its checker distinguishes the one-to-one public facade from the many-to-many
implementation graph described here.
Build and forbidden-token audit results are tracked separately; this document
describes dependencies and does not by itself assert compilation status.
