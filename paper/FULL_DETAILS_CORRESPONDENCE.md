# Full-details paper ↔ Lean correspondence

This is the reader-facing one-to-one index for
[`sections-4-5-full-details.tex`](auxiliary-files/sections-4-5-full-details.tex).
Each of its 31 numbered environments has one distinct canonical Lean
declaration, and each declaration in the table is used for only that
environment. The canonical declarations are stable facades: their proofs may
call several lower-level implementation lemmas, so the underlying dependency
graph remains many-to-many.

“Exact” means that the facade directly packages the formal content of the
numbered result. All thirty-one rows are exact. Lemma A.9 directly packages
the entropy-line continuity and the exact
Shannon-point pole-cancellation formula for derivative orders zero, one, and
two.

The machine-readable source of this table is
[`full-details-correspondence.json`](full-details-correspondence.json), and
[`check-full-details-correspondence.ps1`](../scripts/check-full-details-correspondence.ps1)
checks the LaTeX numbering, labels, order, unique names, the ordered canonical
declaration cells in the LaTeX counterpart, and Lean elaboration. The prose in
this Markdown rendering remains reader-facing documentation.

| Manuscript statement | Lean declaration | Status |
|---|---|---|
| Lemma 4.1 — Power-mean curvature | `ConditionalEntropy.fullDetailsLemma4_1` | Exact |
| Lemma 4.2 — Monomial curvature | `ConditionalEntropy.fullDetailsLemma4_2` | Exact |
| Lemma 4.3 — Finite-support sufficiency | `ConditionalEntropy.fullDetailsLemma4_3` | Exact |
| Proposition 4.4 — General temperate sufficiency | `ConditionalEntropy.fullDetailsProposition4_4` | Exact |
| Proposition 4.5 — Negative-tropical sufficiency | `ConditionalEntropy.fullDetailsProposition4_5` | Exact |
| Proposition 4.6 — Positive-tropical sufficiency | `ConditionalEntropy.fullDetailsProposition4_6` | Exact |
| Proposition 4.7 — Derivation sufficiency | `ConditionalEntropy.fullDetailsProposition4_7` | Exact |
| Proposition 5.1 — Positive necessity | `ConditionalEntropy.fullDetailsProposition5_1` | Exact |
| Proposition 5.2 — Negative Shannon atom excludes upper support | `ConditionalEntropy.fullDetailsProposition5_2` | Exact |
| Proposition 5.3 — Truncated exceptional-moment bound | `ConditionalEntropy.fullDetailsProposition5_3` | Exact |
| Remark 5.4 — Unnormalised cone witnesses and homogeneity | `ConditionalEntropy.fullDetailsRemark5_4` | Exact |
| Remark 5.5 — Compensated two-column witness | `ConditionalEntropy.fullDetailsRemark5_5` | Exact |
| Proposition 5.6 — Exceptional negative branch: unique upper point, finite one-sided moments, and moment bound | `ConditionalEntropy.fullDetailsProposition5_6` | Exact |
| Proposition 5.7 — Negative-tropical necessity | `ConditionalEntropy.fullDetailsProposition5_7` | Exact |
| Proposition 5.8 — Positive-tropical necessity | `ConditionalEntropy.fullDetailsProposition5_8` | Exact |
| Proposition 5.9 — Derivation necessity | `ConditionalEntropy.fullDetailsProposition5_9` | Exact |
| Lemma A.1 — Hessian of the power mean | `ConditionalEntropy.fullDetailsAppendixA_1` | Exact |
| Lemma A.2 — Hessian and sign classification of a monomial | `ConditionalEntropy.fullDetailsAppendixA_2` | Exact |
| Lemma A.3 — Continuity and uniform bound for finite-dimensional Rényi entropy | `ConditionalEntropy.fullDetailsAppendixA_3` | Exact |
| Lemma A.4 — Concavity and Schur concavity in the sufficient-condition ranges | `ConditionalEntropy.fullDetailsAppendixA_4` | Exact |
| Lemma A.5 — Measure-theoretic tools | `ConditionalEntropy.fullDetailsAppendixA_5` | Exact |
| Lemma A.6 — Common discrete approximation of the Rényi parameter | `ConditionalEntropy.fullDetailsAppendixA_6` | Exact |
| Lemma A.7 — Pointwise limits preserve the shape inequalities | `ConditionalEntropy.fullDetailsAppendixA_7` | Exact |
| Lemma A.8 — First and second derivatives of the logarithmic power mean | `ConditionalEntropy.fullDetailsAppendixA_8` | Exact |
| Lemma A.9 — Cancellation and continuity through the Shannon point | `ConditionalEntropy.fullDetailsAppendixA_9` | Exact |
| Lemma A.10 — Continuity of the differentiated entropy at the parameter endpoints | `ConditionalEntropy.fullDetailsAppendixA_10` | Exact |
| Proposition A.11 — Differentiation under the Rényi-parameter integral at fixed dimension | `ConditionalEntropy.fullDetailsAppendixA_11` | Exact |
| Lemma A.12 — Dominant-block remainder | `ConditionalEntropy.fullDetailsAppendixA_12` | Exact |
| Lemma A.13 — First two derivatives of Shannon entropy along an affine path | `ConditionalEntropy.fullDetailsAppendixA_13` | Exact |
| Lemma A.14 — Second-order condition for a one-dimensional quasi-convex function | `ConditionalEntropy.fullDetailsAppendixA_14` | Exact |
| Lemma A.15 — Exact finite-dimensional stationarity correction | `ConditionalEntropy.fullDetailsAppendixA_15` | Exact |

The facade implementations are split by topic across
[`FullDetailsStatements.lean`](../ConditionalEntropy/FullDetailsStatements.lean),
[`FullDetailsAppendixStatements.lean`](../ConditionalEntropy/FullDetailsAppendixStatements.lean),
[`FullDetailsAppendixA3A6.lean`](../ConditionalEntropy/FullDetailsAppendixA3A6.lean),
and
[`FullDetailsAppendixA11.lean`](../ConditionalEntropy/FullDetailsAppendixA11.lean).
