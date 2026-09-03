# Full-details paper ↔ Lean correspondence

This is the reader-facing one-to-one index for
[`sections-4-5-full-details.tex`](auxiliary-files/sections-4-5-full-details.tex).
Each of its 31 numbered environments has one distinct canonical Lean
declaration, and each declaration in the table is used for only that
environment. The canonical declarations are stable facades: their proofs may
call several lower-level implementation lemmas, so the underlying dependency
graph remains many-to-many.

“Exact” means that the facade directly packages the formal content of the
numbered result. Every remaining row is exact. Lemma A.9 directly packages
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
| Lemma 4.1 — power-mean curvature | `ConditionalEntropy.fullDetailsLemma4_1` | Exact |
| Lemma 4.2 — monomial curvature | `ConditionalEntropy.fullDetailsLemma4_2` | Exact |
| Lemma 4.3 — finite-support sufficiency | `ConditionalEntropy.fullDetailsLemma4_3` | Exact |
| Proposition 4.4 — general temperate sufficiency | `ConditionalEntropy.fullDetailsProposition4_4` | Exact |
| Proposition 4.5 — negative-tropical sufficiency | `ConditionalEntropy.fullDetailsProposition4_5` | Exact |
| Proposition 4.6 — positive-tropical sufficiency | `ConditionalEntropy.fullDetailsProposition4_6` | Exact |
| Proposition 4.7 — derivation sufficiency | `ConditionalEntropy.fullDetailsProposition4_7` | Exact |
| Proposition 5.1 — positive necessity | `ConditionalEntropy.fullDetailsProposition5_1` | Exact |
| Proposition 5.2 — negative Shannon-atom obstruction | `ConditionalEntropy.fullDetailsProposition5_2` | Exact |
| Proposition 5.3 — truncated exceptional-moment bound | `ConditionalEntropy.fullDetailsProposition5_3` | Exact |
| Remark 5.4 — homogeneity and channel lift | `ConditionalEntropy.fullDetailsRemark5_4` | Exact formal content |
| Remark 5.5 — compensated two-column witness | `ConditionalEntropy.fullDetailsRemark5_5` | Exact formal content |
| Proposition 5.6 — complete exceptional negative branch | `ConditionalEntropy.fullDetailsProposition5_6` | Exact |
| Proposition 5.7 — negative-tropical necessity | `ConditionalEntropy.fullDetailsProposition5_7` | Exact |
| Proposition 5.8 — positive-tropical necessity | `ConditionalEntropy.fullDetailsProposition5_8` | Exact |
| Proposition 5.9 — derivation necessity | `ConditionalEntropy.fullDetailsProposition5_9` | Exact |
| Lemma A.1 — Hessian of the power mean | `ConditionalEntropy.fullDetailsAppendixA_1` | Exact |
| Lemma A.2 — Hessian and sign classification of a monomial | `ConditionalEntropy.fullDetailsAppendixA_2` | Exact |
| Lemma A.3 — Rényi continuity and support bound | `ConditionalEntropy.fullDetailsAppendixA_3` | Exact |
| Lemma A.4 — concavity and Schur concavity | `ConditionalEntropy.fullDetailsAppendixA_4` | Exact |
| Lemma A.5 — measure-theoretic tools | `ConditionalEntropy.fullDetailsAppendixA_5` | Exact |
| Lemma A.6 — common discrete approximation | `ConditionalEntropy.fullDetailsAppendixA_6` | Exact |
| Lemma A.7 — pointwise preservation of shape | `ConditionalEntropy.fullDetailsAppendixA_7` | Exact |
| Lemma A.8 — logarithmic power-mean derivatives | `ConditionalEntropy.fullDetailsAppendixA_8` | Exact |
| Lemma A.9 — cancellation through the Shannon point | `ConditionalEntropy.fullDetailsAppendixA_9` | Exact |
| Lemma A.10 — endpoint differentiability | `ConditionalEntropy.fullDetailsAppendixA_10` | Exact |
| Proposition A.11 — differentiation under the parameter integral | `ConditionalEntropy.fullDetailsAppendixA_11` | Exact |
| Lemma A.12 — dominant-block remainder | `ConditionalEntropy.fullDetailsAppendixA_12` | Exact |
| Lemma A.13 — Shannon derivatives in covariance form | `ConditionalEntropy.fullDetailsAppendixA_13` | Exact |
| Lemma A.14 — quasiconvex stationary second-order condition | `ConditionalEntropy.fullDetailsAppendixA_14` | Exact |
| Lemma A.15 — exact finite-dimensional stationarity correction | `ConditionalEntropy.fullDetailsAppendixA_15` | Exact |

The facade implementations are split by topic across
[`FullDetailsStatements.lean`](../ConditionalEntropy/FullDetailsStatements.lean),
[`FullDetailsAppendixStatements.lean`](../ConditionalEntropy/FullDetailsAppendixStatements.lean),
[`FullDetailsAppendixA3A6.lean`](../ConditionalEntropy/FullDetailsAppendixA3A6.lean),
and
[`FullDetailsAppendixA11.lean`](../ConditionalEntropy/FullDetailsAppendixA11.lean).
