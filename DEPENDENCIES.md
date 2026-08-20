# Formalization dependency graph

![Condensed dependency graph](paper/dependency-graph.svg)

The graph is a readable condensation of the blueprint's acyclic module plan.
An arrow `A → B` means that blueprint layer `B` is planned to depend on layer
`A`; it does not imply that both Lean modules already exist. Blue nodes contain
one or more kernel-checked components, but `PARTIAL`
does not mean that every manuscript statement in the layer has been proved.
Orange nodes are specified in the blueprint and remain open Lean work.

| Layer | Contents | Current status |
|---|---|---|
| M1 | Finite carriers, cones, and channels | Partial |
| M2 | Compact parameters, measures, support, and moments | Open |
| M3 | Total endpoint-aware Rényi library | Open |
| M4 | Conditional candidates and shape reductions | Partial |
| M5 | Temperate sufficiency | Partial algebraic kernels |
| M6 | Tropical and derivation sufficiency | Open |
| M7 | Differentiation and signed integration | Partial stationarity kernels |
| M8 | Two- and three-block localization | Partial dominant-block bounds |
| M9 | Shannon-point localization | Open |
| M10 | Necessity branches | Partial scalar kernels |
| M11 | Classification and embedded-axiom lift | Open |

The editable source is [`paper/dependency-graph.dot`](paper/dependency-graph.dot).
Run `npm install` followed by `npm run render:graph` to regenerate the SVG and
PNG previews. The exact 152-row manuscript coverage ledger is
[`paper/BLUEPRINT_STATEMENT_STATUS.md`](paper/BLUEPRINT_STATEMENT_STATUS.md).
