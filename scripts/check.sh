#!/usr/bin/env bash
set -euo pipefail

if rg -n '^\s*(axiom|opaque)\b|\b(sorry|admit)\b' \
    --glob '*.lean' --glob '!tmp/**' .; then
  echo 'Project-specific axiom, opaque declaration, sorry, or admit found.' >&2
  exit 1
fi

if [[ "${1:-}" != "--no-build" ]]; then
  lake build ConditionalEntropy BoundaryProofs --wfail
fi

lake env lean scripts/AxiomAudit.lean
