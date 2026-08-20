#!/usr/bin/env bash
set -euo pipefail

if command -v rg >/dev/null 2>&1; then
  if rg -n '^\s*(axiom|opaque)\b|\b(sorry|admit)\b' \
      --glob '*.lean' --glob '!tmp/**' .; then
    echo 'Project-specific axiom, opaque declaration, sorry, or admit found.' >&2
    exit 1
  fi
else
  if grep -RInE --include='*.lean' --exclude-dir=tmp --exclude-dir=.lake --exclude-dir=.git \
      '(^[[:space:]]*(axiom|opaque)([[:space:]]|$))|(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' .; then
    echo 'Project-specific axiom, opaque declaration, sorry, or admit found.' >&2
    exit 1
  fi
fi

if [[ "${1:-}" != "--no-build" ]]; then
  lake build CompleteCharacterization --wfail
fi

lake env lean scripts/AxiomAudit.lean
pwsh -NoProfile -File scripts/check-correspondence.ps1
