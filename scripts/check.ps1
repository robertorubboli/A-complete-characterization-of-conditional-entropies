$ErrorActionPreference = 'Stop'

$matches = rg -n '^\s*(axiom|opaque)\b|\b(sorry|admit)\b' --glob '*.lean' --glob '!tmp/**' .
if ($LASTEXITCODE -eq 0) {
  $matches
  throw 'Project-specific axiom, opaque declaration, sorry, or admit found.'
}
if ($LASTEXITCODE -ne 1) {
  throw 'Source audit failed.'
}

& lake build CompleteCharacterization --wfail
if ($LASTEXITCODE -ne 0) { throw 'Lean build failed.' }

& lake env lean scripts/AxiomAudit.lean
if ($LASTEXITCODE -ne 0) { throw 'Kernel axiom audit failed.' }

& powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check-correspondence.ps1
if ($LASTEXITCODE -ne 0) { throw 'Statement correspondence audit failed.' }
