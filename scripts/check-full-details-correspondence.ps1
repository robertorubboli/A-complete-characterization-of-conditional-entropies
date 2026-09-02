param(
  [switch]$RequireAllExact
)

$ErrorActionPreference = 'Stop'

$repositoryRoot = Split-Path -Parent $PSScriptRoot
$manifestPath = Join-Path $repositoryRoot 'paper\full-details-correspondence.json'

if (-not (Test-Path -LiteralPath $manifestPath)) {
  throw "Missing full-details correspondence manifest: $manifestPath"
}

$manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
if ($manifest.schemaVersion -ne 1) {
  throw "Unsupported full-details correspondence schema version '$($manifest.schemaVersion)'."
}

$sourceRelativePath = [string]$manifest.source
if ([string]::IsNullOrWhiteSpace($sourceRelativePath)) {
  throw 'The manifest must name its full-details LaTeX source.'
}
$sourcePath = Join-Path $repositoryRoot ($sourceRelativePath -replace '/', '\')
if (-not (Test-Path -LiteralPath $sourcePath)) {
  throw "Missing full-details LaTeX source: $sourcePath"
}

# This independent list is deliberate.  The audit must fail if both the source
# and the manifest are accidentally changed in the same way.
$expectedNumbers = @(
  '4.1', '4.2', '4.3', '4.4', '4.5', '4.6', '4.7',
  '5.1', '5.2', '5.3', '5.4', '5.5', '5.6', '5.7', '5.8', '5.9', '5.10',
  'A.1', 'A.2', 'A.3', 'A.4', 'A.5', 'A.6', 'A.7', 'A.8', 'A.9',
  'A.10', 'A.11', 'A.12', 'A.13', 'A.14', 'A.15'
)
$expectedKinds = @(
  'lemma', 'lemma', 'lemma', 'proposition', 'proposition', 'proposition',
  'proposition', 'proposition', 'proposition', 'proposition', 'remark',
  'remark', 'proposition', 'proposition', 'proposition', 'proposition',
  'proposition', 'lemma', 'lemma', 'lemma', 'lemma', 'lemma', 'lemma',
  'lemma', 'lemma', 'lemma', 'lemma', 'proposition', 'lemma', 'lemma',
  'lemma', 'lemma'
)
$expectedLabels = @(
  'lem:power-mean-curvature',
  'lem:monomial-curvature',
  'lem:discrete-sufficient',
  'prop:general-sufficient',
  'prop:negative-tropical-sufficient',
  'prop:positive-tropical-sufficient',
  'prop:derivation-sufficient',
  'prop:positive-necessary',
  'prop:negative-atom-necessary',
  'prop:negative-truncated-moment',
  'rem:normalizing-witnesses',
  'rem:trace-preserving-witnesses',
  'prop:negative-single-point',
  'prop:negative-tropical-necessary',
  'prop:positive-tropical-necessary',
  'prop:derivation-necessary',
  'prop:derivation-classification',
  'lem:app-power-mean-hessian',
  'lem:app-monomial-hessian',
  'lem:app-renyi-continuity',
  'lem:app-renyi-shape',
  'lem:app-measure-tools',
  'lem:app-common-discretisation',
  'lem:app-pointwise-shape',
  'lem:app-ell-derivatives',
  'lem:app-Shannon-cancellation',
  'lem:app-endpoint-differentiability',
  'prop:app-fixed-d-interchange',
  'lem:app-dominant-block',
  'lem:app-Shannon-covariance',
  'lem:app-quasiconvex-stationary',
  'lem:app-exact-stationarity'
)
$expectedCanonicalDeclarations = @(
  'ConditionalEntropy.fullDetailsLemma4_1',
  'ConditionalEntropy.fullDetailsLemma4_2',
  'ConditionalEntropy.fullDetailsLemma4_3',
  'ConditionalEntropy.fullDetailsProposition4_4',
  'ConditionalEntropy.fullDetailsProposition4_5',
  'ConditionalEntropy.fullDetailsProposition4_6',
  'ConditionalEntropy.fullDetailsProposition4_7',
  'ConditionalEntropy.fullDetailsProposition5_1',
  'ConditionalEntropy.fullDetailsProposition5_2',
  'ConditionalEntropy.fullDetailsProposition5_3',
  'ConditionalEntropy.fullDetailsRemark5_4',
  'ConditionalEntropy.fullDetailsRemark5_5',
  'ConditionalEntropy.fullDetailsProposition5_6',
  'ConditionalEntropy.fullDetailsProposition5_7',
  'ConditionalEntropy.fullDetailsProposition5_8',
  'ConditionalEntropy.fullDetailsProposition5_9',
  'ConditionalEntropy.fullDetailsProposition5_10',
  'ConditionalEntropy.fullDetailsAppendixA_1',
  'ConditionalEntropy.fullDetailsAppendixA_2',
  'ConditionalEntropy.fullDetailsAppendixA_3',
  'ConditionalEntropy.fullDetailsAppendixA_4',
  'ConditionalEntropy.fullDetailsAppendixA_5',
  'ConditionalEntropy.fullDetailsAppendixA_6',
  'ConditionalEntropy.fullDetailsAppendixA_7',
  'ConditionalEntropy.fullDetailsAppendixA_8',
  'ConditionalEntropy.fullDetailsAppendixA_9',
  'ConditionalEntropy.fullDetailsAppendixA_10',
  'ConditionalEntropy.fullDetailsAppendixA_11',
  'ConditionalEntropy.fullDetailsAppendixA_12',
  'ConditionalEntropy.fullDetailsAppendixA_13',
  'ConditionalEntropy.fullDetailsAppendixA_14',
  'ConditionalEntropy.fullDetailsAppendixA_15'
)

$expectedCount = 32
if ($expectedNumbers.Count -ne $expectedCount -or
    $expectedKinds.Count -ne $expectedCount -or
    $expectedLabels.Count -ne $expectedCount -or
    $expectedCanonicalDeclarations.Count -ne $expectedCount) {
  throw 'Internal full-details audit specification does not contain 32 aligned rows.'
}

function Get-AppendixSectionName([int]$index) {
  if ($index -lt 1 -or $index -gt 26) {
    throw "Unsupported appendix section index $index."
  }
  return [string][char](64 + $index)
}

function Assert-UniqueValues($values, [string]$description) {
  $seen = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal)
  foreach ($rawValue in $values) {
    $value = [string]$rawValue
    if ([string]::IsNullOrWhiteSpace($value)) {
      throw "Empty $description value found."
    }
    if (-not $seen.Add($value)) {
      throw "Duplicate $description '$value'."
    }
  }
}

# Reconstruct theorem numbering from the actual LaTeX source.  The four theorem
# environments share one section-scoped counter in the document preamble.
$sourceLines = Get-Content -LiteralPath $sourcePath
$sourceRows = [System.Collections.Generic.List[object]]::new()
$numericSection = 0
$appendixMode = $false
$appendixSection = 0
$theoremCounter = 0
$currentSectionName = $null

for ($lineIndex = 0; $lineIndex -lt $sourceLines.Count; $lineIndex++) {
  $line = $sourceLines[$lineIndex]

  if ($line -match '^\s*\\setcounter\{section\}\{([0-9]+)\}') {
    $numericSection = [int]$Matches[1]
    continue
  }
  if ($line -match '^\s*\\appendix\s*$') {
    $appendixMode = $true
    $appendixSection = 0
    $theoremCounter = 0
    $currentSectionName = $null
    continue
  }
  if ($line -match '^\s*\\section\{') {
    $theoremCounter = 0
    if ($appendixMode) {
      $appendixSection++
      $currentSectionName = Get-AppendixSectionName $appendixSection
    } else {
      $numericSection++
      $currentSectionName = [string]$numericSection
    }
    continue
  }

  if ($line -notmatch '^\s*\\begin\{(theorem|lemma|proposition|remark)\}(?:\[[^]]*\])?') {
    continue
  }

  if ([string]::IsNullOrWhiteSpace($currentSectionName)) {
    throw "Formal environment outside a numbered section at source line $($lineIndex + 1)."
  }

  $kind = $Matches[1]
  $theoremCounter++
  $number = "$currentSectionName.$theoremCounter"
  $label = $null
  $foundClosing = $false
  $closingPattern = '^\s*\\end\{' + [regex]::Escape($kind) + '\}'

  for ($lookahead = $lineIndex + 1; $lookahead -lt $sourceLines.Count; $lookahead++) {
    $candidateLine = $sourceLines[$lookahead]
    if (-not $label -and $candidateLine -match '\\label\{([^}]+)\}') {
      $label = $Matches[1]
    }
    if ($candidateLine -match $closingPattern) {
      $foundClosing = $true
      break
    }
  }

  if (-not $foundClosing) {
    throw "Unclosed $kind $number beginning at source line $($lineIndex + 1)."
  }
  if ([string]::IsNullOrWhiteSpace($label)) {
    throw "Missing statement label for $kind $number at source line $($lineIndex + 1)."
  }

  $sourceRows.Add([pscustomobject]@{
    number = $number
    kind = $kind
    label = $label
    line = $lineIndex + 1
  })
}

if ($sourceRows.Count -ne $expectedCount) {
  throw "Expected 32 numbered full-details environments, found $($sourceRows.Count)."
}

$manifestRows = @($manifest.rows)
if ($manifestRows.Count -ne $expectedCount) {
  throw "Expected 32 manifest rows, found $($manifestRows.Count)."
}

Assert-UniqueValues ($sourceRows | ForEach-Object number) 'source statement number'
Assert-UniqueValues ($sourceRows | ForEach-Object label) 'source statement label'
Assert-UniqueValues ($manifestRows | ForEach-Object number) 'manifest statement number'
Assert-UniqueValues ($manifestRows | ForEach-Object label) 'manifest statement label'
Assert-UniqueValues ($manifestRows | ForEach-Object canonicalDeclaration) `
  'canonical Lean declaration'

$allowedCoverage = @('exact', 'qualified', 'gap')
for ($index = 0; $index -lt $expectedCount; $index++) {
  $sourceRow = $sourceRows[$index]
  $manifestRow = $manifestRows[$index]

  if ($sourceRow.number -ne $expectedNumbers[$index] -or
      $sourceRow.kind -ne $expectedKinds[$index] -or
      $sourceRow.label -ne $expectedLabels[$index]) {
    throw "Full-details source mismatch at row $($index + 1): expected " +
      "$($expectedKinds[$index]) $($expectedNumbers[$index]) " +
      "'$($expectedLabels[$index])', found $($sourceRow.kind) " +
      "$($sourceRow.number) '$($sourceRow.label)' (line $($sourceRow.line))."
  }

  if ([string]$manifestRow.number -ne $expectedNumbers[$index] -or
      [string]$manifestRow.kind -ne $expectedKinds[$index] -or
      [string]$manifestRow.label -ne $expectedLabels[$index]) {
    throw "Manifest mismatch at row $($index + 1): expected " +
      "$($expectedKinds[$index]) $($expectedNumbers[$index]) " +
      "'$($expectedLabels[$index])'."
  }

  if ([string]$manifestRow.canonicalDeclaration -ne
      $expectedCanonicalDeclarations[$index]) {
    throw "Canonical declaration mismatch at row $($index + 1): expected " +
      "'$($expectedCanonicalDeclarations[$index])', found " +
      "'$($manifestRow.canonicalDeclaration)'."
  }

  $coverage = [string]$manifestRow.coverage
  if ($allowedCoverage -notcontains $coverage) {
    throw "Invalid coverage '$coverage' for statement $($manifestRow.number); " +
      "expected 'exact', 'qualified', or 'gap'."
  }
  if ($coverage -ne 'exact' -and
      [string]::IsNullOrWhiteSpace([string]$manifestRow.statusDetail)) {
    throw "Non-exact row $($manifestRow.number) must explain its scope or gap."
  }
}

# Keep both human-facing three-column tables synchronized with the
# machine-readable manifest.  Prose references and supporting declarations are
# intentionally ignored.
$leanNotePath = Join-Path $repositoryRoot `
  'paper\auxiliary-files\lean-formalization-note.tex'
if (-not (Test-Path -LiteralPath $leanNotePath)) {
  throw "Missing Lean-formalization note: $leanNotePath"
}
$leanNote = Get-Content -LiteralPath $leanNotePath -Raw
$tableRowMatches = [regex]::Matches(
  $leanNote,
  '\\StatementCell\{(?<statement>(?:Lemma|Proposition|Remark)~.*?)\}\s*&\s*' +
    '\\LeanCell\{\s*\\LeanDecl\{(?<name>fullDetails[A-Za-z0-9_]+)\}\s*\}\s*&\s*' +
    '\\StatusCell\{(?<status>.*?)\}\\\\',
  [System.Text.RegularExpressions.RegexOptions]::Singleline
)
if ($tableRowMatches.Count -ne $expectedCount) {
  throw "Expected 32 complete correspondence rows in the Lean note, found " +
    "$($tableRowMatches.Count)."
}
for ($index = 0; $index -lt $expectedCount; $index++) {
  $statement = $tableRowMatches[$index].Groups['statement'].Value.Trim()
  if ($statement -notmatch '^(Lemma|Proposition|Remark)~((?:[45]|A)\.[0-9]+):') {
    throw "Cannot parse the Lean-note manuscript cell at row $($index + 1): '$statement'."
  }
  $actualKind = $Matches[1].ToLowerInvariant()
  $actualNumber = $Matches[2]
  if ($actualKind -ne $expectedKinds[$index] -or
      $actualNumber -ne $expectedNumbers[$index]) {
    throw "Lean-note manuscript-cell mismatch at row $($index + 1): expected " +
      "$($expectedKinds[$index]) $($expectedNumbers[$index]), found " +
      "$actualKind $actualNumber."
  }

  $actual = 'ConditionalEntropy.' +
    $tableRowMatches[$index].Groups['name'].Value
  if ($actual -ne $expectedCanonicalDeclarations[$index]) {
    throw "Lean-note table mismatch at row $($index + 1): expected " +
      "'$($expectedCanonicalDeclarations[$index])', found '$actual'."
  }

  $status = $tableRowMatches[$index].Groups['status'].Value.Trim()
  $coverage = [string]$manifestRows[$index].coverage
  $expectedStatusPrefix = switch ($coverage) {
    'exact' { 'Exact' }
    'qualified' { 'Qualified' }
    'gap' { 'Gap' }
  }
  if (-not $status.StartsWith($expectedStatusPrefix,
      [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "Lean-note status mismatch at row $($index + 1): manifest coverage " +
      "is '$coverage', but the visible cell is '$status'."
  }
}

$markdownTablePath = Join-Path $repositoryRoot 'paper\FULL_DETAILS_CORRESPONDENCE.md'
if (-not (Test-Path -LiteralPath $markdownTablePath)) {
  throw "Missing Markdown full-details table: $markdownTablePath"
}
$markdownRows = [System.Collections.Generic.List[object]]::new()
foreach ($line in Get-Content -LiteralPath $markdownTablePath) {
  if ($line -match '^\|\s*(Lemma|Proposition|Remark)\s+((?:[45]|A)\.[0-9]+)\s+[^|]*\|\s*`([^`]+)`\s*\|\s*([^|]+)\|') {
    $markdownRows.Add([pscustomobject]@{
      kind = $Matches[1].ToLowerInvariant()
      number = $Matches[2]
      declaration = $Matches[3]
      status = $Matches[4].Trim()
    })
  }
}
if ($markdownRows.Count -ne $expectedCount) {
  throw "Expected 32 rows in the Markdown correspondence table, found " +
    "$($markdownRows.Count)."
}
for ($index = 0; $index -lt $expectedCount; $index++) {
  $row = $markdownRows[$index]
  if ($row.kind -ne $expectedKinds[$index] -or
      $row.number -ne $expectedNumbers[$index] -or
      $row.declaration -ne $expectedCanonicalDeclarations[$index]) {
    throw "Markdown correspondence mismatch at row $($index + 1)."
  }
  $coverage = [string]$manifestRows[$index].coverage
  $expectedStatusPrefix = switch ($coverage) {
    'exact' { 'Exact' }
    'qualified' { 'Qualified' }
    'gap' { 'Gap' }
  }
  if (-not $row.status.StartsWith($expectedStatusPrefix,
      [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "Markdown status mismatch at row $($index + 1): manifest coverage " +
      "is '$coverage', but the visible cell is '$($row.status)'."
  }
}

# An exact row is not accepted merely because its name appears in JSON.  Lean
# must resolve and elaborate every canonical declaration through the checked
# repository entry point.  Qualified rows must also elaborate, but do not
# certify the entire prose statement.  Gap rows are deliberately omitted from
# this file: they are recorded, but not certified as existing.
$exactRows = @($manifestRows | Where-Object coverage -eq 'exact')
$qualifiedRows = @($manifestRows | Where-Object coverage -eq 'qualified')
$gapRows = @($manifestRows | Where-Object coverage -eq 'gap')
$elaboratedRows = @($exactRows) + @($qualifiedRows)

if ($elaboratedRows.Count -gt 0) {
  $auditPath = Join-Path ([System.IO.Path]::GetTempPath()) `
    ("full-details-correspondence-{0}.lean" -f [guid]::NewGuid().ToString('N'))
  $auditLines = [System.Collections.Generic.List[string]]::new()
  $auditLines.Add('import CompleteCharacterization')
  $auditLines.Add('')
  foreach ($row in $elaboratedRows) {
    $auditLines.Add("#check $($row.canonicalDeclaration)")
  }

  try {
    [System.IO.File]::WriteAllLines($auditPath, $auditLines)
    Push-Location $repositoryRoot
    try {
      $leanOutput = & lake env lean $auditPath 2>&1
      $leanExitCode = $LASTEXITCODE
    } finally {
      Pop-Location
    }
    if ($leanExitCode -ne 0) {
      $leanOutput | ForEach-Object { Write-Output $_ }
      throw 'One or more exact canonical Lean declarations do not elaborate.'
    }
  } finally {
    if (Test-Path -LiteralPath $auditPath) {
      Remove-Item -LiteralPath $auditPath -Force
    }
  }
}

Write-Output ("Full-details structural correspondence audit passed: " +
  "$expectedCount ordered, uniquely labelled rows.")
Write-Output ("Exact canonical rows elaborated by Lean: $($exactRows.Count).")
Write-Output ("Qualified canonical rows elaborated by Lean: $($qualifiedRows.Count).")

if ($qualifiedRows.Count -gt 0) {
  Write-Output ('Qualified rows (the listed declaration exists, but the full ' +
    'prose statement has an explicit scope boundary):')
  foreach ($row in $qualifiedRows) {
    Write-Output ("  $($row.number) [$($row.label)] -> " +
      "$($row.canonicalDeclaration): $($row.statusDetail)")
  }
}

if ($gapRows.Count -gt 0) {
  Write-Output ("Audited correspondence gaps without an exact certificate: " +
    "$($gapRows.Count).")
  foreach ($row in $gapRows) {
    Write-Output ("  $($row.number) [$($row.label)] -> " +
      "$($row.canonicalDeclaration): $($row.statusDetail)")
  }
}

$nonExactCount = $qualifiedRows.Count + $gapRows.Count
if ($RequireAllExact -and $nonExactCount -gt 0) {
  throw "Full-details correspondence has $nonExactCount non-exact row(s)."
}

if ($nonExactCount -eq 0) {
  Write-Output ('Machine one-to-one certificate passed: all 32 canonical rows ' +
    'are marked exact and elaborate. Semantic equivalence is established by ' +
    'the recorded manual statement review, not inferred from LaTeX by this script.')
} else {
  Write-Output ("This is not a 32-row exactness certificate: $nonExactCount " +
    'row(s) have a recorded qualification or gap.')
}
