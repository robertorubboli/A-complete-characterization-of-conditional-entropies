$ErrorActionPreference = 'Stop'

$repositoryRoot = Split-Path -Parent $PSScriptRoot
$blueprintPath = Join-Path $repositoryRoot 'paper\blueprint-sections-4-5.tex'
$markdownPath = Join-Path $repositoryRoot 'paper\BLUEPRINT_STATEMENT_STATUS.md'
$latexPath = Join-Path $repositoryRoot 'paper\blueprint-statement-correspondence.tex'

$blueprintLines = Get-Content -LiteralPath $blueprintPath
$start = (Select-String -LiteralPath $blueprintPath -SimpleMatch `
  '\section{Sufficient conditions for the parameters}' | Select-Object -First 1).LineNumber
$end = (Select-String -LiteralPath $blueprintPath -SimpleMatch `
  '\subsection{Lean module manifest}' | Select-Object -First 1).LineNumber

if (-not $start -or -not $end -or $start -ge $end) {
  throw 'Could not locate the blueprint statement range.'
}

$labels = [System.Collections.Generic.List[string]]::new()
$environmentPattern = '^\\begin\{(definition|lemma|proposition|corollary|theorem)\}'
$labelPattern = '\\label\{([^}]+)\}'

for ($lineIndex = $start - 1; $lineIndex -lt $end - 1; $lineIndex++) {
  if ($blueprintLines[$lineIndex] -notmatch $environmentPattern) { continue }
  $label = $null
  for ($lookahead = $lineIndex; $lookahead -le [Math]::Min($lineIndex + 3, $end - 2); $lookahead++) {
    $match = [regex]::Match($blueprintLines[$lookahead], $labelPattern)
    if ($match.Success) {
      $label = $match.Groups[1].Value
      break
    }
  }
  if (-not $label) {
    throw "Missing label for formal environment at blueprint line $($lineIndex + 1)."
  }
  $labels.Add($label)
}

$markdownLabels = [regex]::Matches(
  (Get-Content -LiteralPath $markdownPath -Raw),
  '(?m)^\| `([^`]+)` —') | ForEach-Object { $_.Groups[1].Value }
$latexText = Get-Content -LiteralPath $latexPath -Raw
$latexLabels = [regex]::Matches(
  $latexText,
  '\\BlueprintStatement\{([^}]+)\}') | ForEach-Object { $_.Groups[1].Value }
$latexRows = [regex]::Matches(
  $latexText,
  '(?s)\\BlueprintStatement\{[^}]+\}.*?&.*?&.*?\\\\')

if ($labels.Count -ne 152) { throw "Expected 152 blueprint labels, found $($labels.Count)." }
if ($markdownLabels.Count -ne 152) { throw "Expected 152 Markdown rows, found $($markdownLabels.Count)." }
if ($latexLabels.Count -ne 152) { throw "Expected 152 LaTeX rows, found $($latexLabels.Count)." }
if ($latexRows.Count -ne 152) { throw "Expected 152 three-column LaTeX rows, found $($latexRows.Count)." }

for ($index = 0; $index -lt $labels.Count; $index++) {
  if ($labels[$index] -ne $markdownLabels[$index]) {
    throw "Markdown label mismatch at row $($index + 1): expected '$($labels[$index])', found '$($markdownLabels[$index])'."
  }
  if ($labels[$index] -ne $latexLabels[$index]) {
    throw "LaTeX label mismatch at row $($index + 1): expected '$($labels[$index])', found '$($latexLabels[$index])'."
  }
}

Write-Output 'Correspondence audit passed: 152 source-ordered rows and three columns.'
