#!/usr/bin/env bash
# Released under the MIT license. See LICENSE.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
verification_dir="${1:-.lake/verification}"
mkdir -p "$verification_dir"

{
  date -u '+UTC: %Y-%m-%dT%H:%M:%SZ'
  git rev-parse HEAD 2>/dev/null || true
  lake env lean --version
  cat lean-toolchain
  sha256sum lakefile.toml lake-manifest.json
} | tee "$verification_dir/environment.log"

# Record exactly which Lean sources were present at the start of the check.
find OnLeConjecture -name '*.lean' -type f -print0 \
  | sort -z \
  | xargs -0 sha256sum > "$verification_dir/sources.sha256"
sha256sum OnLeConjecture.lean AuditLeConjectureNative.lean \
  >> "$verification_dir/sources.sha256"

lake --wfail build 2>&1 | tee "$verification_dir/build.log"
lake env lean -DwarningAsError=true AuditLeConjectureNative.lean \
  2>&1 | tee "$verification_dir/audit.log"
sha256sum --check --status "$verification_dir/sources.sha256"
printf 'Build and final-theorem axiom audit passed. Logs: %s\n' "$verification_dir"
