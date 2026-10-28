#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"
components=false
case "${1:-}" in
  "") ;;
  --components) components=true ;;
  --help|-h)
    echo "Usage: bash scripts/verify.sh [--components]"
    echo "Default: the three principal statements. --components: all 68 statements, including the three principal results."
    exit 0 ;;
  *) echo "Usage: bash scripts/verify.sh [--components]" >&2; exit 2 ;;
esac
if [[ $# -gt 1 ]]; then
  echo "Usage: bash scripts/verify.sh [--components]" >&2
  exit 2
fi

unset LEAN_PATH LEAN_SRC_PATH
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
validation_args=()
config=comparator.json
label=comparator
if "$components"; then
  validation_args+=(--components)
  config=comparator-components.json
  label=comparator-components
fi
log_dir=verification-output
mkdir -p "$log_dir"
python3 scripts/check_project.py "${validation_args[@]}" 2>&1 | tee "$log_dir/project.log"
lake --version 2>&1 | tee "$log_dir/versions.log"
lake env lean --version 2>&1 | tee -a "$log_dir/versions.log"
lake exe cache get 2>&1 | tee "$log_dir/cache.log"
lake build 2>&1 | tee "$log_dir/build.log"
lake env lean AxiomReport.lean 2>&1 | tee "$log_dir/axioms.log"
python3 scripts/check_axioms.py "$log_dir/axioms.log" --json "$log_dir/axioms.json"
bash scripts/verify-comparator.sh "$config" 2>&1 | tee "$log_dir/$label.log"
for checker in 'Lean paranoid' lean4lean nanoda con-leche con-ron 'Lean default'; do
  if ! grep -Fq "$checker kernel accepts the solution" "$log_dir/$label.log"; then
    echo "error: missing Comparator acceptance for $checker" >&2
    exit 1
  fi
done
if ! grep -Fq 'Your solution is okay!' "$log_dir/$label.log"; then
  echo "error: Comparator did not report successful statement/proof comparison" >&2
  exit 1
fi
echo "Build, axiom reports and all six sandboxed Comparator checks passed."
