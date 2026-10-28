#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"
config=${1:-comparator.json}
if [[ $# -gt 1 ]]; then
  echo "Usage: bash scripts/verify-comparator.sh [comparator.json]" >&2
  exit 2
fi
for required_command in bwrap lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required for the sandboxed Comparator" >&2
    exit 1
  fi
done

# Follow Palomar's template: register only the selected toolchain's bundled
# independent kernels, in an ephemeral copy outside the submitted project.
# Reference: https://github.com/PalomarRegistry/PalomarTemplate/blob/main/scripts/verify-comparator.sh
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker leanchecker-paranoid lean4lean nanoda_bin con-leche con-ron; do
  if [[ ! -x "$prefix/bin/$tool" ]]; then
    echo "error: the pinned toolchain does not bundle $tool" >&2
    exit 1
  fi
done
temporary_config=$(mktemp "${TMPDIR:-/tmp}/spectral-isometry-comparator.XXXXXX")
trap 'rm -f "$temporary_config"' EXIT
python3 - "$config" "$temporary_config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text(encoding="utf-8"))
if not isinstance(config, dict):
    raise SystemExit("Comparator configuration must be one JSON object")
if "external_kernels" in config:
    raise SystemExit("Do not put external_kernels in a submitted Comparator configuration")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [str(Path(prefix) / "bin" / "nanoda_bin")],
    "con-ron": [str(Path(prefix) / "bin" / "con-ron")],
}
Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY
lake comparator --config "$temporary_config" --paranoid
