#!/usr/bin/env python3
"""Validate the actual output of `lake env lean AxiomReport.lean`."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
HEADER = re.compile(
    r"^.*?'(?P<name>[^\r\n]+)' depends on axioms:\s*\[(?P<axioms>[^\]]*)\]", re.M
)
EMPTY = re.compile(r"^.*?'(?P<name>[^\r\n]+)' does not depend on any axioms\s*$", re.M)


def reports(text: str) -> dict[str, list[str]]:
    result = {}
    for match in list(HEADER.finditer(text)) + list(EMPTY.finditer(text)):
        name = match.group("name")
        if name in result:
            raise ValueError(f"Duplicate axiom report for {name}")
        entries = match.groupdict().get("axioms") or ""
        axioms = {entry.strip() for entry in entries.split(",") if entry.strip()}
        if not axioms <= ALLOWED:
            raise ValueError(f"{name}: unpermitted axioms: {', '.join(sorted(axioms - ALLOWED))}")
        result[name] = sorted(axioms)
    if not result:
        raise ValueError("No actual Lean axiom reports found")
    if re.search(r"\berror(?:\(|:)", text):
        raise ValueError("The supplied log contains a compiler error")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--report", type=Path, default=ROOT / "AxiomReport.lean")
    parser.add_argument("--json", type=Path, help="Save the checked declaration/axiom map")
    args = parser.parse_args()
    try:
        expected = re.findall(r"(?m)^\s*#print\s+axioms\s+(\S+)\s*$",
                              args.report.read_text(encoding="utf-8"))
        if not expected or len(expected) != len(set(expected)):
            raise ValueError("AxiomReport must contain distinct fully qualified report commands")
        actual = reports(args.log.read_text(encoding="utf-8"))
        if set(actual) != set(expected):
            missing, extra = sorted(set(expected) - set(actual)), sorted(set(actual) - set(expected))
            raise ValueError(f"Report mismatch; missing={missing}, unexpected={extra}")
        if args.json:
            args.json.parent.mkdir(parents=True, exist_ok=True)
            args.json.write_text(json.dumps(actual, indent=2) + "\n", encoding="utf-8")
    except (OSError, UnicodeError, ValueError) as error:
        print(f"Axiom check failed: {error}", file=sys.stderr)
        return 1
    print(f"Checked {len(actual)} actual axiom reports; only propext, Classical.choice and Quot.sound are permitted.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
