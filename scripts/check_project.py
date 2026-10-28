#!/usr/bin/env python3
"""Check publication metadata, locked dependencies and the Lean source layout.

These static checks complement Lean and Comparator; they are not a proof checker.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

try:
    try:
        import tomllib
    except ModuleNotFoundError:
        import tomli as tomllib
    import jsonschema
    import yaml
except ImportError as error:
    raise SystemExit(
        "Install the validation dependencies with: "
        "python3 -m pip install -r scripts/requirements.txt"
    ) from error


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PRIMARY = {
    "SpectralIsometry.main_result",
    "SpectralIsometry.entire_group",
    "SpectralIsometry.normalization",
}
MAINTAINERS = {"Matthew J. Colbrook", "George Stepaniants"}
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
MATHLIB = "b63f6e8a68d220e3b3bc4f3792bb53650d375f24"
PACKAGES = {
    "mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets",
    "aesop", "Qq", "batteries", "Cli",
}
PLACEHOLDER = re.compile(r"\b(?:TODO|TBD|CHANGEME|unassigned|unspecified|placeholder)\b", re.I)
IMPORT = re.compile(r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([^\r\n]*)")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def lean_code(text: str) -> str:
    """Mask nested comments and ordinary strings while preserving line breaks."""
    out = list(text)
    index = depth = 0
    string = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                out[index:index + 2] = "  "
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                out[index:index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if text[index] not in "\r\n":
                    out[index] = " "
                index += 1
        elif string:
            if text[index] == "\\":
                out[index] = " "
                index += 1
                if index < len(text):
                    if text[index] not in "\r\n":
                        out[index] = " "
                    index += 1
            elif text[index] == '"':
                out[index] = " "
                string = False
                index += 1
            else:
                if text[index] not in "\r\n":
                    out[index] = " "
                index += 1
        elif text.startswith("/-", index):
            out[index:index + 2] = "  "
            depth = 1
            index += 2
        elif text.startswith("--", index):
            while index < len(text) and text[index] not in "\r\n":
                out[index] = " "
                index += 1
        elif text[index] == '"':
            out[index] = " "
            string = True
            index += 1
        else:
            index += 1
    require(depth == 0 and not string, "Unterminated Lean comment or string")
    return "".join(out)


def imports(code: str) -> list[str]:
    result = []
    for match in IMPORT.finditer(code):
        names = match.group(1).split()
        if names[:1] == ["all"]:
            names = names[1:]
        require(bool(names), "Empty Lean import")
        for name in names:
            require(bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", name)),
                    f"Unsupported Lean import syntax: {name}")
        result.extend(names)
    return result


def module_path(root: Path, name: str) -> Path:
    require(bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", name)),
            f"Invalid module name: {name}")
    return root.joinpath(*name.split(".")).with_suffix(".lean")


def foundation_import(name: str) -> bool:
    return name in {"Mathlib", "Lean", "Init", "Std"} or name.startswith(
        ("Mathlib.", "Lean.", "Init.", "Std.")
    )


def comparator_config(root: Path, filename: str, components: bool) -> dict:
    document = json.loads((root / filename).read_text(encoding="utf-8"))
    require(isinstance(document, dict), f"{filename}: expected a JSON object")
    require("external_kernels" not in document,
            f"{filename}: external_kernels is not a Palomar submitter field")
    require("enable_nanoda" not in document,
            f"{filename}: bundled kernels are registered by the verification script")
    names = document.get("theorem_names")
    require(isinstance(names, list) and all(isinstance(name, str) for name in names),
            f"{filename}: theorem_names must be a list of declaration names")
    require(len(names) == len(set(names)), f"{filename}: duplicate theorem names")
    require(PRIMARY <= set(names), f"{filename}: all three principal results are required")
    require(len(names) == (68 if components else 3),
            f"{filename}: expected {'68' if components else '3'} theorem targets")
    require(set(document.get("permitted_axioms", [])) == ALLOWED_AXIOMS,
            f"{filename}: permitted_axioms must contain exactly the standard three axioms")
    require(document.get("definition_names", []) == [],
            f"{filename}: no separate definition holes are used")
    require(document.get("solution_module") == "Solution",
            f"{filename}: the proof module must be Solution")
    require(isinstance(document.get("challenge_module"), str),
            f"{filename}: missing challenge_module")
    require(module_path(root, document["challenge_module"]).is_file(),
            f"{filename}: challenge module is missing")
    return document


def check(root: Path, components: bool) -> tuple[int, int]:
    for filename in ["README.md", "LICENSE", "NOTICE", "formalization.yaml",
                     "lean-toolchain", "lakefile.toml", "lake-manifest.json",
                     "Solution.lean", "Challenge.lean", "AxiomReport.lean"]:
        require((root / filename).is_file(), f"Missing project file: {filename}")

    metadata = yaml.safe_load((root / "formalization.yaml").read_text(encoding="utf-8"))
    schema = json.loads((ROOT / "scripts/formalization.schema.json").read_text(encoding="utf-8"))
    jsonschema.validate(metadata, schema)
    project = metadata["project"]
    require(project.get("license") == "Apache-2.0", "Project licence must be Apache-2.0")
    for field in ["name", "authors", "responsible_maintainers"]:
        value = project.get(field)
        entries = value if isinstance(value, list) else [value]
        require(bool(entries) and all(isinstance(entry, str) and entry.strip() for entry in entries),
                f"project.{field}: nonempty text is required")
        require(not any(PLACEHOLDER.search(entry) for entry in entries),
                f"project.{field}: replace placeholder values before submission")
    require(MAINTAINERS <= set(project["responsible_maintainers"]),
            "Both named human maintainers must be recorded")
    require(bool(MAINTAINERS & set(project["authors"])),
            "Record human formalization authors in project.authors; AI assistance belongs in automation")
    status = metadata.get("status", {})
    require(status.get("sorry_count") == 0 and status.get("sorry_in_definitions") == 0,
            "Proof-development sorry counts must be zero")
    require(set(status.get("axioms", [])) <= ALLOWED_AXIOMS,
            "Metadata declares an unpermitted axiom")
    results = status.get("main_results", [])
    require(PRIMARY <= {item.get("declaration") for item in results},
            "Metadata must list the three principal declarations")
    for item in results:
        require((root / item.get("file", "")).is_file(), "A main-result file is missing")
        require((root / item.get("comparator_config", "")).is_file(),
                "A main-result Comparator configuration is missing")
        require(set(item.get("axioms", [])) <= ALLOWED_AXIOMS,
                "A main-result metadata entry declares an unpermitted axiom")
    for source in metadata.get("sources", []):
        location = source.get("location")
        if location and not re.match(r"https?://", location):
            require((root / location).is_file(), f"Missing source reference: {location}")

    licence = (root / "LICENSE").read_text(encoding="utf-8")
    require(all(text in licence for text in ["Apache License", "Version 2.0",
            "TERMS AND CONDITIONS", "END OF TERMS AND CONDITIONS"]),
            "LICENSE must contain the complete standard Apache-2.0 text")
    notice = (root / "NOTICE").read_text(encoding="utf-8").lower()
    require("openai" in notice and "mathlib" in notice,
            "NOTICE must retain the Mathlib and OpenAI proof-reuse attribution")

    readme = (root / "README.md").read_text(encoding="utf-8")
    require(not re.search(r"\b(?:checksum\w*|hash(?:es)?|sha-?256)\b|\b[0-9a-fA-F]{40,64}\b", readme, re.I),
            "Keep verification digests and dependency revisions out of the README")
    require(not re.search(r"natural[- ]language|proof[- ]route|method[- ]substitution", readme, re.I),
            "Keep proof-comparison discussion out of the README")
    require(not re.search(r"\b(?:TODO|TBD|CHANGEME|YOUR_USERNAME|YOUR_REPOSITORY)\b|<(?:owner|repo|repository)>", readme, re.I),
            "Replace publication placeholders in the README")
    require("https://submit.palomar-registry.org/" in readme,
            "README must link to the current Palomar submission form")
    require("PalomarSubmission/issues/new" not in readme,
            "README links to the retired Palomar submission form")

    require((root / "lean-toolchain").read_text(encoding="utf-8").strip() == TOOLCHAIN,
            "Use the release's pinned Lean 4.35.0-rc3 toolchain")
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = manifest.get("packages", [])
    require(len(packages) == 9 and {package.get("name") for package in packages} == PACKAGES,
            "The resolved dependency lockfile must contain the nine selected packages")
    for package in packages:
        require(package.get("type") == "git" and
                bool(re.fullmatch(r"[0-9a-f]{40}", package.get("rev", ""))),
                f"Dependency {package.get('name')}: use a resolved Git revision")
    mathlib = next(package for package in packages if package["name"] == "mathlib")
    require(mathlib["rev"] == MATHLIB, "The Mathlib lockfile revision changed")
    lake = tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
    requirement = [item for item in lake.get("require", []) if item.get("name") == "mathlib"]
    require(len(requirement) == 1 and requirement[0].get("rev") == MATHLIB,
            "The Lake Mathlib requirement must agree with the resolved lockfile")

    configs = [comparator_config(root, "comparator.json", False)]
    require(configs[0]["challenge_module"] == "Challenge",
            "The principal challenge module must be Challenge")
    if (root / "comparator-components.json").is_file() or components:
        configs.append(comparator_config(root, "comparator-components.json", True))
    challenges = {document["challenge_module"]: document for document in configs}
    challenge_paths = {module_path(root, name).resolve(): document for name, document in challenges.items()}
    source_roots = [root / library.get("srcDir", ".") for library in lake.get("lean_lib", [])]
    source_roots.append(root)
    paths = sorted(path for path in root.rglob("*.lean")
                   if not {".lake", ".git", ".venv", "__pycache__"} & set(path.relative_to(root).parts))
    require(bool(paths), "No Lean source files found")
    for path in paths:
        relative = path.relative_to(root).as_posix()
        text = path.read_text(encoding="utf-8-sig")
        code = lean_code(text)
        require(re.match(r"\s*module\b", code) is not None, f"{relative}: missing module header")
        require(len(text.splitlines()) <= 10000, f"{relative}: split modules longer than 10000 lines")
        names = imports(code)
        for name in names:
            if not foundation_import(name):
                require(any(module_path(base, name).is_file() for base in source_roots),
                        f"{relative}: unresolved local import {name}")
        require(not re.search(r"\b(?:axiom|admit|native_decide|ofReduceBool)\b", code),
                f"{relative}: prohibited proof admission or native trust token")
        require("debug.skipKernelTC" not in code, f"{relative}: kernel checking must remain enabled")
        if path.resolve() in challenge_paths:
            document = challenge_paths[path.resolve()]
            require(all(foundation_import(name) for name in names),
                    f"{relative}: a Challenge may import only foundation libraries")
            if path.name == "Challenge.lean":
                require(len(text.splitlines()) < 300, "Keep the principal Challenge below 300 lines")
                require(all(name == "Mathlib" or name.startswith("Mathlib.") for name in names),
                        "The principal Challenge may import only Mathlib")
            require(len(re.findall(r"\bsorry\b", code)) == len(document["theorem_names"]),
                    f"{relative}: expected one deliberate placeholder for each target")
        else:
            require(not re.search(r"\bsorry\b", code), f"{relative}: proof source contains sorry")
            require(not set(names) & set(challenges), f"{relative}: proof source imports a Challenge")
    return len(paths), len(configs[-1]["theorem_names"]) if components else 3


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--components", action="store_true", help="Require the optional 68-target configuration")
    args = parser.parse_args()
    try:
        count, targets = check(args.root.resolve(), args.components)
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, jsonschema.ValidationError) as error:
        print(f"Project check failed: {error}", file=sys.stderr)
        return 1
    print(f"Project layout and metadata checks passed: {count} Lean files, {targets} selected targets.")
    print("This static check is followed by the actual Lean and Comparator runs.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
