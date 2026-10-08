#!/usr/bin/env python3
"""Audit named NDJSON export coverage before independent NanoDa replay.

This checks selection, declaration kinds, safety, metadata and axiom policy.
It does not type-check proof terms: NanoDa must subsequently accept the same
export bytes. Format source: leanprover/lean4export, pinned in the manifest.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

STANDARD_AXIOMS = frozenset(("propext", "Classical.choice", "Quot.sound"))
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
KINDS = ("axiom", "def", "thm", "opaque", "quot")


class AuditError(ValueError):
    """The exported environment or selection violates its declared policy."""


def require(condition, message):
    if not condition:
        raise AuditError(message)


def validate_manifest(manifest):
    require(manifest.get("schema_version") == 1, "unsupported manifest schema")
    require(isinstance(manifest.get("lean_version"), str), "missing Lean version")
    for key in ("lean_githash", "lean4export_commit", "nanoda_commit"):
        require(isinstance(manifest.get(key), str)
                and re.fullmatch(r"[0-9a-f]{40}", manifest[key]), f"invalid {key}")
    axioms = manifest.get("permitted_axioms", [])
    require(isinstance(axioms, list) and len(axioms) == 3
            and set(axioms) == STANDARD_AXIOMS, "manifest must permit exactly standard axioms")
    for key in ("modules", "supplemental_declarations"):
        values = manifest.get(key)
        require(isinstance(values, list) and values, f"empty {key}")
        require(all(isinstance(x, str) and NAME.fullmatch(x) for x in values), f"invalid {key}")
        require(len(values) == len(set(values)), f"duplicate {key}")
    targets = manifest.get("targets")
    require(isinstance(targets, list) and targets, "empty targets")
    names = []
    for target in targets:
        require(isinstance(target, dict) and set(target) == {"name", "kind"}, "invalid target")
        require(isinstance(target["name"], str) and NAME.fullmatch(target["name"]), "invalid target name")
        require(target["kind"] in ("thm", "def"), "target kind must be thm or def")
        names.append(target["name"])
    require(len(names) == len(set(names)), "duplicate target")


def validate_nanoda(config, manifest):
    validate_manifest(manifest)
    required = {
        "use_stdin": True,
        "unpermitted_axiom_hard_error": True,
        "unsafe_permit_all_axioms": False,
        "nat_extension": True,
        "string_extension": True,
        "num_threads": 1,
        "print_success_message": True,
        "print_axioms": True,
    }
    require(set(config) == set(required) | {"permitted_axioms"}, "unexpected NanoDa config keys")
    for key, value in required.items():
        require(type(config[key]) is type(value) and config[key] == value, f"invalid NanoDa {key}")
    require(config["permitted_axioms"] == manifest["permitted_axioms"], "NanoDa axiom policy mismatch")


def check_safety(value):
    if isinstance(value, dict):
        if "isUnsafe" in value:
            require(value["isUnsafe"] is False, "unsafe declaration in export")
        if "safety" in value:
            require(value["safety"] == "safe", "unsafe or partial definition in export")
        for child in value.values():
            check_safety(child)
    elif isinstance(value, list):
        for child in value:
            check_safety(child)


def audit_export(export_path, manifest):
    validate_manifest(manifest)
    names = {0: ""}
    declarations = {}
    axioms = set()
    metadata = None
    digest = hashlib.sha256()

    def add_declaration(kind, record):
        require(isinstance(record, dict), "invalid declaration record")
        index = record.get("name")
        require(type(index) is int and index in names, "declaration has unknown name index")
        name = names[index]
        require(name and name not in declarations, f"duplicate or anonymous declaration: {name}")
        check_safety(record)
        # Safety fields are required by version 3.1.0 for these declaration kinds.
        if kind == "def":
            require(record.get("safety") == "safe", f"missing safe definition flag: {name}")
        elif kind in ("axiom", "opaque", "inductive", "ctor", "rec"):
            require(record.get("isUnsafe") is False, f"missing safe declaration flag: {name}")
        declarations[name] = kind
        if kind == "axiom":
            require(name in STANDARD_AXIOMS, f"unpermitted axiom: {name}")
            axioms.add(name)

    with Path(export_path).open("rb") as stream:
        for line_number, raw_line in enumerate(stream, 1):
            digest.update(raw_line)
            try:
                row = json.loads(raw_line)
            except (ValueError, UnicodeDecodeError) as error:
                raise AuditError(f"invalid NDJSON at line {line_number}: {error}") from error
            require(isinstance(row, dict), f"non-object at line {line_number}")
            if line_number == 1:
                require(set(row) == {"meta"}, "first record must be metadata")
                metadata = row["meta"]
                require(isinstance(metadata, dict), "invalid metadata")
                require(metadata.get("lean") == {"version": manifest["lean_version"],
                        "githash": manifest["lean_githash"]}, "Lean metadata mismatch")
                require(metadata.get("format") == {"version": "3.1.0"}, "format metadata mismatch")
                require(metadata.get("exporter") == {"name": "lean4export", "version": "3.1.0"},
                        "exporter metadata mismatch")
                continue
            require("meta" not in row, "duplicate metadata")
            check_safety(row)
            if "in" in row:
                index = row["in"]
                require(type(index) is int and index == len(names), "non-sequential name index")
                require(("str" in row) != ("num" in row), "invalid name record")
                part = row.get("str", row.get("num"))
                require(isinstance(part, dict), "invalid name component")
                prefix = part.get("pre")
                require(type(prefix) is int and prefix in names, "unknown name prefix")
                suffix = part.get("str") if "str" in row else part.get("i")
                require(isinstance(suffix, str) if "str" in row else type(suffix) is int,
                        "invalid name suffix")
                names[index] = ".".join(x for x in (names[prefix], str(suffix)) if x)
            else:
                kinds = [kind for kind in KINDS if kind in row]
                require(len(kinds) <= 1, "multiple declaration kinds in record")
                if kinds:
                    require(set(row) == {kinds[0]}, "unexpected declaration record keys")
                    add_declaration(kinds[0], row[kinds[0]])
                elif "inductive" in row:
                    require(set(row) == {"inductive"}, "unexpected inductive record keys")
                    group = row["inductive"]
                    require(isinstance(group, dict) and set(group) == {"types", "ctors", "recs"},
                            "invalid inductive block")
                    for key, kind in (("types", "inductive"), ("ctors", "ctor"), ("recs", "rec")):
                        require(isinstance(group[key], list), "invalid inductive declarations")
                        for record in group[key]:
                            add_declaration(kind, record)
                else:
                    require("ie" in row or "il" in row, "unknown export record")
    require(metadata is not None, "empty export")
    for target in manifest["targets"]:
        name, kind = target["name"], target["kind"]
        require(name in declarations, f"missing selected declaration: {name}")
        require(declarations[name] == kind, f"wrong declaration kind: {name}")
    for name in manifest["supplemental_declarations"]:
        require(name in declarations, f"missing supplemental declaration: {name}")
    return {
        "export_sha256": digest.hexdigest(),
        "metadata": metadata,
        "selected_declarations": manifest["targets"],
        "exported_declaration_count": len(declarations),
        "exported_axioms": sorted(axioms),
        "status": "export audit passed; NanoDa replay is required separately",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("export", type=Path, nargs="?")
    parser.add_argument("--nanoda-config", type=Path)
    parser.add_argument("--list", choices=("modules", "declarations"))
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    validate_manifest(manifest)
    if args.nanoda_config:
        validate_nanoda(json.loads(args.nanoda_config.read_text(encoding="utf-8")), manifest)
    if args.list:
        values = manifest["modules"] if args.list == "modules" else (
            manifest["supplemental_declarations"] + [target["name"] for target in manifest["targets"]])
        print("\n".join(values))
    elif args.export:
        print(json.dumps(audit_export(args.export, manifest), indent=2))
    else:
        parser.error("provide an export file or --list")


if __name__ == "__main__":
    try:
        main()
    except (AuditError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"model-boundary audit failed: {error}", file=sys.stderr)
        sys.exit(1)
