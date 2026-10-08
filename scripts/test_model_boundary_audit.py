#!/usr/bin/env python3
"""Negative coverage tests for export auditing; no native builds required."""

from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

from audit_model_boundary import AuditError, audit_export, validate_manifest, validate_nanoda

ROOT = Path(__file__).resolve().parents[1]


class ExportAuditTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((ROOT / "model-boundary-replay.json").read_text(encoding="utf-8"))
        self.manifest["modules"] = ["Fixture"]
        self.manifest["targets"] = [{"name": "Proof.result", "kind": "thm"}]
        self.manifest["supplemental_declarations"] = ["Seed"]
        self.rows = [{"meta": {
            "lean": {"version": self.manifest["lean_version"], "githash": self.manifest["lean_githash"]},
            "format": {"version": "3.1.0"},
            "exporter": {"name": "lean4export", "version": "3.1.0"},
        }}]
        self.names = {"": 0}
        self.add("Seed", "def")
        self.add("Proof.result", "thm")

    def name(self, name):
        if name not in self.names:
            prefix, _, suffix = name.rpartition(".")
            prefix_id = self.name(prefix)
            name_id = len(self.names)
            self.names[name] = name_id
            self.rows.append({"str": {"pre": prefix_id, "str": suffix}, "in": name_id})
        return self.names[name]

    def add(self, name, kind):
        record = {"name": self.name(name), "levelParams": [], "type": 0}
        if kind in ("def", "thm", "opaque"):
            record["value"] = 0
        if kind == "def":
            record["safety"] = "safe"
        if kind in ("axiom", "opaque", "inductive", "ctor", "rec"):
            record["isUnsafe"] = False
        self.rows.append({kind: record})

    def audit(self):
        with tempfile.TemporaryDirectory(prefix="model-boundary-audit-") as directory:
            path = Path(directory) / "export.ndjson"
            path.write_text("".join(json.dumps(row) + "\n" for row in self.rows), encoding="utf-8")
            return audit_export(path, self.manifest)

    def fails(self, message):
        with self.assertRaisesRegex(AuditError, message):
            self.audit()

    def test_accepts_selected_safe_declarations(self):
        report = self.audit()
        self.assertEqual(report["exported_declaration_count"], 2)
        self.assertEqual(report["selected_declarations"], self.manifest["targets"])
        self.assertEqual(len(report["export_sha256"]), 64)

    def test_missing_target(self):
        self.rows.pop()
        self.fails("missing selected declaration")

    def test_wrong_target_kind(self):
        record = self.rows[-1].pop("thm")
        record["safety"] = "safe"
        self.rows[-1]["def"] = record
        self.fails("wrong declaration kind")

    def test_target_replaced_by_axiom(self):
        record = self.rows[-1].pop("thm")
        record["isUnsafe"] = False
        self.rows[-1]["axiom"] = record
        self.fails("unpermitted axiom")

    def test_unpermitted_unused_axiom(self):
        self.add("sorryAx", "axiom")
        self.fails("unpermitted axiom")

    def test_standard_axiom_is_allowed(self):
        self.add("Quot.sound", "axiom")
        self.assertEqual(self.audit()["exported_axioms"], ["Quot.sound"])

    def test_unsafe_definition(self):
        self.rows[2]["def"]["safety"] = "unsafe"
        self.fails("unsafe or partial")

    def test_partial_definition(self):
        self.rows[2]["def"]["safety"] = "partial"
        self.fails("unsafe or partial")

    def test_missing_definition_safety(self):
        del self.rows[2]["def"]["safety"]
        self.fails("missing safe definition flag")

    def test_unsafe_inductive_constructor(self):
        constructor = self.name("I.mk")
        self.rows.append({"inductive": {"types": [], "ctors": [
            {"name": constructor, "isUnsafe": True}], "recs": []}})
        self.fails("unsafe declaration")

    def test_safe_inductive_block(self):
        indices = [self.name(name) for name in ("I", "I.mk", "I.rec")]
        # Exact field layout from pinned Export.lean's grouped serializer.
        self.rows.append({"inductive": {
            "types": [{"name": indices[0], "levelParams": [], "type": 0,
                       "numParams": 0, "numIndices": 0, "all": [indices[0]],
                       "ctors": [indices[1]], "numNested": 0, "isRec": False,
                       "isReflexive": False, "isUnsafe": False}],
            "ctors": [{"name": indices[1], "levelParams": [], "type": 0,
                       "induct": indices[0], "cidx": 0, "numParams": 0,
                       "numFields": 0, "isUnsafe": False}],
            "recs": [{"name": indices[2], "levelParams": [], "type": 0,
                      "all": [indices[0]], "numParams": 0, "numIndices": 0,
                      "numMotives": 1, "numMinors": 1, "rules": [],
                      "k": False, "isUnsafe": False}],
        }})
        self.assertEqual(self.audit()["exported_declaration_count"], 5)

    def test_all_inductive_components_require_false_safety(self):
        for key in ("types", "ctors", "recs"):
            for value in (True, None):
                with self.subTest(component=key, safety=value):
                    original = deepcopy(self.rows)
                    record = {"name": self.name("I"), "isUnsafe": value}
                    group = {"types": [], "ctors": [], "recs": []}
                    group[key] = [record]
                    self.rows.append({"inductive": group})
                    self.fails("unsafe declaration")
                    self.rows = original
                    self.names.pop("I")

    def test_metadata_version_mismatch(self):
        self.rows[0]["meta"]["lean"]["version"] = "4.31.0"
        self.fails("Lean metadata mismatch")

    def test_metadata_hash_mismatch(self):
        self.rows[0]["meta"]["lean"]["githash"] = "0" * 40
        self.fails("Lean metadata mismatch")

    def test_metadata_format_mismatch(self):
        self.rows[0]["meta"]["format"]["version"] = "3.2.0"
        self.fails("format metadata mismatch")

    def test_metadata_exporter_mismatch(self):
        self.rows[0]["meta"]["exporter"]["name"] = "untrusted"
        self.fails("exporter metadata mismatch")

    def test_duplicate_metadata(self):
        self.rows.append(deepcopy(self.rows[0]))
        self.fails("duplicate metadata")

    def test_duplicate_declaration(self):
        self.rows.append(deepcopy(self.rows[-1]))
        self.fails("duplicate or anonymous declaration")

    def test_missing_supplement(self):
        self.manifest["supplemental_declarations"] = ["Other"]
        self.fails("missing supplemental")

    def test_unknown_name_index(self):
        self.rows[-1]["thm"]["name"] = 1000
        self.fails("unknown name index")

    def test_empty_export(self):
        self.rows = []
        self.fails("empty export")

    def test_manifest_cannot_widen_axioms(self):
        self.manifest["permitted_axioms"].append("Lean.trustCompiler")
        self.fails("exactly standard axioms")


class ConfigurationTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((ROOT / "model-boundary-replay.json").read_text(encoding="utf-8"))
        self.config = json.loads((ROOT / "nanoda-model-boundary.json").read_text(encoding="utf-8"))

    def test_repository_configuration(self):
        validate_manifest(self.manifest)
        validate_nanoda(self.config, self.manifest)

    def test_nanoda_cannot_disable_hard_axiom_error(self):
        self.config["unpermitted_axiom_hard_error"] = False
        with self.assertRaisesRegex(AuditError, "invalid NanoDa"):
            validate_nanoda(self.config, self.manifest)

    def test_nanoda_cannot_accept_all_axioms(self):
        self.config["unsafe_permit_all_axioms"] = True
        with self.assertRaisesRegex(AuditError, "invalid NanoDa"):
            validate_nanoda(self.config, self.manifest)

    def test_nanoda_cannot_request_more_threads(self):
        self.config["num_threads"] = 2
        with self.assertRaisesRegex(AuditError, "invalid NanoDa"):
            validate_nanoda(self.config, self.manifest)

    def test_nanoda_cannot_widen_axioms(self):
        self.config["permitted_axioms"].append("Lean.trustCompiler")
        with self.assertRaisesRegex(AuditError, "axiom policy mismatch"):
            validate_nanoda(self.config, self.manifest)

    def test_nanoda_cannot_add_file_input(self):
        self.config["export_file_path"] = "other.ndjson"
        with self.assertRaisesRegex(AuditError, "unexpected NanoDa config keys"):
            validate_nanoda(self.config, self.manifest)

    def test_nanoda_rejects_boolean_thread_count(self):
        self.config["num_threads"] = True
        with self.assertRaisesRegex(AuditError, "invalid NanoDa"):
            validate_nanoda(self.config, self.manifest)

    def test_nanoda_extensions_cannot_be_disabled(self):
        for key in ("nat_extension", "string_extension"):
            with self.subTest(option=key):
                config = deepcopy(self.config)
                config[key] = False
                with self.assertRaisesRegex(AuditError, "invalid NanoDa"):
                    validate_nanoda(config, self.manifest)


if __name__ == "__main__":
    unittest.main()
