# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only native-record or historical-presentation controls; no native rerun.

The caller must authenticate supplied inputs separately. Presentation-only tests
use the complete original public Markdown/manifest, never constructed native JSON.
Neither mode authenticates native provenance or certifies Lean proofs.
"""
import argparse
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import generate_api as api

ROOT = Path(__file__).resolve().parent.parent
RECORDS = {}
ORIGINAL_API = b""
ORIGINAL_MANIFEST = {}
SOURCES = {p: (ROOT / p).read_bytes() for p in api.INPUTS}


def fixture():
    return copy.deepcopy(RECORDS), dict(SOURCES)


def first(records):
    return records[api.MODULES[0]]["declarations"][0]


class Controls(unittest.TestCase):
    def test_complete_real_record_reproduction(self):
        records, sources = fixture()
        raw, manifest = api.render(records, api.SOURCE, sources)
        self.assertEqual(raw, (ROOT / "docs/API.md").read_bytes())
        self.assertEqual(manifest, (ROOT / "docs/api-manifest.json").read_bytes())
        facts = json.loads(manifest)
        self.assertEqual(raw.count(b"\n### "), 103)
        self.assertEqual(raw.count(b"**API note (not a source docstring):**"), 10)
        self.assertEqual(raw.count(b"**Authored editorial API note (not a native source docstring):**"), 1)
        self.assertEqual(facts["original_api_sha256"], api.ORIGINAL_API_SHA256)
        self.assertEqual(facts["editorial_declarations"], [api.EDITORIAL_DECLARATION])
        self.assertEqual(facts["documentation_counts"], dict(original_native_source_docstrings=93,
            rendered_native_source_docstrings=92, authored_missing_docstring_notes=10,
            authored_editorial_notes=1))
        self.assertEqual(facts["library_display_sites"], 103)
        self.assertEqual(facts["boundary_client_display_sites"], 0)
        self.assertEqual(len(facts["inputs"]), 31)
        self.assertEqual(len(facts["documentation_inputs"]), 3)
        self.assertEqual(set(facts["native_record_sha256"]), set(api.MODULES))
        self.assertFalse(facts["proof_certification"])
        self.assertFalse(facts["release_acceptance"])
        for module in api.MODULES[13:]:
            self.assertEqual(records[module]["declarations"], [])

    def test_all_visible_tokens_and_literal_kinds(self):
        raw = (ROOT / "docs/API.md").read_bytes()
        for record in RECORDS.values():
            for row in record["declarations"]:
                self.assertIn(api.Header(row["header"]).rendered().encode(), raw)
        self.assertIn(b"noncomputable def AdicCompletion.abstractCompletion", raw)
        self.assertIn(b"noncomputable instance ValuationSubring.compositeAlgebra", raw)
        self.assertEqual({m["display_kind"] for m in api.EXPECTED.values()},
                         {"theorem", "instance", "def", "noncomputable def",
                          "noncomputable instance"})
        from collections import Counter
        self.assertEqual(Counter(m["kind"] for m in api.EXPECTED.values()),
                         {"theorem": 75, "def": 23, "instance": 5})
        self.assertEqual(Counter(m["display_kind"] for m in api.EXPECTED.values()),
                         {"theorem": 75, "def": 2, "noncomputable def": 21,
                          "instance": 3, "noncomputable instance": 2})

    def test_parser_entities_and_nested_names(self):
        self.assertEqual(api.Header('<div><span>{A : Type u} [Module R A]</span> :'
                                    '<div class="decl_type">x &lt; y</div></div>').rendered(),
                         '{A : Type u} [Module R A] : x < y')
        self.assertEqual(api.Header('<span><span>Module</span>.<span>IsKilledByIdealPower</span></span>').rendered(),
                         'Module.IsKilledByIdealPower')

    def test_parser_rejects_invalid_markup(self):
        for text in ('<script>x</script>', '<div><span></div>', '<div>unclosed',
                     '<span onclick="x">x</span>', '<div><!--comment--></div>',
                     '<!DOCTYPE html>', 'outside', '<div/>tail'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                api.Header(text)

    def test_name_kind_module_and_completeness_refusals(self):
        mutations = [lambda r: r.pop(api.MODULES[-1]),
                     lambda r: r.update(Extra=dict(name="Extra", declarations=[])),
                     lambda r: r[api.MODULES[0]]["declarations"].pop(),
                     lambda r: r[api.MODULES[0]]["declarations"].append(copy.deepcopy(first(r))),
                     lambda r: r[api.MODULES[1]]["declarations"].append(copy.deepcopy(first(r))),
                     lambda r: r[api.MODULES[0]].update(name="Wrong")]
        for key, value in (("name", "Wrong"), ("kind", "axiom"), ("line", 0),
                           ("line", 999999), ("line", True), ("docLink", "wrong")):
            mutations.append(lambda r, k=key, v=value: first(r)["info"].update({k: v}))
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                records, sources = fixture()
                mutate(records)
                with self.assertRaises(ValueError):
                    api.render(records, api.SOURCE, sources)

    def test_signature_token_and_implicit_binder_loss(self):
        for needle, replacement in (("noncomputable def", "def"),
                                    (">Type</a> u", ">Type</a> v"),
                                    (">CommRing<", ">Ring<")):
            records, sources = fixture()
            row = next(row for r in records.values() for row in r["declarations"]
                       if needle in row["header"])
            row["header"] = row["header"].replace(needle, replacement)
            with self.subTest(needle=needle), self.assertRaises(ValueError):
                api.render(records, api.SOURCE, sources)
        records, sources = fixture()
        row = next(row for record in records.values() for row in record["declarations"]
                   if row["info"]["name"] == "AdicCompletion.abstractCompletion")
        visible = api.Header(row["header"]).rendered()
        self.assertIn('[IsUniformAddGroup R]', visible)
        from html import escape
        name = row['info']['name']
        tail = visible[len('noncomputable def ' + name):].replace('[IsUniformAddGroup R]', '')
        row['header'] = ('<div><span class="decl_kind">noncomputable def</span> '
                         '<span class="decl_name">' + escape(name) + '</span>'
                         '<span>' + escape(tail) + '</span></div>')
        with self.assertRaises(ValueError):
            api.render(records, api.SOURCE, sources)

    def test_docstring_bytes_and_absence_refused(self):
        for missing in (False, True):
            records, sources = fixture()
            row = next(row for r in records.values() for row in r["declarations"]
                       if (row["info"]["name"] in api.NOTES) == missing)
            row["info"]["doc"] = "fabricated" if missing else row["info"]["doc"] + "changed"
            with self.subTest(missing=missing), self.assertRaises(ValueError):
                api.render(records, api.SOURCE, sources)

    def test_editorial_note_still_requires_original_native_docstring(self):
        records, sources = fixture()
        row = next(row for record in records.values() for row in record["declarations"]
                   if row["info"]["name"] == api.EDITORIAL_DECLARATION)
        original = row["info"]["doc"]
        raw, _ = api.render(records, api.SOURCE, sources)
        self.assertNotIn(original.strip().encode(), raw)
        self.assertIn(api.EDITORIAL_NOTES[api.EDITORIAL_DECLARATION].encode(), raw)
        self.assertEqual(api.digest(original.encode()), api.EXPECTED[api.EDITORIAL_DECLARATION]["doc_sha256"])
        for replacement in ("", original + "changed", api.EDITORIAL_NOTES[api.EDITORIAL_DECLARATION]):
            row["info"]["doc"] = replacement
            with self.subTest(replacement=replacement), self.assertRaises(ValueError):
                api.render(records, api.SOURCE, sources)

    def test_editorial_mapping_is_exactly_one_bounded_note(self):
        records, sources = fixture()
        for notes in ({}, {api.EDITORIAL_DECLARATION: "valid", "Other": "extra"},
                      {"Other": "wrong declaration"}, {api.EDITORIAL_DECLARATION: ""},
                      {api.EDITORIAL_DECLARATION: "```"}, {api.EDITORIAL_DECLARATION: 42}):
            with self.subTest(notes=notes), patch.dict(api.EDITORIAL_NOTES, notes, clear=True):
                with self.assertRaises(ValueError):
                    api.render(records, api.SOURCE, sources)

    def test_source_url_and_exact_range_refusals(self):
        records, sources = fixture()
        info = first(records)["info"]
        valid = info["sourceLink"]
        base, fragment = valid.split("#")
        changes = [valid.replace("github.com", "github.com.evil.invalid"),
                   valid.replace("https://", "http://"),
                   valid.replace("/adic-modules/", "/other/"),
                   valid.replace(api.SOURCE, "b" * 40),
                   valid.replace("AdicCompletion.lean", "Other.lean"), base,
                   valid + "?query=1", valid + "\n", base + "#L1-L2",
                   base + "#L1-L0", base + "#L1-L999999",
                   base + "#L01-L2", base + "#L1", valid + "#extra"]
        self.assertTrue(fragment.startswith("L"))
        for value in changes:
            with self.subTest(value=value):
                altered = copy.deepcopy(records)
                first(altered)["info"]["sourceLink"] = value
                with self.assertRaises(ValueError):
                    api.render(altered, api.SOURCE, sources)

    def test_source_inventory_and_frozen_revision(self):
        records, sources = fixture()
        for revision in ("main", "a" * 40, api.SOURCE[:-1], api.SOURCE.upper()):
            with self.subTest(revision=revision), self.assertRaises(ValueError):
                api.render(records, revision, sources)
        for path in sources:
            altered = dict(sources)
            altered.pop(path)
            with self.subTest(path=path), self.assertRaises(ValueError):
                api.render(records, api.SOURCE, altered)

    def test_manifest_binding_all_thirty_one_inputs(self):
        manifest = json.loads((ROOT / "docs/api-manifest.json").read_bytes())
        api.manifest_source_binding(manifest, api.SOURCE, SOURCES)
        for key, value in (("format", 2), ("format", True), ("docgen_revision", "b" * 40),
                           ("analyzed_source_revision", "b" * 40),
                           ("modules", list(api.MODULES[:-1])), ("module_paths", {}),
                           ("inputs", {})):
            with self.subTest(key=key), self.assertRaises(ValueError):
                api.manifest_source_binding(dict(manifest, **{key: value}), api.SOURCE, SOURCES)
        for path in api.INPUTS:
            with self.subTest(path=path), self.assertRaises(ValueError):
                api.manifest_source_binding(manifest, api.SOURCE, dict(SOURCES, **{path: b"changed"}))

    def test_cli_source_only_parentless_drift_and_broken_git(self):
        with tempfile.TemporaryDirectory(prefix="adic-api-controls-") as temporary:
            root = Path(temporary) / "candidate"
            native = Path(temporary) / "native"
            native.mkdir()
            for module, record in RECORDS.items():
                (native / ("declaration-data-" + module + ".bmp")).write_text(json.dumps(record))
            paths = list(api.INPUTS) + ["scripts/" + p for p in
                    ("generate_api.py", "api_inventory.json", "api_notes.json")]
            paths += ["docs/API.md", "docs/api-manifest.json"]
            for path in paths:
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / path, target)
            argv = [sys.executable, "-B"] + ["-O"] * sys.flags.optimize + ["scripts/generate_api.py", "--native-data", str(native),
                    "--source-revision", api.SOURCE, "--check"]
            def run(ok, expected):
                result = subprocess.run(argv, cwd=root, capture_output=True)
                self.assertEqual(result.returncode == 0, ok, result.stderr.decode())
                self.assertIn(expected, (result.stdout + result.stderr).decode())
            run(True, 'committed-source-hashes')
            for path in (api.INPUTS[0], "lake-manifest.json", "docs/API.md", "scripts/api_notes.json"):
                old = (root / path).read_bytes()
                (root / path).write_bytes(old + b"\n")
                run(False, "drift" if path in api.INPUTS else "generated file differs")
                (root / path).write_bytes(old)
            (root / ".git").write_text("invalid worktree marker\n")
            run(False, "refusing fallback")
            (root / ".git").unlink()
            subprocess.run(["git", "init", "-q", str(root)], check=True, capture_output=True)
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture",
                            "-c", "user.email=fixture@example.invalid", "commit", "-qm",
                            "Synthetic independent-root fixture"], check=True)
            count = subprocess.check_output(["git", "-C", str(root), "rev-list", "--count", "HEAD"])
            self.assertEqual(count.strip(), b"1")
            self.assertFalse(api.git_source_available(root, api.SOURCE))
            run(True, 'committed-source-hashes')
            head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"]).decode().strip()
            tree = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD^{tree}"]).decode().strip()
            self.assertTrue(api.git_source_available(root, head))
            with self.assertRaisesRegex(ValueError, "not a commit"):
                api.git_source_available(root, tree)
            (native / "declaration-data-Extra.bmp").write_text("{}")
            run(False, "native module file inventory differs")


class PresentationControls(unittest.TestCase):
    def test_guarded_complete_public_snapshot_presentation(self):
        raw = api.editorial_presentation(ORIGINAL_API)
        self.assertEqual(raw, (ROOT / "docs/API.md").read_bytes())
        self.assertEqual(raw.count(b"\n### "), 103)
        self.assertEqual(raw.count(b"**API note (not a source docstring):**"), 10)
        self.assertEqual(raw.count(b"**Authored editorial API note (not a native source docstring):**"), 1)
        self.assertIn(api.EDITORIAL_NOTES[api.EDITORIAL_DECLARATION].encode(), raw)
        self.assertEqual(api.editorial_presentation(ORIGINAL_API), raw)

    def test_presentation_manifest_preserves_original_bindings(self):
        raw = api.editorial_manifest(ORIGINAL_MANIFEST, ORIGINAL_API)
        self.assertEqual(raw, (ROOT / "docs/api-manifest.json").read_bytes())
        manifest = json.loads(raw)
        for key, value in ORIGINAL_MANIFEST.items():
            if key not in {"documentation_inputs", "api_sha256"}:
                self.assertEqual(manifest[key], value, key)
        self.assertEqual(manifest["original_api_sha256"], api.digest(ORIGINAL_API))
        self.assertEqual(manifest["api_sha256"], api.digest(api.editorial_presentation(ORIGINAL_API)))
        self.assertEqual(manifest["documentation_counts"], dict(original_native_source_docstrings=93,
            rendered_native_source_docstrings=92, authored_missing_docstring_notes=10,
            authored_editorial_notes=1))
        self.assertEqual(manifest["editorial_declarations"], [api.EDITORIAL_DECLARATION])
        self.assertEqual(len(manifest["inputs"]), 31)
        self.assertEqual(len(manifest["native_record_sha256"]), 28)

    def test_changed_or_already_presented_snapshot_refused(self):
        for raw in (ORIGINAL_API + b"\n", ORIGINAL_API[:-1], b"invented small test input",
                    api.editorial_presentation(ORIGINAL_API)):
            with self.subTest(raw_hash=api.digest(raw)), self.assertRaises(ValueError):
                api.editorial_presentation(raw)

    def test_changed_manifest_identity_refused(self):
        for key in ("api_sha256", "analyzed_source_revision", "docgen_revision"):
            with self.subTest(key=key), self.assertRaises(ValueError):
                api.editorial_manifest(dict(ORIGINAL_MANIFEST, **{key: "changed"}), ORIGINAL_API)

    def test_single_editorial_mapping_refusals(self):
        for notes in ({}, {api.EDITORIAL_DECLARATION: "valid", "Other": "extra"},
                      {"Other": "wrong declaration"}, {api.EDITORIAL_DECLARATION: ""},
                      {api.EDITORIAL_DECLARATION: "```"}, {api.EDITORIAL_DECLARATION: 42}):
            with self.subTest(notes=notes), patch.dict(api.EDITORIAL_NOTES, notes, clear=True):
                with self.assertRaises(ValueError):
                    api.editorial_presentation(ORIGINAL_API)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--native-data", type=Path)
    mode.add_argument("--original-api", type=Path,
                      help="complete original historical public Markdown, not native records")
    parser.add_argument("--original-manifest", type=Path,
                        help="original public manifest for presentation-only controls")
    args = parser.parse_args()
    if args.native_data is not None:
        api.require(args.original_manifest is None, "native and presentation input modes differ")
        api.require({p.name for p in args.native_data.glob("declaration-data-*.bmp")} ==
                    {"declaration-data-" + m + ".bmp" for m in api.MODULES}, "native file inventory differs")
        RECORDS.update({m: json.loads((args.native_data / ("declaration-data-" + m + ".bmp")).read_bytes())
                        for m in api.MODULES})
        suite = "Controls"
    else:
        api.require(args.original_manifest is not None, "original public manifest required")
        ORIGINAL_API = args.original_api.read_bytes()
        ORIGINAL_MANIFEST = json.loads(args.original_manifest.read_bytes())
        suite = "PresentationControls"
    unittest.main(argv=[sys.argv[0]], defaultTest=suite, verbosity=2)
