# API reference generation

[API.md](API.md) and [api-manifest.json](api-manifest.json) preserve the historical
13-leaf, 28-module, 103-display-site generated snapshot (75 theorems,
23 definitions, five instances). That inventory predates the separate
`PrimaryComponent` and `AdicCompletion.RestrictScalars` leaves and their test
modules: it is **not** a current whole-library inventory. Read the
[manual primary-component reference](PrimaryComponent.md) and the
[scalar-restriction guide](Guide.md#restricting-scalars-in-adic-completions)
for those declarations and their ordinary-import clients. The current public
root re-exports fifteen mathematical leaves; sixteen test/audit modules are
not re-exported by `AdicModules`. The scalar-restriction
[producer](../AdicModules/AdicCompletion/RestrictScalars.lean) and
[client](../AdicModulesTest/AdicCompletion/RestrictScalars.lean) are maintained
source references, not regenerated entries in the historical snapshot.

Read the [mathematical guide](Guide.md) for hypotheses and usage and
[CREDITS.md](CREDITS.md) for provenance. Native display sites are not the complete
kernel-declaration inventory: private examples, helpers and generated declarations
also belong to a complete actual transitive standard-axiom audit; ordinary
successful builds check proof terms without separate stored-proof replay.

## Preserved information

The bounded adapter preserves all native visible header tokens, including implicit
arguments and literal modifiers, normalizing whitespace only. It verifies each
module/name/kind, signature hash, docstring hash and source range against the fixed
inventory. Native pretty-printing depends on source namespaces, notation and type
inference; displayed fragments are not promised to elaborate in isolation.
In particular, 21 definitions and two instances have a literal `noncomputable`
modifier in the native display. Native display kind and source spelling are not
interchangeable: some proof-valued instances omit that modifier in native output.

There are 93 native source docstrings and ten separately authored explanations,
labeled **API note (not a source docstring)**. The latter live in
`scripts/api_notes.json` and require semantic review; they are not fabricated
source documentation. Two nonprivate, nonautomatic raw equation names have no
native display site: `Module.IsKilledByIdealPower.eq_1` and
`ValuationRing.localizedAdicCompletionResidueFieldEquiv.eq_1`. The separate proof
inventory accounts for them rather than inventing documentation signatures.

This assembly ships Markdown, source links and JSON provenance, not the native
HTML website, JavaScript, styles, fonts, search or dependency documentation. No
external documentation host is required to read its own API. Historical native
source URLs are checked as exact strings, not claimed to be live public web links.
All shipped API source links are relative to this same checkout.

## Native reproduction

Use a separate unchanged doc-gen4 checkout at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, including its committed manifest,
with Lean `v4.34.0-rc2`. Build that core-only tool with `lake build doc-gen4`.
Do not add it to this library or change the mathematical dependency pins.
In the library checkout, first successfully fetch the matching mathlib cache and
build all default targets as described in the root README. The following Bash
historical-snapshot commands require Python3 and the 28 original built modules;
the old adapter's whole-input `--check` is not expected to pass against a changed
current root/Axioms module. These commands do not update the manual supplement:

```sh
docgen_executable=/absolute/path/to/doc-gen4
docs_work=$(mktemp -d)
mkdir "$docs_work/analysis" "$docs_work/rendered"
source_revision=$(python3 -c 'import json; print(json.load(open("docs/api-manifest.json"))["analyzed_source_revision"])')
leaves=(AdicCompletion BoundedIdealPowerTorsion CompletedIntegers CompletedLocalStructure CompletedValuationComposite CompositeValuationSubring LocalizedCompletion LocalizedFiltration LocalizedQuotientValuationSubring LocalizedResidueField LocalizedValuationSubring PrincipalAdicSpectrum ValuationTopology)
for leaf in "${leaves[@]}"; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" "AdicModules.$leaf" api.db "https://github.com/FormalFrontier/adic-modules/blob/$source_revision/AdicModules/$leaf.lean"
done
lake env "$docgen_executable" single --build "$docs_work/analysis" AdicModules api.db "https://github.com/FormalFrontier/adic-modules/blob/$source_revision/AdicModules.lean"
for leaf in Axioms "${leaves[@]}"; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" "AdicModulesTest.$leaf" api.db "https://github.com/FormalFrontier/adic-modules/blob/$source_revision/AdicModulesTest/$leaf.lean"
done
lake env "$docgen_executable" bibPrepass --build "$docs_work/rendered" --none
lake env "$docgen_executable" fromDb --build "$docs_work/rendered" --manifest "$docs_work/rendered/manifest.json" "$docs_work/analysis/api.db"
python3 -B scripts/generate_api.py --native-data "$docs_work/rendered/doc-data" --source-revision "$source_revision" --check
python3 -B scripts/test_generate_api.py --native-data "$docs_work/rendered/doc-data"
```

Create both directories before invoking the native SQLite opener. Run the tool in
this project's `lake env` so imports resolve to its pinned compiled modules.
Retain actual argv, output, exit status, resolved artifacts and both manifests;
native warnings or failures must not be hidden. `single` receives a URL without
fragment; the native linker adds `#Lstart-Lend`. The adapter requires the exact
repository, full revision, module-specific path and recorded bounded range.

## Independent public history and data checks

`api-manifest.json` binds all 28 source files and three configuration/pin files,
module paths, tool/source revisions, three adapter/inventory/note hashes, canonical
native-record hashes, exact display names and the generated API hash. Documentation-
only successors can reuse native evidence through exact equality of all 31 inputs.
Changed mathematical sources or pins require renewed affected native checks.

When the historical source commit exists, the adapter compares every input against
that Git object. A parentless public release need not contain development history.
Only Git's explicit missing-object result, or a source-only tree without a `.git`
marker, enables fallback to the committed manifest's exact hashes. Broken Git
repositories, command failures and wrong object types refuse fallback. `--check`
compares both complete generated files byte for byte. After a reviewed inventory
update, omit `--check` to generate new files from matching native records.

The data tests require the supplied native-record directory and exercise positive
reproduction, malformed records, source/pin drift and source-only/parentless Git
contexts. They do not rerun doc-gen4 or Lean and do not authenticate the provenance
of arbitrary supplied JSON. Real native receipts require independent inspection.
Neither adapter hashes nor successful rendering certify proofs, rights or release
acceptance. Full review remains separate.
