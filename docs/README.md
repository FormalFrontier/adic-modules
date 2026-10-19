# API reference generation

[API.md](API.md) and [api-manifest.json](api-manifest.json) present the historical
13-leaf, 28-module, 103-display-site snapshot (75 theorems,
23 definitions, five instances), with one labeled authored editorial API note.
The original source/tool/native-record bindings remain unchanged; the manifest's
`original_api_sha256` identifies the original presentation retained in Git history,
while `api_sha256` binds the Markdown with the editorial note. This inventory
predates later library leaves: it is **not** a current whole-library inventory.
The scalar-restriction [producer](../AdicModules/AdicCompletion/RestrictScalars.lean)
and [client](../AdicModulesTest/AdicCompletion/RestrictScalars.lean), like the other
current sources, are maintained references, not regenerated historical entries.

## Headline results

The current [root overview](../README.md#headline-results), [results reference](Results.md)
and [Guide](Guide.md) describe bounded ideal-power torsion and source-torsion
primary exactness; adic scalar restriction, finite-power completion quotients
and conditional completion–tensor comparisons; Hensel lifting; Frobenius cores
and Teichmüller images; ideal-power and valuation topologies; finite two-sided
CRT; and span/closure comparisons.
For example:

- For any ideal `I` in a commutative ring and any `n : ℕ`, finite generation
  of only `I ^ n` gives the canonical `R`-algebra equivalence between the
  completion modulo the `n`th power of the extended ideal and `R ⧸ I ^ n`.
  Evaluation is the forward map and the canonical algebra map induces its inverse,
  including at degree zero. The [quotient guide](Guide.md#finite-power-quotients-of-completions)
  describes `AdicCompletion.quotientPowAlgEquiv` and its three characteristic APIs.
- Over a commutative ring, the canonical completion–tensor comparison is an
  equivalence for finitely presented modules under finite-free cofinality; finite
  projective modules and finite modules over Noetherian rings have separate comparisons.
  Independently of projectivity, completion of a finite module is finite over
  `AdicCompletion I R`. A finite projective module also remains projective over this
  canonical completed scalar ring, with no restriction on the ideal. The standard
  `Module.finitePresentation_of_projective` lemma supplies finite presentation.
- A finite pairwise comaximal family of **two-sided** ideals in a possibly
  noncommutative ring gives the canonical ring CRT equivalence and a unique
  quotient class, not a unique ring representative.
- For a commutative ring and a possibly noncommutative algebra, scalar-ideal
  submodule quotients carry ring and algebra structures with the original
  additive group and scalar action; the two-sided ideal view also works over semirings.
- For a semiring module with separately continuous addition and a dense
  subsemiring, span set-closures agree under coefficient continuity at the
  selected generators, without global coefficient continuity.

The linked statements retain all other hypotheses and boundaries.
These are current mathematical interfaces built on dependency-provided ideals,
quotients, completions, topologies and perfection, not newly generated API entries
or assertions of independent constructions of those stock objects.

For the complete current **126-source** map (**56 production including root
(55 leaves) + 70 tests/models/audit imports**), use the [Guide module map](Guide.md#module-map)
and [root import map](../README.md#imports-and-module-map). See also
[dependent products and completeness models](Guide.md#dependent-products-and-completeness-models)
for the two product library leaves and the separate test-only proposition checks/contracts
and nonzero/boundary models. The
[primary-component reference](PrimaryComponent.md) and [finite-quotient guide](FiniteQuotient.md)
give supplementary APIs. The Guide also covers scalar restriction, integer
singleton spans, p-adic bases, left-ideal density and comaximal powers, and
[dense-subsemiring span closure](Guide.md#closure-of-spans-over-a-dense-subsemiring).
The original left-ideal and span calculations and their additional private
applications are distinguished in the model map below and the Guide.

Source rosters, written proof descriptions and the historical generated snapshot
do not certify complete transitive standard-axiom assurance for private,
generated, model or imported declarations. Source and tool bindings, authored-note
labels and reproduction limits for the historical adapter are retained below.

## Mathematical model map

The four left-ideal and five span model files retain original calculations
independent of the corresponding library proofs; `Int`, `MatrixNat` and `Real`
also include additional private applications.

The model-source map uses the same fixed mathematical carriers and actions:

| Span model file | Span calculations and controls |
| --- | --- |
| [Real](../AdicModulesTest/Topology/Algebra/Module/Span/Real.lean) | Dense rational real axis with proper common closure and strict enlargement; integer real line missing density and separated by `1 / 2`. |
| [Discrete](../AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean) | Independent discrete real module missing coefficient continuity; mixed real/discrete axis with selected but not global coefficient continuity. |
| [PadicInt](../AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean) | Canonical normed p-adic self-module and integer restriction; arbitrary singleton stock closure comparison, unit/one whole closures, nonzero nonunit `p` proper closed ideal (including `2`), zero and existing ideal-power/shifted norm neighborhoods. |
| [Boundary](../AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean) | Empty, zero and subsingleton spans; nontrivial indiscrete rational self-module with nonclosed `{0}`, universal zero closure and nonzero `1` outside spans but in closures. |
| [Indiscrete](../AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean) | Indiscrete rational scalars and canonical independent discrete `ULift.{v} ℚ`; dense proper integer range, fixed-scalar continuity, failed selected coefficient continuity, closed proper integer/restricted spans excluding transported half, whole rational span and unequal closures. |

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

The frozen native records contain **93 original source docstrings**. The adapter
still validates all 93 original docstring hashes; it renders 92 verbatim and
presents exactly `ValuationRing.coe_localizedAdicCompletionValuationSubringEquiv_apply`
with an **Authored editorial API note (not a native source docstring)** instead.
Its original native docstring/inventory hash is not replaced by the authored note
or by the current Lean docstring. Ten unchanged missing-docstring explanations
are labeled **API note (not a source docstring)**. In `scripts/api_notes.json`,
`missing_docstrings` holds those ten notes and `editorial_docstrings` holds only
the single editorial note. All authored notes require semantic review; none is
native documentation or a new doc-gen run. The manifest records the original and
rendered native counts and both authored-note counts separately.
Two nonprivate, nonautomatic raw equation names have no
native display site: `Module.IsKilledByIdealPower.eq_1` and
`ValuationRing.localizedAdicCompletionResidueFieldEquiv.eq_1`. The separate proof
inventory accounts for them rather than inventing documentation signatures.

This assembly ships Markdown, source links and JSON provenance, not the native
HTML website, JavaScript, styles, fonts, search or dependency documentation. No
external documentation host is required to read its own API. Historical native
source URLs are checked as exact strings, not claimed to be live public web links.
All shipped API source links are relative to this same checkout.

## Editorial presentation reproduction

Native analysis and editorial presentation are separate stages. The full adapter
first validates the original native records and assembles the original historical
Markdown, then calls `editorial_presentation` on those complete bytes. The
post-render function requires the original SHA-256
`d60949e7068b5c0e660544e4a1eb86b10369957f041f7cd0bade4125bf423ca9`,
and permits exactly the single authored mapping above. It changes that explanatory
paragraph and the presentation's title/scope/count disclosure, not any display
signature, declaration, source link or module inventory. `editorial_manifest`
retains the original native/source/tool bindings and updates only presentation
metadata and adapter/output hashes.

The same bounded stage can be checked without native doc-data, using the complete
original public Markdown and its original public manifest retained in Git history.
These are historical public output files, **not reconstructed native JSON**:

```sh
original_api=/absolute/path/to/original-API.md
original_manifest=/absolute/path/to/original-api-manifest.json
python3 -B - "$original_api" "$original_manifest" <<'PY'
import json
from pathlib import Path
import sys
sys.path.insert(0, "scripts")
import generate_api as api
original = Path(sys.argv[1]).read_bytes()
manifest = json.loads(Path(sys.argv[2]).read_bytes())
api.require(api.editorial_presentation(original) == Path("docs/API.md").read_bytes(),
            "editorial presentation differs")
api.require(api.editorial_manifest(manifest, original) == Path("docs/api-manifest.json").read_bytes(),
            "editorial manifest differs")
PY
python3 -B scripts/test_generate_api.py --original-api "$original_api" --original-manifest "$original_manifest"
```

This validates the guarded post-render presentation, **not full native
regeneration**, a new native run or the provenance of arbitrary supplied records.
Native-record controls require complete authentic native inputs separately; their
absence is not permission to fabricate them from Markdown. Changed current Lean
docstrings are not historical native inputs.

## Full native reproduction

Use a separate unchanged doc-gen4 checkout at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, including its committed manifest,
with Lean `v4.34.0-rc2`. Build that core-only tool with `lake build doc-gen4`.
Do not add it to this library or change the mathematical dependency pins.
Use a separate library checkout of the **unchanged frozen analyzed source**
`2de7cf7ce503c2243cb5c3b93b7a2d78ec700b3f`, with all 31 original source/pin
files, including its Mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103` graph.
Copy the current four `scripts/` API adapter/inventory/notes/data-test files and
both `docs/API.md` and `docs/api-manifest.json` into that checkout for presentation
reproduction, without copying current Lean sources, roots or configuration/pins.
First successfully fetch the matching historical mathlib cache and build all
original default targets. The following Bash commands run in that frozen-source
checkout and require Python3 and its 28 original built modules. They do not
regenerate the current whole library or update the manual supplement. The
adapter's whole-input `--check` must refuse the changed current source/pin graph:

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

`api-manifest.json` binds all 28 original source files and three original
configuration/pin files, module paths, frozen tool/source revisions, three current
adapter/inventory/note hashes, unchanged canonical native-record hashes, exact
display names and the rendered API hash. It separately records the original API
presentation hash, single editorial declaration and original-versus-rendered
native/authored counts. The editorial adapter change is not renewed native
analysis: its inputs remain the historical 31 files and native records, not the
changed current Lean docstrings or dependency graph. Native evidence can be reused
only for the exactly bound original inputs. Claims about changed sources or pins
require renewed affected native checks.

When the historical source commit exists, the adapter compares every input against
that Git object. A parentless public release need not contain development history.
Only Git's explicit missing-object result, or a source-only tree without a `.git`
marker, enables fallback to the committed manifest's exact hashes. Broken Git
repositories, command failures and wrong object types refuse fallback. `--check`
compares both complete rendered files byte for byte, including the deterministic
editorial note and presentation metadata. Omit `--check` only to render from the
matching original native records and frozen source/pin inputs. The single
editorial mapping cannot bypass original docstring verification or extend the
fixed declaration inventory.

With `--native-data`, the data tests require a supplied authentic native-record
directory and exercise positive full reproduction, malformed records, source/pin
drift and source-only/parentless Git contexts. With `--original-api` and
`--original-manifest`, only the presentation controls run: complete original
public-output hash guards, the single note, unchanged provenance bindings and
exact presented-output/manifest equality. Neither mode reruns doc-gen4 or Lean
or authenticates the provenance of arbitrary supplied JSON. Real native receipts
require independent inspection.
Neither adapter hashes nor successful rendering certify proofs, rights or release
acceptance. Full review remains separate.
