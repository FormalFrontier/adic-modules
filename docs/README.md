# API reference generation

[API.md](API.md) and [api-manifest.json](api-manifest.json) present the historical
13-leaf, 28-module, 103-display-site snapshot (75 theorems,
23 definitions, five instances), with one labeled authored editorial API note.
The original source/tool/native-record bindings remain unchanged; the manifest's
`original_api_sha256` identifies the original presentation retained in Git history,
while `api_sha256` binds the Markdown with the editorial note. That inventory
predates the separate
`PrimaryComponent`, `AdicCompletion.RestrictScalars`, `Algebra.Module.Int`,
`Topology.Algebra.Submodule`, `Topology.Algebra.PadicInt`,
`RingTheory.Ideal.Operations`, `Topology.Algebra.Ideal` and
`Topology.Algebra.Module.Span` leaves and their test/model modules:
it is **not** a current whole-library inventory. Read the
[manual primary-component reference](PrimaryComponent.md) and the
[scalar-restriction guide](Guide.md#restricting-scalars-in-adic-completions)
for those declarations and their ordinary-import clients, the
[integer-singleton-span guide](Guide.md#integer-singleton-spans-in-unital-rings)
and its [clients](../AdicModulesTest/Algebra/Module/Int.lean), and the
[submodule-closure module](../AdicModules/Topology/Algebra/Submodule.lean) for
its neighborhood-basis formula and
[applications](../AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean).
The [p-adic guide](Guide.md#p-adic-neighborhood-bases-and-integer-spans) describes
the twelve-result generic-density and p-adic API: ideal-power bases, linear
topology, density, properness and top suprema with restricted ideal neighborhoods.
Its [clients](../AdicModulesTest/Topology/Algebra/PadicInt.lean) gain membership of
excluded elements after adding positive-degree neighborhoods.
The [comaximal-powers guide](Guide.md#comaximal-powers-of-left-ideals)
describes `Ideal.sup_pow_eq_top_of_sup_eq_top` and its written subtraction-free
proof for arbitrary semiring left ideals at every natural exponent, including
zero. Neither ideal must be two-sided; powers are formed in the original
semiring. Two private lemmas recover Mathlib's two-sided specializations
without adding public entry points. The
[left-ideal density guide](Guide.md#left-ideal-density-and-integer-powers-topologies)
describes `Ideal.dense_iff_sup_eq_top_of_hasBasis` and its written direct
additive proof by translated neighborhoods in the supplied powers topology.
It needs only a ring with a compatible topological additive-group structure
and a powers basis at zero, without two-sidedness or multiplication continuity;
no restriction to integer scalars is needed. The four left-ideal model files
retain original direct calculations independent of the general density
criterion. `Int` additionally applies that criterion to `(3)` in the `(2)`-adic
integers, and `MatrixNat` additionally applies the comaximal-powers theorem
to its column ideals. The [matrix](Guide.md#matrix-left-ideal-models) and
[boundary](Guide.md#ideal-power-boundary-models) calculations are documented
separately.
The current public root re-exports **21 mathematical source leaves**;
**28 test/model/audit source modules** are not re-exported by `AdicModules`.
Including the public root gives **50 maintained Lean source modules**: 22
library sources including the root and 28 test sources. These are source-file
counts, not counts of mathematical models, compiled modules, generated API
entries, kernel declarations or audited axioms.
The dense-subsemiring comparison,
`Submodule.closure_span_eq_of_dense_subsemiring`, uses additive-submonoid
closure, continuous dense images at selected generators and span induction.
The original span and closure calculations in the five model files (`Real`,
`Discrete`, `PadicInt`, `Boundary`, `Indiscrete`) are independent of the generic
proof. `Real` also includes an additional private application of
`Submodule.closure_span_eq_of_dense_subsemiring` to the rational axis, identifying
its proper closure and excluding the second coordinate unit.
Read the
[span-comparison guide](Guide.md#closure-of-spans-over-a-dense-subsemiring)
for the original calculations and private real application, canonical actions and
separation and coefficient-continuity boundaries. None of these current sources is a regenerated
entry in the historical native API snapshot. These counts, written proof
descriptions and the generated snapshot do not certify complete transitive
standard-axiom assurance for private, generated, model or imported declarations.
The scalar-restriction [producer](../AdicModules/AdicCompletion/RestrictScalars.lean) and
[client](../AdicModulesTest/AdicCompletion/RestrictScalars.lean) are maintained
source references, not regenerated entries in the historical snapshot.

## Current source roster

The table enumerates all 21 library leaves and all 28 test/model/audit sources;
[`AdicModules`](../AdicModules.lean) is the additional public root. Module names
use the prefixes `AdicModules.` and `AdicModulesTest.` respectively.
The four left-ideal and five span model files retain original calculations
independent of the corresponding library proofs; `Int`, `MatrixNat` and `Real`
also include additional private applications.

| Library leaf | Test/audit sources |
| --- | --- |
| [BoundedIdealPowerTorsion](../AdicModules/BoundedIdealPowerTorsion.lean) | [BoundedIdealPowerTorsion](../AdicModulesTest/BoundedIdealPowerTorsion.lean) |
| [PrimaryComponent](../AdicModules/PrimaryComponent.lean) | [PrimaryComponent](../AdicModulesTest/PrimaryComponent.lean) |
| [AdicCompletion](../AdicModules/AdicCompletion.lean) | [AdicCompletion](../AdicModulesTest/AdicCompletion.lean) |
| [AdicCompletion.RestrictScalars](../AdicModules/AdicCompletion/RestrictScalars.lean) | [AdicCompletion.RestrictScalars](../AdicModulesTest/AdicCompletion/RestrictScalars.lean) |
| [Algebra.Module.Int](../AdicModules/Algebra/Module/Int.lean) | [Algebra.Module.Int](../AdicModulesTest/Algebra/Module/Int.lean) |
| [RingTheory.Ideal.Operations](../AdicModules/RingTheory/Ideal/Operations.lean) | [RingTheory.Ideal.Operations.MatrixNat](../AdicModulesTest/RingTheory/Ideal/Operations/MatrixNat.lean) (original calculations and additional private comaximal-powers application) |
| [Topology.Algebra.Ideal](../AdicModules/Topology/Algebra/Ideal.lean) | [Topology.Algebra.Ideal.Int](../AdicModulesTest/Topology/Algebra/Ideal/Int.lean), [Topology.Algebra.Ideal.Matrix](../AdicModulesTest/Topology/Algebra/Ideal/Matrix.lean), [Topology.Algebra.Ideal.Boundary](../AdicModulesTest/Topology/Algebra/Ideal/Boundary.lean) (original calculations and additional private density application in Int) |
| [Topology.Algebra.Submodule](../AdicModules/Topology/Algebra/Submodule.lean) | [Topology.Algebra.SubmoduleClosure](../AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean) |
| [Topology.Algebra.PadicInt](../AdicModules/Topology/Algebra/PadicInt.lean) | [Topology.Algebra.PadicInt](../AdicModulesTest/Topology/Algebra/PadicInt.lean) |
| [Topology.Algebra.Module.Span](../AdicModules/Topology/Algebra/Module/Span.lean) | [Topology.Algebra.Module.Span.Real](../AdicModulesTest/Topology/Algebra/Module/Span/Real.lean), [Topology.Algebra.Module.Span.Discrete](../AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean), [Topology.Algebra.Module.Span.PadicInt](../AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean), [Topology.Algebra.Module.Span.Boundary](../AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean), [Topology.Algebra.Module.Span.Indiscrete](../AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean) |
| [ValuationTopology](../AdicModules/ValuationTopology.lean) | [ValuationTopology](../AdicModulesTest/ValuationTopology.lean) |
| [CompletedIntegers](../AdicModules/CompletedIntegers.lean) | [CompletedIntegers](../AdicModulesTest/CompletedIntegers.lean) |
| [CompletedLocalStructure](../AdicModules/CompletedLocalStructure.lean) | [CompletedLocalStructure](../AdicModulesTest/CompletedLocalStructure.lean) |
| [PrincipalAdicSpectrum](../AdicModules/PrincipalAdicSpectrum.lean) | [PrincipalAdicSpectrum](../AdicModulesTest/PrincipalAdicSpectrum.lean) |
| [LocalizedFiltration](../AdicModules/LocalizedFiltration.lean) | [LocalizedFiltration](../AdicModulesTest/LocalizedFiltration.lean) |
| [LocalizedCompletion](../AdicModules/LocalizedCompletion.lean) | [LocalizedCompletion](../AdicModulesTest/LocalizedCompletion.lean) |
| [LocalizedValuationSubring](../AdicModules/LocalizedValuationSubring.lean) | [LocalizedValuationSubring](../AdicModulesTest/LocalizedValuationSubring.lean) |
| [LocalizedResidueField](../AdicModules/LocalizedResidueField.lean) | [LocalizedResidueField](../AdicModulesTest/LocalizedResidueField.lean) |
| [LocalizedQuotientValuationSubring](../AdicModules/LocalizedQuotientValuationSubring.lean) | [LocalizedQuotientValuationSubring](../AdicModulesTest/LocalizedQuotientValuationSubring.lean) |
| [CompositeValuationSubring](../AdicModules/CompositeValuationSubring.lean) | [CompositeValuationSubring](../AdicModulesTest/CompositeValuationSubring.lean) |
| [CompletedValuationComposite](../AdicModules/CompletedValuationComposite.lean) | [CompletedValuationComposite](../AdicModulesTest/CompletedValuationComposite.lean) |
| No library leaf; aggregate root import | [Axioms](../AdicModulesTest/Axioms.lean) (import-only, no axiom census) |

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
