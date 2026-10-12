# Contributors, origin and redistribution basis

Authors: Formal Frontier Agents. Original project contributions use the complete
[Apache-2.0 license](../LICENSE). Collective project credit does not identify a
legal copyright holder. This is AI-agent development, not a claim of human peer
review, source-author endorsement or mathematical novelty.

## Original project expression

Anchor authored the original bounded ideal-power torsion API and its finite-module
bridge, the abstract and valuation-ring completion developments, localization,
residue-field and composite-valuation results, examples and subsequent module
readiness repairs. The initial bounded-torsion implementation adapted Anchor's
earlier project source-repository research: it changed the scratch namespace and
names, documented a reusable API, made parameter choices explicit and extracted
an exponent-sum extension lemma. That research is an expression predecessor,
not merely a mathematical citation. Anchor's earlier valuation-completion design
also informed the implementation; its proposed sketches are not substitutes for
the subsequently generalized Lean statements. Later readiness work exposed
public module boundaries, added ordinary-import clients and the default test
target, and repaired proof-local export and simp-normalization issues.

The primary-component exactness contribution has an expression predecessor in
Formal Frontier's NSW source research by a different agent contributor. A separate
Formal Frontier agent authored the library adaptation, which adds restricted maps
on ordinary integer-prime subgroups and transports exactness. These two
contributions and their authorship are distinct.

The restriction-of-scalars equivalence and its ordinary-import client have an
earlier Formal Frontier implementation as their expression predecessor, proved
by one agent contributor. A different agent authored the library adaptation,
changing only the client import and test namespace. The original proof/client
and the library adaptation have distinct authorship.

## Mathematical and upstream references

The mathematical background includes Fujiwara and Kato, *Foundations of Rigid
Geometry I*, [arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5), and
classical module, completion, valuation and localization theory. These are
mathematical references, not permission to copy protected expression or claims
of complete source correspondence. No source PDF, scan, figure or substantial
source excerpt is bundled.

The library uses native Lean and mathlib objects and proof infrastructure at
the pinned revisions and does not vendor those dependencies. Upstream licenses
and author notices remain upstream. The primary-component development reuses
mathlib's Dedekind, abelian torsion and integer-ideal infrastructure. Anchor's
earlier design consulted mathlib's Laurent-series completion comparison, which
credits Aaron Anderson, María Inés de Frutos-Fernández and Filippo A. E. Nuccio
under Apache-2.0 and bears copyright (c) 2021 Aaron Anderson. The present
completed-integer comparison instead uses a two-variable density argument via
`AbstractCompletion.funext`; it does not copy the Laurent-series proof.

The scalar-restriction leaf uses mathlib's native ideal-map/power identity,
`Submodule.Quotient.restrictScalarsEquiv`, `Submodule.quotEquivOfEq` and
`AdicCompletion` inverse-limit interfaces rather than copying their proofs.
The original scalar-restriction guide credits mathlib contributors Kenny Lau,
Judith Ludwig, Christian Merten, Jiedong Jiang and Nailin Guan for relevant
infrastructure; their upstream Apache-2.0 author and license notices remain in
mathlib. This library asserts no authorship of that upstream expression.

## Documentation adapter expression

The bounded Markdown API generator and its data tests adapt Anchor's earlier
Apache-2.0 project implementation in `coherent-modules`. The module/site
inventory, notes, literal-kind controls and recipe are specialized here. Display
headers and 92 rendered source docstrings in the historical API are from this
library's pinned native doc-gen run. One further original native docstring is
verified but presented as a separately authored, labeled editorial API note.
The ten missing-docstring explanations are also authored API notes, not source
docstrings. The editorial presentation does not claim a new native run. The tool
is used as a dependency of reproduction, not vendored.

## Authorization and review limits

Formal Frontier's standing Apache-2.0 authorization covers verified
original project contributions, including the earlier project research adapted
above. A historical missing license file is not itself a license grant. Project
SPDX/author headers do not name an unverified copyright holder; no third-party
notice is removed.

Independent rights/provenance assessments are specific to the files and public
history examined. A project label, AI generation, Git author field or mathematical
citation alone does not settle a concrete ownership, copying or redistribution
concern. Rights/provenance, mathematical correctness, complete proof checking
and source coverage are distinct matters.
