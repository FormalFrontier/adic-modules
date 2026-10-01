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
Formal Frontier's NSW source research by a different agent contributor. Its
original research review covered that bounded research, not the Adic library
port. A separate Formal Frontier agent authored the port, which adds restricted
maps on ordinary integer-prime subgroups and transports exactness. These two
contributions and their authorship are distinct.

The restriction-of-scalars equivalence and its ordinary-import client were
originally proved in Formal Frontier's shared incubator by one agent contributor.
A different agent authored their transfer into this library, changing only the
client import and test namespace. The incubator review and checks alone did not
verify the new destination dependency graph. The destination contribution
received separate independent review and configured build and complete
private-inclusive standard-axiom checks before acceptance into development main
on 2026-09-30; its documentation was subsequently accepted into development main.
Neither acceptance is an official successor release or a source-coverage decision.
Review and release decisions are bound to exact artifacts, not automatically
inherited by later documentation changes.

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
The incubator guide credits mathlib contributors Kenny Lau, Judith Ludwig,
Christian Merten, Jiedong Jiang and Nailin Guan for relevant infrastructure;
their upstream Apache-2.0 author and license notices remain in mathlib. This
library asserts no authorship of that upstream expression.

## Documentation adapter expression

The bounded Markdown API generator and its data tests adapt Anchor's earlier
Apache-2.0 project implementation in `coherent-modules`. The module/site
inventory, notes, literal-kind controls and recipe are specialized here; the
earlier project's review does not approve this adaptation. Display headers and
docstrings in the historical API are from this library's pinned native doc-gen
run. The ten missing-docstring explanations are newly authored API notes, not
source docstrings. The tool is used as a dependency of reproduction, not vendored.

## Authorization and review limits

Formal Frontier's 2026-09-25 standing Apache-2.0 authorization covers verified
original project contributions, including the earlier project research adapted
above. A historical missing license file is not itself a license grant. Project
SPDX/author headers do not name an unverified copyright holder; no third-party
notice is removed.

Independent rights/provenance review covers the exact file inventory and public
history considered for a release. A project label, AI generation, Git author field or
mathematical citation alone does not settle a concrete ownership, copying or
redistribution concern. Rights review, semantics, complete proof checking,
source coverage and release publication remain separate decisions.
