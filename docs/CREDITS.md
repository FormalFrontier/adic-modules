# Contributors, origin and redistribution basis

Authors: Formal Frontier Agents. Original project contributions use the complete
[Apache-2.0 license](../LICENSE). Collective project credit does not identify a
legal copyright holder. The development described here is AI-agent work, not a
claim of human peer review, source-author endorsement or mathematical novelty.

## Original project expression

Anchor authored the original implementation, examples, subsequent readiness
repairs and this assembly. The following exact first-added or substantive
predecessor commits identify the contributions, including their tracked tests;
they are not merely the later merge commits. Library paths have prefix
`AdicModules/`, with corresponding clients under `AdicModulesTest/`.

| Contribution | Original project commit |
| --- | --- |
| `BoundedIdealPowerTorsion.lean`: initial API | `b0bf31a32cb38f3fc33f88c9a7546ffef64d3beb` |
| Finite-module primary-component bridge | `3c51b7c1721c575559ac01d6733352f0ef60758a` |
| `AdicCompletion.lean` | `dcd1f070fd76da0069f842e7b50dee669fb7136e` |
| `ValuationTopology.lean` | `06e9877b808ced212e4b8cfc057aa0475c682cdf` |
| `CompletedIntegers.lean` and comparison support | `e500e52cf69e8bca74e57f241760c7f404e8582c` |
| `CompletedLocalStructure.lean` | `fa297d1de26d7a5ac1f08d36c37c6fa25a6df607` |
| `PrincipalAdicSpectrum.lean` | `fb568363923f7546fb66b697064aac3544e3b1e2` |
| `LocalizedFiltration.lean` | `a92ae259be61c1652bce6ed68fd6140eac737b9b` |
| `LocalizedCompletion.lean` | `8850920be8aca02778d653c53ecd1a1361149db7` |
| `CompositeValuationSubring.lean` | `1930368fb62f2bcc573db07940f2ae00e4f9032d` |
| Nonzero-prime radical containment and its localization use | `bf9353527a55a56994d44ae8969b155aeb24261b` |
| `LocalizedValuationSubring.lean` | `6cbc19e2c2c52662f76303ec0eaa9efd5ef048aa` |
| `LocalizedResidueField.lean` | `8c58ae614c1cd28dd91a3d9be43d100f834d3c6d` |
| `LocalizedQuotientValuationSubring.lean` | `b958925455b66ee4d8265ee9b1e2d3158c9cd943` |
| `CompletedValuationComposite.lean` | `184e198aec1e1a13d1587aac9578fea50548c6b4` |

The initial bounded-torsion expression was adapted from Anchor's earlier
`Research/fk-bounded-ideal-torsion-scratch.lean` in the project source repository
`source-fujiwara-kato-rigid-geometry-i` at
`be699bac931360b69c1205d2f7eece06f6152ac7`. The adaptation changed the scratch
namespace and names, documented the reusable API, made parameter choices explicit,
and extracted the explicit exponent-sum extension lemma. The finite-generation
bridge was added later. The older project research is an expression predecessor,
not just a mathematical citation.

Anchor's valuation-completion design at source-repository revision
`9c9ca1e801631c9fed2fd9b337cda2cb3b5373a7`, file
`Research/fk-valuation-principal-adic-completion-design.md`, guided the later
implementation. Its proposed hypotheses and API sketches are not substituted for
the actual, subsequently generalized Lean statements. Readiness work from
`28f7a10355f0b00f67a5e975458449614cf71369` through
`a590809e4012f98f443edff7a40574aad1108799` adds module visibility, named private
clients, proof-local export compatibility, the default test target and the
completed-integer simp-normalization repair. Earlier development reviews do not
automatically approve these changes or this release assembly.

The new `PrimaryComponent.lean` has an expression predecessor in
`source-nsw`, accepted research revision
`3c76ffd1abb20b0927bbd72ff8ba3dffb2ca8fef`, files
`NSWResearch/Chapter10/PrimaryTorsionExactness.lean` and
`research/chapter-x-primary-torsion-exactness-reuse.md` (original author
expression `b5181f78b7274b9e4fa63de74a85cbc0f86c4f43`). The original
source-research author was Formal Frontier worker-b Task
`hive-request-cc72e29df4ce7c3051bfb029c85e59fec5d3853a`, UID
`8f42012f-5421-46e1-88fa-068ce8e60628`; its fresh worker-a review
approved bounded research, **not** this different library contribution.
The Adic port adds an ordinary-subgroup restricted map and its exactness
transport, and is authored by a distinct Formal Frontier worker-b Task
`hive-request-6f4d01cb68a0c44b2782b550e0c501fe69398e16`, UID
`bf9d73f7-a8e7-4d94-941d-119acd8ca43b`. Exact candidate attribution,
checks and its later independent disposition are recorded by the maintainer;
this credit does not assert review or acceptance of the new work.

Independent Formal Frontier agents reviewed earlier mathematical units; their
exact candidate-specific verdicts remain in the development records. Review is
distinct from code authorship. Historical objects need not belong to a public
release's independent ancestry; this shipped credit preserves their identities.

## Mathematical and upstream references

The mathematical background includes Fujiwara and Kato, *Foundations of Rigid
Geometry I*, [arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5), and classical
module, completion, valuation and localization theory. These are mathematical
references, not permissions to copy protected expression or claims of full source
correspondence. No source PDF, scan, figure or substantial source excerpt is bundled.

The library uses native Lean/mathlib objects and proof infrastructure at the exact
pinned revisions. It does not vendor those dependencies. Their licenses and author
notices remain in their upstream repositories. The source design consulted
`Mathlib/Algebra/Module/Torsion/PrimaryComponent.lean`,
`Mathlib/GroupTheory/Torsion.lean` and `Mathlib/RingTheory/Ideal/Int.lean` at
mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`; the new leaf reuses
their primary-component, Dedekind surjectivity, abelian torsion and integer-ideal
objects rather than copying or replacing upstream implementations. The earlier
design also consulted
mathlib's `Mathlib/RingTheory/LaurentSeries.lean` completion-comparison pattern at
`e37d88a26f3791ed5a93daa1f949af1021b8d103`. That file credits Aaron Anderson,
María Inés de Frutos-Fernández and Filippo A. E. Nuccio, under Apache-2.0, with
copyright (c) 2021 Aaron Anderson. The present completed-integer comparison uses
its own two-variable density argument via `AbstractCompletion.funext`; it does
not copy the Laurent-series extension-homomorphism proof or specialize the
library to rank-one valuations. The reference and upstream credit are retained
without claiming ownership of upstream expression.

## Documentation adapter expression

The bounded Markdown generator and its data tests are adapted from Anchor's
project implementation in `coherent-modules`, exact revision
`1270dfa78e1d60d20ae15841b47be43dcc231287`, paths
`scripts/generate_api.py` and `scripts/test_generate_api.py`, under Apache-2.0.
The module/site inventory, notes, literal-kind controls and recipe are specialized
to this library; the Coherent review does not approve this adaptation. Generated
display headers and docstrings come from this library's pinned native doc-gen4
run. The ten missing-docstring explanations are newly authored API notes, not
source docstrings. The tool is used as a dependency of reproduction, not vendored.

## Standing authorization and scope of review

Formal Frontier's 2026-09-25 standing Apache-2.0 authorization covers verified
original project contributions, including the earlier project research adapted
above. Historical absence of a license file is not itself a license grant.
This assembly adds truthful SPDX/project-author headers without naming an
unverified copyright holder; no existing third-party notice is removed.

The entire final file inventory, generated artifacts and proposed public history
still require independent rights/provenance review. A project label, AI generation,
Git author field or mathematical citation alone does not resolve a concrete
ownership, copying or redistribution concern. Rights review, semantics, complete
proof checking, source coverage and release publication are separate decisions.
