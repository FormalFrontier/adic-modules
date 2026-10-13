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

Rudder authored the bundled submodule-closure theorem and its five applications
in discrete, indiscrete and adic integer topologies. The proof packages
mathlib's existing set-level closure formula through canonical submodule
carriers and reindexes the neighborhood basis along `PLift.down`; it does not
reprove that set-level result or introduce a competing closure construction.

Rudder also authored the integer-span density result and the p-adic basis,
linearity, properness and density chapter, adapting earlier Formal Frontier
p-adic proof developments. The formulations and proofs retain Mathlib's norm
topology, integer module and restricted ideal carriers rather than constructing
new versions of these objects. The top-supremum result and its positive-degree
membership client use the library's generic submodule-closure formula rather
than copying its proof or substituting an arithmetic argument.

## Mathematical and upstream references

The mathematical background includes Fujiwara and Kato, *Foundations of Rigid
Geometry I*, [arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5), and
classical module, completion, valuation and localization theory. These are
mathematical references, not permission to copy protected expression or claims
of complete source correspondence. No source PDF, scan, figure or substantial
source excerpt is bundled.

The submodule-closure theorem is motivated by Fujiwara and Kato,
*Foundations of Rigid Geometry I* (2017), Proposition 7.1.6 and Exercise 0.7.1.
It generalizes the filtered ring-module setting to any submodule neighborhood
basis in a given topological additive group over a semiring with continuous
fixed-scalar actions, without claiming a topology construction from arbitrary
semiring filtrations.

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

The closure proof uses `Filter.HasBasis.iInter_add_right_eq_closure`,
`Submodule.topologicalClosure_coe`, `Submodule.coe_sup`, `Submodule.coe_iInf`,
`Filter.HasBasis.comp_surjective` and `Set.iInter_plift_down`. The relevant
mathlib files credit Johannes Hölzl, Mario Carneiro, Patrick Massot,
Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov,
Frédéric Dupuis, Heather Macbeth, Nathaniel Thomas, Jeremy Avigad,
Kevin Buzzard and Leonardo de Moura. The clients also reuse mathlib's
nonnegative submonoid, integer scalar continuity, linear-topology and adic
filter-basis interfaces; the corresponding files additionally credit
Damiano Testa, Antoine Chambert-Loir, María Inés de Frutos-Fernández and
Anatole Dedecker. In particular, integer fixed-scalar continuity comes from
`AddGroup.continuousConstSMul_int`, not a new scalar-continuity API.
These upstream files are Apache-2.0; their licenses, copyright and author
notices remain upstream, and no upstream proof bodies are copied here.

The p-adic chapter follows Mathlib's p-adic norm and approximation theory by
Robert Y. Lewis, Mario Carneiro and Johan Commelin. Its basis proof combines
`Metric.nhds_basis_closedBall_pow` with
`PadicInt.norm_le_pow_iff_mem_span_pow`; scalar restriction preserves the carrier
through `Submodule.coe_restrictScalars`, and linearity uses
`IsLinearTopology.mk_of_hasBasis`. The ring-level density argument uses
`IsUnit.isHomeomorph_smul`, dense-range composition,
`Submodule.span_singleton_eq_range` and central integer casts. Its p-adic
specialization reuses `PadicInt.denseRange_intCast`, not a copied approximation
proof. Properness follows the existing `PadicInt.inv`, norm-one inverse identity
and faithful integer casts, reducing the obstruction to
`Int.eq_one_or_neg_one_of_mul_eq_one`. The underlying norm, metric, span,
scalar-restriction and continuous-action files additionally credit
Alex Kontorovich, Oliver Nash, Andrew Yang, Robert Y. Lewis and Johan Commelin,
alongside the contributors above. These Mathlib APIs and proof ideas are reused
under their upstream Apache-2.0 notices, which remain upstream. The supremum
consumer also uses `Submodule.dense_iff_topologicalClosure_eq_top`, `iInf_const`
and `iInf_le` to pass from dense closure to the individual neighborhood sums.

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
