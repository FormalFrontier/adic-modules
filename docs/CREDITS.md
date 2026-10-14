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

Rudder also authored the unital cyclic-ring integer-cast bridge, its singleton-span
consequences and integer, cyclic-quotient and matrix clients. The proof evaluates
mathlib's existing cyclic additive-endomorphism theorem on right multiplication
at `1`, then uses the existing singleton-span eliminator and contraposition.
It does not copy or reimplement the cyclic-endomorphism proof, introduce a new
integer action or assert that this bridge is a theorem from the source book.

Rudder also authored the integer-span density result and the p-adic basis,
linearity, properness and density chapter, adapting earlier Formal Frontier
p-adic proof developments. The formulations and proofs retain Mathlib's norm
topology, integer module and restricted ideal carriers rather than constructing
new versions of these objects. The top-supremum result and its positive-degree
membership client use the library's generic submodule-closure formula rather
than copying its proof or substituting an arithmetic argument.

The dense-subsemiring span-comparison statement, its proof and all five model
source files are original Formal Frontier Agent expression: rational-axis and
integer-line, discrete-line and mixed-axis, p-adic singleton,
empty/zero/subsingleton and indiscrete self-module, and independent discrete
rational-module calculations. No complete transitive standard-axiom assurance
is claimed for these span sources. The original span and closure calculations
are independent of the comparison theorem; the real model also includes an
additional private application of
`Submodule.closure_span_eq_of_dense_subsemiring` to the rational axis, identifying
its proper closure and excluding the second coordinate unit.

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

The integer-span proofs reuse `AddMonoidHom.map_addCyclic`, generated additively
from `MonoidHom.map_cyclic`, `AddMonoidHom.mulRight`, `Int.smul_one_eq_cast`,
`AddCommGroup.toIntModule` and `Submodule.span_singleton_eq_top_iff`.
The relevant cyclic-group files credit Johannes Hölzl; the ring file credits
Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov and
Neil Strickland. The integer-module file credits Nathaniel Thomas, Jeremy
Avigad, Johannes Hölzl and Mario Carneiro. The singleton-span file credits
Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis
and Heather Macbeth. The cyclic-class definitions
credit Jeremy Avigad, Leonardo de Moura, Simon Hudon and Mario Carneiro, and the
integer-cast interfaces credit Mario Carneiro and Gabriel Ebner.

The integer-span clients reuse `ZMod.intCast_surjective`, maintained cyclic
instances, integer-unit lemmas and matrix-unit, diagonal-cast and multiplication
interfaces. The corresponding ZMod file credits Chris Hughes, and the
integer-unit file credits Jeremy Avigad. The matrix-unit file credits
Jalex Stark, Kim Morrison, Eric Wieser, Oliver Nash and Wen Yang; the diagonal
and multiplication files credit Ellen Arlt, Blair Shi, Sean Leather,
Mario Carneiro, Johan Commelin and Lu-Ming Zhang. These mathlib files are
Apache-2.0, with their original licenses, copyright and author notices retained
upstream. This library reuses their interfaces and formalization approach,
without copying upstream proof bodies or claiming authorship of them.

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

`Submodule.closure_span_eq_of_dense_subsemiring` uses Mathlib's canonical
subsemiring restriction of scalar actions through `Subsemiring.module` and
`Subsemiring.smul_def`. Its proof takes
`AddSubmonoid.topologicalClosure` of the additive carrier of the restricted span,
using `AddSubmonoid.coe_topologicalClosure` and `Submodule.coe_toAddSubmonoid`.
`Continuous.range_subset_closure_image_dense` puts every scalar multiple of each
selected generator in this closure. `Submodule.span_induction`, strengthened to
assert membership for every scalar multiple, then handles the full `R`-span
without extending the coefficient-continuity hypothesis to all module elements.
`Submodule.span_subset_span` supplies the reverse inclusion. The comparison
combines these existing APIs rather than copying their proofs; the span and
closure infrastructure and its contributors are credited above.
The real and discrete-module models reuse
`Submodule.mem_span_singleton`, `Submodule.span_singleton_eq_range`,
`Rat.denseRange_cast`, `Continuous.range_subset_closure_image_dense`, coordinate
and product continuity, `irrational_sqrt_two` and
`Int.isClosedEmbedding_coe_real`. The canonical Pi and Prod module developments
credit Simon Hudon, Patrick Massot and Eric Wieser; rational-density development
credits Yury Kudryashov; the irrational-real development credits Mario Carneiro,
Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne and Yury Kudryashov; the integer
embedding development credits Johannes Hölzl and Mario Carneiro. Singleton-span
and closure infrastructure is credited above. These interfaces and formalization
approaches are reused under Mathlib's upstream Apache-2.0 notices, which remain
upstream; no upstream proof bodies are copied into the model files.

The p-adic singleton models follow the stock continuous-image approach through
`closure_image_closure`, `DenseRange.closure_range`,
`Submodule.span_singleton_eq_range`, `Set.range_comp`, `Set.image_univ` and
`Int.cast_smul_eq_zsmul`, with the canonical integer action and subsemiring
restriction. Unit density and ideal-power neighborhoods use the existing p-adic
chapter; the nonunit ideal uses Mathlib's norm/ideal carrier identity and closed
norm sublevels. The p-adic approximation, norm and ideal formalizations by
Robert Y. Lewis, Mario Carneiro and Johan Commelin are credited above. The
empty/zero/subsingleton calculations and non-T1 rational self-module controls
use Mathlib's span and indiscrete-topology APIs. The independent discrete
rational module uses Kim Morrison's canonical `ULift.module'` action and the
transport described by `ULift.moduleEquiv`, not a new module structure or a
change to the scalar topology. Continuous-image closure infrastructure credits
Johannes Hölzl, Mario Carneiro and Jeremy Avigad; singleton-span and integer-module
contributors are credited above. These mathematical ideas, formalization
approaches and interfaces are reused, not their upstream proof bodies. Their
Apache-2.0 copyright, author and license notices remain upstream. Mathematical
credit is distinct from the redistribution basis for original project expression;
no additional third-party source text, assets or figures are bundled.

## Comaximal powers and finite Chinese remainders

The comaximal-powers development uses Mathlib's left-ideal and power APIs in
`Mathlib.RingTheory.Ideal.Operations`, credited to Kenny Lau, and Neil
Strickland's geometric-sum formalization in `Mathlib.Algebra.Ring.GeomSum`.
Its subtraction-free recurrence works for arbitrary semiring left ideals;
the independent-power pairwise guard applies it twice. The two private
specializations retain the respective two-sided hypotheses of Mathlib's
`Ideal.sup_pow_eq_top` and `Ideal.sup_pow_eq_top'`.

The finite-selector proof adapts Mathlib's
`Ideal.quotientInfToPiQuotient_surj` from
`Mathlib.RingTheory.Ideal.Quotient.Operations`, using
`Ideal.sup_iInf_eq_top` from the ideal operations module. The finite-quotient
module retains Kenny Lau's 2018 copyright notice, the Apache-2.0 license
notice and author credit to Kenny Lau, Patrick Massot and Formal Frontier
Agents. It reuses Mathlib's actual `Ideal.quotientInfToPiQuotient`, quotient
formulas and injectivity, quotient factors, `Ideal.pow_sup_pow_eq_top` and
commutative `Ideal.quotientInfRingEquivPiQuotient`, rather than introducing
replacement quotients or a different canonical map.

The inverse and representative criteria, common-ring scalar bridge,
linear-equivalence definition and inclusion/precision squares build on those
same objects. The linear definition uses the ring equivalence's existing
`toAddEquiv.toLinearEquiv` and the canonical quotient/Pi module actions.
Their integer examples reuse Mathlib's principal-ideal, congruence and finite
calculation APIs. See the [finite-quotient guide](FiniteQuotient.md) for the
mathematical scope and the distinction between ring CRT and arbitrary
left-ideal module diagonals. These reuse and adaptation credits supplement,
not replace, the upstream and project author notices above.

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
