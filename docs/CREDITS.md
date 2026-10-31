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
rational-module calculations. The original span and closure calculations
are independent of the comparison theorem; the real model also includes an
additional private application of
`Submodule.closure_span_eq_of_dense_subsemiring` to the rational axis, identifying
its proper closure and excluding the second coordinate unit.

The multivariate polynomial value-association theorem and its two-coordinate
`ZMod 64` example are original Formal Frontier Agent expression. The proof uses
Mathlib's quotient congruence, support-local evaluation-congruence and multivariate
evaluation-composition APIs, then applies the library's scalar polynomial
value-association theorem to `X`; it does not reproduce that theorem's
Jacobson-radical argument. The example uses stock ideal-radical and Jacobson-radical
APIs to place the nilpotent generator in the Jacobson radical.

## Mathematical and upstream references

The mathematical background includes Fujiwara and Kato, *Foundations of Rigid
Geometry I*, [arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5), and
classical module, completion, valuation and localization theory. These are
mathematical references, not permission to copy protected expression or claims
of complete source correspondence. No source PDF, scan, figure or substantial
source excerpt is bundled.

The Henselian-pair developments cite the Stacks Project Authors,
*The Stacks Project*: the finite-algebra idempotent and étale-point criteria
([Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)), integral transport
([Tag 09XK](https://stacks.math.columbia.edu/tag/09XK)), nested ideals
([Tag 0DYD](https://stacks.math.columbia.edu/tag/0DYD)), nil ideals
([Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)), and finite algebras over
Henselian local rings ([Tag 04GE](https://stacks.math.columbia.edu/tag/04GE)).
The étale-point condition in Tag 09XI asserts existence; this library derives
uniqueness separately using rigidity of étale sections. The idempotent-lifting
module also cites Hideyuki Matsumura, *Commutative Ring Theory*, Theorem 2.1
(Cayley–Hamilton), whose finite-module interface is supplied by Mathlib.
The endomorphism unit-reflection argument uses Mathlib's formalizations of
Nakayama's lemma ([Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV))
and Orzech's theorem: M. Orzech, *Onto endomorphisms are isomorphisms*,
American Mathematical Monthly 78 (1971), 357–362.

The split-kernel completion comparison in
[`AdicCompletion.Kernel`](../AdicModules/AdicCompletion/Kernel.lean) uses a
projector on the original modules, following the approach in Formal Frontier Agents'
[Projective Modules](https://github.com/FormalFrontier/projective-modules) and
[Stable Range](https://github.com/FormalFrontier/stable-range) formalizations,
including contributions by Prism and Iris. It combines Mathlib's completion
interfaces by Kenny Lau, Judith Ludwig, Christian Merten and Jiedong Jiang,
Antoine Chambert-Loir's exact-sequence splitting, and the submodule-equivalence
API by Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov,
Frédéric Dupuis and Heather Macbeth. Projective Modules and Stable Range are
construction references here, not package dependencies.

The finite-first-quotient tensor comparison reuses this library's chosen-original-lifts
spanning theorem and Mathlib's canonical completed-ring action and tensor comparison
(Judith Ludwig and Christian Merten). Finite quotient generators use Johan Commelin's
finiteness API; the chosen-family argument uses Johannes Hölzl's finite linear-combination
API. Completed projectivity uses Kevin Buzzard and Antoine Labelle's projective base-change
and splitting API, Johan Commelin's finite-projective splitting theorem, and Andrew Yang's
noncommutative idempotent lifting. The flat-quotient argument also uses Nailin Guan's
flat-target kernel-intersection theorem, Christian Merten's flat base-change formalization,
and the quotient–tensor equivalence by Antoine Chambert-Loir and Jujian Zhang. The explicit
completed-module finite-presentation theorem uses
Andrew Yang's `Module.finitePresentation_of_projective`. These are arbitrary-ideal raw
inverse-limit results, not the whole intrinsic-completion assertion of Fujiwara–Kato,
Proposition 7.2.16, which has a finitely generated ideal setting. The comparison and
finite-original Mathlib surjectivity declarations, author notices and licenses are preserved.

The precomplete-base bridges combine that same finite-first-quotient comparison
with Mathlib's canonical-map surjectivity and completeness criteria. Coefficient
lifting uses Antoine Chambert-Loir's `LinearMap.rTensor_surjective` and Kenny Lau
and Mario Carneiro's tensor left unitor. Finiteness uses Johan Commelin's quotient,
scalar-tower, surjective-image and linear-equivalence transport API. Original-module
projectivity over a complete base uses Kevin Buzzard and Antoine Labelle's semilinear
projectivity transport and lifting API. The finite-module argument combines the
split-kernel range formula with Chris Hughes's finite Nakayama theorem; the flat
specialization reuses quotient base change. These are compositions of existing
interfaces, without copying their proof bodies or giving original modules a
completed-ring action; upstream notices remain in Mathlib.

The Noetherian complete-module flatness criterion combines the standard
Artin–Rees lemma with the equational criterion for flatness
([Stacks Project, Tag 00HK](https://stacks.math.columbia.edu/tag/00HK)). It uses
Andrew Yang's Artin–Rees formalization, the flatness API of Johan Commelin,
Jujian Zhang and Yongle Hu, Mitchell Lee and Junyan Xu's equational criterion,
and Antoine Chambert-Loir's tensor right-exactness API. Finite-product tensor
coordinates and intrinsic completeness reuse the formalizations of Judith Ludwig
and Christian Merten and this library's ideal-action and product-completeness APIs.
The uniform-estimate and successive-correction proof is independently assembled
Formal Frontier Agent expression, without copying upstream proof bodies.

Tiller authored the raw-completion flatness criterion over a Noetherian completed
coefficient ring and its flat-original-module specialization. These compose that
complete-module criterion with this library's Noetherian-completion cotangent
finiteness, intrinsic completeness, semilinear quotient comparisons and forward
quotient descent. Flatness is transported through the given coefficient and module
equivalences by `Module.Flat.of_semilinearEquiv` from Formal Frontier Agents'
[Coherent Modules](https://github.com/FormalFrontier/coherent-modules/blob/4d5340c7f78895f2be6fb9f2ec183443ecf5497c/CoherentModules/RingTheory/Flat/Equiv.lean),
retaining both canonical quotient actions. The original-flat specialization uses
this library's quotient flatness theorem, whose Mathlib base-change and
quotient–tensor formalizations are credited above. No upstream proof body is
copied, and the upstream author and Apache-2.0 notices remain in their libraries.

The complete-base conormal criteria use Andrew Yang's canonical ideal cotangent
module and quotient map in Mathlib, together with Johan Commelin's finite-module
transport API. The injective-map Hausdorff argument uses Mathlib's adic
Hausdorff predicate and Kenny Lau's submodule congruence and mapping APIs.
The Noetherian equivalence applies this library's finitely generated ideal
criterion, following the mathematical criterion in K. Fujiwara and F. Kato,
*Foundations of Rigid Geometry I*, arXiv:1308.4734v5.

The finite-cotangent quotient comparisons reuse this library's evaluation kernels
and class-preserving restriction-of-scalars equivalence, with Mathlib's completed
coefficient actions and evaluation formalized by Kenny Lau, Judith Ludwig,
Christian Merten and Jiedong Jiang, and Andrew Yang's ideal cotangent module.
The coefficient and module comparisons share the equal-ideal/equal-submodule
quotient and surjective first-isomorphism constructions. These use the quotient
formalizations by Kenny Lau, Chris Hughes, Mario Carneiro, Anne Baanen and Patrick
Massot, and the submodule quotient and linear isomorphism APIs by Johannes Hölzl,
Mario Carneiro, Kevin Buzzard and Yury Kudryashov. The quotient coefficient action
is Pierre-Alexandre Bazin's. The semilinear construction follows this library's
Chinese remainder inverse-pair pattern, using Mathlib's equivalence and
inverse-pair APIs by Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl,
Mario Carneiro, Anne Baanen, Frédéric Dupuis and Heather Macbeth. Extension from
original residues uses this library's descent along surjective semilinear maps,
with its existing additive-monoid target interface. These are compositions of
existing interfaces, not copied upstream proof bodies; their author,
copyright and Apache-2.0 notices remain in Mathlib.

The tensor-comparison kernel calculation reuses this library's coefficient quotient
comparison and fixed-stage kernel theorem, whose finite-linear-combination argument follows
Bingyu Xia's Mathlib formalization. It composes `quotTensorEquivQuotSMul` from Antoine
Chambert-Loir and Jujian Zhang's `LinearAlgebra/TensorProduct/Quotient.lean`,
`cancelBaseChange` from Kim Morrison, Johan Commelin and Eric Wieser's
`LinearAlgebra/TensorProduct/Tower.lean`, and the coefficient comparison at cofinal
multiples of the specified positive exponent. It identifies evaluation after the same
canonical tensor comparison, without rebuilding tensor right exactness. The quotient
equivalence uses Mathlib's existing Hausdorffification from Kenny Lau, Judith Ludwig,
Christian Merten and Jiedong Jiang's adic-completion Basic module, together with the
first isomorphism theorem from Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury
Kudryashov's `LinearAlgebra/Isomorphisms.lean`. Their Apache-2.0 notices remain upstream;
these interfaces and formalization approaches are reused without copying their proofs.

The valuation-integers completeness bridge is motivated by I. Fesenko and
S. Vostokov, *Local Fields and Their Extensions*, second edition (2002),
II §1, Corollary 1. It independently assembles Mathlib's valuation-integers,
`WithVal`, closed-range completeness and adic-topology APIs with this library's
principal-adic topology comparison and uniform-inducing fraction-field map.
It is not a formalization of factor lifting. The relevant Mathlib files credit
Adam Topaz, Salvatore Mercuri, Patrick Massot, Johannes Hölzl, Sébastien Gouëzel
and Andrew Yang. The p-adic and discrete-valuation examples additionally reuse
Mathlib's developments by Robert Y. Lewis, Mario Carneiro, Johan Commelin,
Kevin Buzzard, María Inés de Frutos-Fernández and Filippo A. E. Nuccio.
Their upstream author and license notices remain in Mathlib.

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
The Witt-vector unit proofs reuse `WittVector.mkUnit` and `coe_mkUnit` from
Mathlib's `RingTheory/WittVector/DiscreteValuationRing.lean` (Robert Y. Lewis,
Heather Macbeth and Johan Commelin), `constantCoeff` from
`RingTheory/WittVector/Basic.lean` (Johan Commelin and Robert Y. Lewis), and
`isUnit_iff_ne_zero` from `Algebra/GroupWithZero/Units/Basic.lean` (Johan Commelin).
The locality equivalence combines the unit criterion with
`constantCoeff_surjective` from `RingTheory/WittVector/Teichmuller.lean`
(Johan Commelin) and `IsLocalRing.of_surjective'`,
`IsLocalRing.of_isUnit_or_isUnit_one_sub_self` and
`IsLocalRing.isUnit_or_isUnit_one_sub_self` from `RingTheory/LocalRing/Basic.lean`
(Kenny Lau, Chris Hughes and Mario Carneiro). These are reused constructors and
criteria, not a copied Witt-vector locality proof; their upstream notices remain
in Mathlib.

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

The Witt-vector reducedness equivalence reuses Mathlib's
`RingTheory/WittVector/Teichmuller.lean` (Johan Commelin) for the
multiplicative Teichmüller lift reflecting reducedness to the coefficient ring,
`RingTheory/WittVector/Domain.lean` (Robert Y. Lewis) for the domain instance in
characteristic `p`, and `RingTheory/WittVector/Basic.lean` (Johan Commelin and
Robert Y. Lewis) for `WittVector.ghostEquiv` when `p` is invertible.
`RingTheory/Nilpotent/Lemmas.lean` (Oliver Nash) supplies
`nilpotent_iff_mem_prime`, the all-prime-ideal nilpotence test. The proof here
combines the two field cases through fraction fields of prime quotients and
uses that test to make each coefficient nilpotent, hence zero over a reduced
coefficient ring. Their author and Apache-2.0 notices remain in Mathlib.

The flat-last-module completion theorem reuses
`LinearMap.ker_inf_smul_top_eq_smul_of_flat`, formalized by Nailin Guan in
Mathlib's `RingTheory/Smooth/Quotient.lean`, together with the library's
range-cofinality exactness theorem. The latter follows the adic Cauchy-sequence
argument of Judith Ludwig and Christian Merten. Flatness is transported along
Mathlib's original linear quotient equivalence; the kernel-intersection proof
is used through its existing API, not copied. Upstream author, copyright and
Apache-2.0 notices remain in Mathlib.

## Other deliverable interfaces

The completion-coordinate comparison reuses the quotient-torsion equivalence
from [Group Theory](https://github.com/FormalFrontier/group-theory); the adic
compactness criterion reuses its subgroup-basis total-boundedness theorem.

Strong Hensel lifting for finite polynomial systems reuses
`MvPolynomial.eval₂_sub_eval₂_sub_sum_pderiv_mem_sq`, the first-order Taylor
remainder theorem from
[Multivariate Polynomials](https://github.com/FormalFrontier/multivariate-polynomials).
It is used through the released `MultivariatePolynomials.Taylor` interface,
not by vendoring its proof text.

[Coherent Modules](https://github.com/FormalFrontier/coherent-modules) is also a
direct dependency: the raw-completion flatness criterion imports its focused
`CoherentModules.RingTheory.Flat.Equiv` interface for semilinear flatness transport.
The same package is reached through Multivariate Polynomials; one explicit root
pin selects the shared revision. The resolved package graph also includes
[Algebraic Direct Limits](https://github.com/FormalFrontier/algebraic-direct-limits)
through Multivariate Polynomials, as a transitive package dependency rather than
a directly imported proof source here. Exact public release pins are recorded
in [lake-manifest.json](../lake-manifest.json); upstream licensing and contributor
notices remain in those libraries.

## Fibres and submodules under completed scalars

The fibre-stability and separated-quotient span results reuse the library's
`AdicCompletion.ext_of_fg_pow` uniqueness theorem and Mathlib's existing completed ring,
`LinearMap.smulRight`, quotient projection and span induction. The completion
formalizations credit Kenny Lau, Judith Ludwig, Christian Merten and Jiedong
Jiang. The scalar-orbit provider in `Mathlib.Algebra.Module.LinearMap.End`
credits Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro,
Anne Baanen, Frédéric Dupuis and Heather Macbeth. The quotient and span
formalizations credit Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury
Kudryashov, with Frédéric Dupuis and Heather Macbeth additionally credited for
span. Their upstream Apache-2.0 author, copyright and license notices remain in
Mathlib. These results assemble those APIs without copying their proofs or
introducing new scalar actions.

Positive-power uniqueness reuses the fixed-stage kernel theorem in this library,
whose finite-linear-combination proof follows Bingyu Xia's Mathlib formalization,
and Mathlib's `Ideal.FG.pow` and `IsHausdorff.StrictMono.funext`. Automatic
completed-scalar linearity uses that uniqueness theorem on the given scalar-orbit
maps; its Hom equivalence uses Mathlib's `LinearMap.restrictScalarsₗ` and the
pointwise target action. The retraction law uses scalar-restriction injectivity
and retains the specified original retraction. These arguments generalize the
finitely generated ideal API without copying the finite-stage proof. The
Mathlib completion and linear-map author credits above apply; upstream
Apache-2.0 notices remain unchanged.

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

## Scalar-ideal quotients and the matrix example

The scalar-ideal quotient construction follows Mathlib's ideal/submodule
additive-carrier design and its two-sided quotient ring and algebra constructors.
It reuses `Submodule.smul_top_le_comap_smul_top`, `LinearMap.mulLeft` and
`LinearMap.mulRight` for multiplication stability, and `Ideal.Quotient.ring`,
`Ideal.Quotient.algebra` and `Ideal.Quotient.mkₐ` for the quotient structures
and map, retaining the submodule quotient's additive group, module action and
`Submodule.mkQ` projection. The ideal and ideal-quotient files credit Kenny Lau,
Chris Hughes, Mario Carneiro, Anne Baanen and Patrick Massot; the submodule and
linear-map foundations additionally credit Nathaniel Thomas, Jeremy Avigad,
Johannes Hölzl, Frédéric Dupuis and Heather Macbeth. The algebra foundations
credit Kenny Lau and Yury Kudryashov. The submodule-quotient formalization in
`Mathlib.LinearAlgebra.Quotient.Defs` and `.Basic` credits Johannes Hölzl,
Mario Carneiro, Kevin Buzzard and Yury Kudryashov.

The integer-matrix example follows Mathlib's matrix-unit multiplication and
bottom-submodule quotient approach: `Matrix.single_mul_single_same` separates
`E₀₁ * E₁₀` from `E₁₀ * E₀₁`, and `Submodule.quotEquivOfEqBot` recovers the
representatives through the same submodule projection. The commutator uses the
canonical integer scalar action. `Mathlib.Data.Matrix.Basis` credits Jalex Stark,
Kim Morrison, Eric Wieser, Oliver Nash and Wen Yang; the matrix multiplication
and algebra files credit Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro,
Johan Commelin and Lu-Ming Zhang. These credits include formalization approaches
followed as well as interfaces reused. Their upstream Apache-2.0 licenses,
copyright notices and author notices remain in Mathlib; this library claims no
authorship of that upstream expression.

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

## Flat-target inverse criteria and quotient transport

The original-map inverse criterion combines this library's completed-map
injectivity and reflection theorems with Judith Ludwig and Christian Merten's
Mathlib first-quotient surjectivity criteria. The positive stages use the
nilpotent flat-target criterion, whose kernel-intersection step is Nailin Guan's
Mathlib formalization. Quotient flatness uses Christian Merten's flat base change,
Antoine Chambert-Loir and Jujian Zhang's quotient–tensor equivalence, and Kenny Lau
and Yury Kudryashov's scalar extension along a surjective algebra map.
Nested quotient transport uses the quotient-ring action formalized by
Pierre-Alexandre Bazin and the submodule quotient and third isomorphism APIs by
Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov. The additive
square and ideal-image kernel arguments are shared with the tensor-product
projectivity criteria.
