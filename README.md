# adic-modules

Authors: Formal Frontier Agents

Lean results on ideal-power torsion, inverse-limit adic completions, integer
singleton spans in unital rings, submodule closure from neighborhood bases,
proper dense integer spans in p-adic integers and valuation rings. It also
contains comaximal-power and powers-topology density theorems for arbitrary
left ideals, with integer, matrix-ring, matrix-semiring and boundary models;
and a dense-subsemiring span-closure comparison with real, discrete, p-adic
and degenerate-boundary models. The models retain their independent original
calculations, alongside additional private applications to integer ideal density,
natural-matrix comaximal powers and real rational-axis closure.
Import `AdicModules` for
the public library or an individual module for a narrower dependency. The library builds on Lean, mathlib's native ideals and
adic completion, and the pinned dependencies in this repository; it does not
require source-research records to use its mathematical API.

## Headline results

- **Bounded torsion and primary components.**
  [`Module.IsKilledByIdealPower R M I`](AdicModules/BoundedIdealPowerTorsion.lean)
  means *one* exponent of `I` annihilates the entire module. Its basic
  submodule and surjective-image results work over a commutative semiring and
  an additive commutative monoid; quotients and extensions have their stated
  commutative-ring/additive-group hypotheses. Over a commutative ring,
  [`isKilledByIdealPower_iff_primaryComponent_eq_top`](AdicModules/BoundedIdealPowerTorsion.lean)
  identifies this uniform condition with the entire elementwise primary
  component **when `Module.Finite R M` holds** (finite generation, not a
  finite underlying set). Separately,
  [`Ideal.primaryComponent.exact`](AdicModules/PrimaryComponent.lean) preserves
  an exact pair at a Dedekind-domain height-one prime if its **source** is
  torsion; neither finiteness nor a uniform exponent nor torsion of the middle
  or target is assumed. For abelian groups,
  [`AddCommGroup.primaryComponent.exact`](AdicModules/PrimaryComponent.lean)
  gives exactness of the actual restricted homomorphisms on ordinary
  `p`-primary subgroups, again with a torsion source. See the
  [primary-component supplement](docs/PrimaryComponent.md).

- **Adic completions and restricting scalars.**
  [`AdicCompletion.abstractCompletion`](AdicModules/AdicCompletion.lean) packages
  the native inverse limit as an `AbstractCompletion` for a *commutative ring*
  equipped with a compatible uniform additive-group structure, an ideal
  satisfying `IsAdic I`, and `I.FG`. It does not give an unconditional
  completion of any ring. A different result,
  [`AdicCompletion.restrictScalarsEquiv`](AdicModules/AdicCompletion/RestrictScalars.lean),
  compares completions for **any** `I : Ideal R` when `R` and `S` are
  commutative rings, `S` is an `R`-algebra, and the additive commutative group
  `M` carries compatible `R`- and `S`-module structures with
  `IsScalarTower R S M`:

  ```lean
  AdicCompletion.restrictScalarsEquiv I M :
    AdicCompletion (I.map (algebraMap R S)) M ≃ₗ[R] AdicCompletion I M
  ```

  The map goes **from the extended-ideal `S` completion to the `R`
  completion**, and is `R`-linear, not a tensor/base-change theorem. Its
  [level-quotient comparison](AdicModules/AdicCompletion/RestrictScalars.lean)
  and transition, evaluation and canonical-`of` identities work in both
  directions, including level zero and the bottom and top ideals. No finite
  generation, flatness, separatedness or completeness-predicate hypothesis is
  needed for this comparison; these are not assertions about the distinct
  `AbstractCompletion` construction.

- **Integer singleton spans in unital rings.**
  [`IsAddCyclic.intCast_surjective`](AdicModules/Algebra/Module/Int.lean)
  gives surjective integer casts for an additively cyclic `NonAssocRing R`.
  [`Submodule.intCast_surjective_of_span_singleton_eq_top`](AdicModules/Algebra/Module/Int.lean)
  gives the same conclusion when `Submodule.span ℤ ({x} : Set R) = ⊤`, using
  the canonical integer action induced by the additive group. Consequently,
  [`Submodule.int_span_singleton_ne_top_of_not_surjective_intCast`](AdicModules/Algebra/Module/Int.lean)
  makes **every** singleton integer span proper when integer casts are not
  surjective. No multiplication associativity, commutativity, characteristic-zero,
  nontriviality or topology hypothesis is needed. The
  [clients](AdicModulesTest/Algebra/Module/Int.lean) include integers, every
  `ZMod n` including `n = 0` and `n = 1`, and noncommutative two-by-two integer
  matrices. Properness of a particular span does not imply nonsurjectivity of
  casts: the span of `2` in `ℤ` is proper although its integer casts are onto.

- **Submodule closure from a neighborhood basis.**
  [`Submodule.topologicalClosure_eq_iInf_sup`](AdicModules/Topology/Algebra/Submodule.lean)
  identifies `N.topologicalClosure` with `⨅ i, ⨅ (_ : p i), N ⊔ U i` when
  the active submodules `U i` form a basis of neighborhoods of zero. It applies
  over a semiring `R` to an additive commutative group `M` with an `R`-module
  structure, a **given compatible topological additive-group structure**, and
  continuous multiplication by each fixed scalar. Scalar, module and
  `Sort`-valued index universes are independent. No scalar topology, joint
  scalar continuity, Hausdorffness, countability or closedness assumption is
  needed; this does **not** construct a topology from arbitrary semiring
  submodule filtrations. The [clients](AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean)
  compute discrete and indiscrete closures and specialize to canonical
  `(2)`-adic powers, including proposition indices and an active `Bool` predicate.

- **Comaximal powers of left ideals and density in powers topologies.**
  [`Ideal.sup_pow_eq_top_of_sup_eq_top`](AdicModules/RingTheory/Ideal/Operations.lean)
  has a written proof of
  `∀ {R : Type u} [Semiring R] {J I : Ideal R} {n : ℕ}, J ⊔ I = ⊤ → J ⊔ I ^ n = ⊤`.
  It applies to arbitrary left ideals in every semiring, including
  noncommutative semirings without additive inverses or multiplication
  cancellation. Neither ideal must be two-sided; every natural exponent,
  including zero, is covered. Powers are whole ideal powers in the original
  semiring, not spans of powers of chosen generators. Two private
  specializations recover Mathlib's comaximal-power conclusions under their
  respective two-sidedness hypotheses. See the
  [comaximal-powers guide](docs/Guide.md#comaximal-powers-of-left-ideals)
  for the application API and subtraction-free recurrence.
  Separately,
  [`Ideal.dense_iff_sup_eq_top_of_hasBasis`](AdicModules/Topology/Algebra/Ideal.lean)
  states `Dense (J : Set R) ↔ J ⊔ I = ⊤` for a ring with a given compatible
  additive-group topology whose zero neighborhoods have basis `I ^ n`.
  Neither ideal must be two-sided; no continuity of ring multiplication or
  of the ring scalar action is assumed. Its written proof translates the
  powers basis to each ring element and tests closure by intersection with
  these translated neighborhoods, using all-power comaximality. The topology
  is the same supplied topology, not one constructed from an arbitrary filtration.
  Independently, the [integer model](AdicModulesTest/Topology/Algebra/Ideal/Int.lean)
  contains four private proof terms for nonzero properness of
  `Ideal.span {(3 : ℤ)}`, comaximality with every power of `(2)`, representation
  of every residue modulo `2 ^ n`, and density in the original integers with
  `(Ideal.span {(2 : ℤ)}).adicTopology`. These use neither the general density
  criterion nor the default discrete topology.
  The [integer-matrix model](AdicModulesTest/Topology/Algebra/Ideal/Matrix.lean)
  treats nonzero proper, non-two-sided column ideals in `M₂(ℤ)`: the induced
  second-column topology gives an ideal-power basis and a proper dense ideal
  that is not closed, in a non-Hausdorff topology with discontinuous right
  multiplication. The [natural-matrix model](AdicModulesTest/RingTheory/Ideal/Operations/MatrixNat.lean)
  gives semiring column membership, comaximality and all-power calculations
  without commutativity, additive inverses or multiplication cancellation.
  Its elementary matrix units do not commute and are not invertible; `E01² = 0`
  but `(Ideal.span {E01})²` contains nonzero `E11`, so ideal powers cannot be
  replaced by spans of generator powers. The [boundary models](AdicModulesTest/Topology/Algebra/Ideal/Boundary.lean)
  distinguish discrete and `(2)`-adic integers, top/indiscrete and
  bottom/discrete bases, zeroth and first powers, and subsingleton rings.
  All four model files retain direct calculations that do not invoke the general
  density criterion. The integer file also applies that criterion to `(3)` in
  the `(2)`-adic topology, and the natural-matrix file applies the comaximal-powers
  theorem to its column ideals. See the
  [model guide](docs/Guide.md#matrix-left-ideal-models).

- **P-adic neighborhood bases and proper dense integer spans.**
  The [p-adic module](AdicModules/Topology/Algebra/PadicInt.lean) uses the usual
  norm topology on `ℤ_[p]`, with `p` prime. The ideals generated by `p ^ n`
  form a basis at zero, including `n = 0`; restricting their scalars to `ℤ`
  preserves all p-adic multiples. This topology is linear both for self-scalars
  and for integer scalars, without adding global instances.
  [`Submodule.dense_int_span_of_isUnit_of_denseRange_intCast`](AdicModules/Topology/Algebra/Submodule.lean)
  works in any ring with dense integer casts and continuous multiplication by
  each fixed ring element: the integer span of a unit is dense. Its p-adic
  specializations give density for units and integer generators not divisible
  by `p`. In contrast, every integer generator has a **proper** integer span,
  including `0` and `±1`. In `ℤ_[2]`, the integer span of `3` is proper and
  dense but excludes `1`.
  [`PadicInt.int_span_three_two_proper_sup_pow`](AdicModules/Topology/Algebra/PadicInt.lean)
  applies the generic closure formula to show that its supremum with every
  restricted ideal generated by `2 ^ n` is top. This is not the self-scalar ideal
  of the unit `3`. The [clients](AdicModulesTest/Topology/Algebra/PadicInt.lean)
  gain membership of `1` and the inverse of `3` after adding positive-degree
  neighborhoods, and check closure, properness and the zero and degree-zero
  basis boundaries.

- **Valuation topology, completed integers and spectra.** For a valuation
  domain `V` with fraction field `K`, nonzero `a : V` and separated
  `(a)`-adic topology, the
  [valuation-topology comparison](AdicModules/ValuationTopology.lean) identifies
  the principal-adic and induced valuation topologies. The
  [`V`-algebra equivalence](AdicModules/CompletedIntegers.lean)
  `ValuationRing.principalAdicCompletionEquiv` identifies the principal-adic
  inverse limit with the valuation integers of the completed fraction field;
  it is compatible with the canonical maps and allows independent universes
  for `V` and `K`. The
  [completed-local-structure results](AdicModules/CompletedLocalStructure.lean)
  give a valuation domain whose fraction field is that completed field.
  [Ideal and spectrum results](AdicModules/PrincipalAdicSpectrum.lean) include
  extension-after-contraction for completion ideals and an extended valuation
  comparison; the nonfield, faithful-flatness and prime-spectrum
  order-isomorphism assertions retain the **additional premise** that `a`
  lies in the maximal ideal. No rank-one, discrete or Noetherian hypothesis
  is imposed on these stated results.

- **Localization in one completed fraction field.** For denominators disjoint
  from the radical of `(a)`, the
  [literal images of base-ring powers](AdicModules/LocalizedFiltration.lean)
  are `V`-submodules of the localization, sandwiched between successive
  extended-ideal powers. The filtration supplies the localized topology and,
  assuming principal-adic separatedness, its separation; it is **not** an
  unconditional identity with powers of the extended ideal. Under a nonzero
  generator, radical-disjoint denominators and separatedness, the
  [localized-completion map](AdicModules/LocalizedCompletion.lean) embeds into
  the common completed fraction field. The
  [valuation-subring equivalence](AdicModules/LocalizedValuationSubring.lean)
  and [residue-field comparison](AdicModules/LocalizedResidueField.lean)
  describe that completion and its residue field. For localization at a
  nonzero prime, separatedness supplies radical-disjointness; the
  [quotient valuation subring](AdicModules/LocalizedQuotientValuationSubring.lean)
  uses those prime-specific hypotheses.

- **Literal composite valuations.** The
  [`ValuationSubring.composite`](AdicModules/CompositeValuationSubring.lean)
  is the residue preimage of a valuation subring of the residue field;
  localization at its distinguished prime and quotient by that prime recover
  its two factors. For the completion above, the
  [completed-composite equality](AdicModules/CompletedValuationComposite.lean)
  identifies the completed valuation integers *literally* with the composite
  of the completed localization and its transported residue factor. It does
  not define a new kind of completion.

### Dense-subsemiring span comparison and examples

[`Submodule.closure_span_eq_of_dense_subsemiring`](AdicModules/Topology/Algebra/Module/Span.lean)
identifies the set closures of `Submodule.span A E` and `Submodule.span R E`
for a semiring `R` and an additive commutative monoid `M` with an `R`-module
structure. Here `R` and `M` have independent universes and topologies,
`A : Subsemiring R` is dense, addition on `M` is separately continuous, and
`r ↦ r • m` is continuous **only for each selected `m ∈ E`**. The `A`-action
is the canonical restriction of the same `R`-action on the same `M`.
There is no additive-group, joint-addition, global coefficient-continuity,
`ContinuousSMul`, `T1`, nonempty-generator or finite-generator premise.
For empty `E` or `E = {0}`, both closures are `closure {0}`, not necessarily
`{0}` without separation assumptions. The proof uses the additive-submonoid
closure of the `A`-span, continuous dense images at the generators, and span
induction with the strengthened assertion that every `R`-multiple lies in that
closure. It does not assume scalar invariance of the closure in advance.

The [real-plane and integer-line examples](AdicModulesTest/Topology/Algebra/Module/Span/Real.lean)
and [discrete and mixed-module examples](AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean)
retain original closure calculations independent of the comparison theorem.
The real model also includes an additional private application of
`Submodule.closure_span_eq_of_dense_subsemiring` to the rational axis, identifying
its proper closure and excluding the second coordinate unit. They include a
proper rational-axis closure, a missing-density counterexample, a
missing-coefficient-continuity counterexample, and a proper mixed-axis closure
without global coefficient continuity or joint scalar continuity. The
[p-adic singleton examples](AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean)
apply stock continuous-image closure directly on the canonical `ℤ_[p]` self-module:
units give whole closures, `p` gives the proper closed ideal `p ℤ_[p]`, and
`0` gives `{0}`. The
[boundary examples](AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean)
include empty and zero generators, subsingleton modules, and a nontrivial
indiscrete rational self-module with `closure {0} = univ`. The
[indiscrete-scalar example](AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean)
uses Mathlib's canonical `ULift.{v} ℚ` module with a discrete topology,
independent of indiscrete scalar `ℚ`: integer casts are dense, but the
coefficient map at transported `1` is not continuous. Its closed proper integer
span excludes transported `1 / 2`, while the rational span is whole.
The original span and closure calculations in all five model files are
independent of the generic proof; the real file also contains the additional
private rational-axis application. The
[span-comparison guide](docs/Guide.md#closure-of-spans-over-a-dense-subsemiring)
gives their full model map and mathematical boundaries.

The [mathematical guide](docs/Guide.md) gives the complete current module map,
individual hypotheses, more formulas and import examples. General
nonseparated reduction, arbitrary-denominator localization, value-group
exact sequences, height/rational-rank additivity and whole-source coverage
are **not** claimed here.

## Imports and checks

Import `AdicModules` or, for example, the narrower
`AdicModules.AdicCompletion.RestrictScalars`, `AdicModules.Algebra.Module.Int`,
`AdicModules.RingTheory.Ideal.Operations`, `AdicModules.Topology.Algebra.Ideal`,
`AdicModules.Topology.Algebra.Submodule`,
`AdicModules.Topology.Algebra.Module.Span` or `AdicModules.Topology.Algebra.PadicInt`.
The public root re-exports 21 mathematical source leaves, including the
comaximal-powers theorem, left-ideal density criterion and span-closure comparison.
The separate 28 test/model/audit source modules illustrate downstream use and
contain model calculations and selected statement checks. Together with the
public root, these are **50 tracked Lean source modules**: 22 library sources
including the root and 28 test sources. This is a source-file enumeration, not
a count of mathematical models, compiled modules, kernel declarations or audited
proofs. The complete roster below pairs all 21 library leaves with all 28
test/model/audit sources; the [public root](AdicModules.lean) is the remaining
source. The model files are not re-exported by the public root.

| Library leaf (prefix `AdicModules.`) | Test/audit sources (prefix `AdicModulesTest.`) |
| --- | --- |
| [BoundedIdealPowerTorsion](AdicModules/BoundedIdealPowerTorsion.lean) | [BoundedIdealPowerTorsion](AdicModulesTest/BoundedIdealPowerTorsion.lean) |
| [PrimaryComponent](AdicModules/PrimaryComponent.lean) | [PrimaryComponent](AdicModulesTest/PrimaryComponent.lean) |
| [AdicCompletion](AdicModules/AdicCompletion.lean) | [AdicCompletion](AdicModulesTest/AdicCompletion.lean) |
| [AdicCompletion.RestrictScalars](AdicModules/AdicCompletion/RestrictScalars.lean) | [AdicCompletion.RestrictScalars](AdicModulesTest/AdicCompletion/RestrictScalars.lean) |
| [Algebra.Module.Int](AdicModules/Algebra/Module/Int.lean) | [Algebra.Module.Int](AdicModulesTest/Algebra/Module/Int.lean) |
| [RingTheory.Ideal.Operations](AdicModules/RingTheory/Ideal/Operations.lean) | [RingTheory.Ideal.Operations.MatrixNat](AdicModulesTest/RingTheory/Ideal/Operations/MatrixNat.lean) (independent original calculations; additional private comaximal-powers application) |
| [Topology.Algebra.Ideal](AdicModules/Topology/Algebra/Ideal.lean) | [Topology.Algebra.Ideal.Int](AdicModulesTest/Topology/Algebra/Ideal/Int.lean), [Topology.Algebra.Ideal.Matrix](AdicModulesTest/Topology/Algebra/Ideal/Matrix.lean), [Topology.Algebra.Ideal.Boundary](AdicModulesTest/Topology/Algebra/Ideal/Boundary.lean) (independent original calculations; additional private density application in Int) |
| [Topology.Algebra.Submodule](AdicModules/Topology/Algebra/Submodule.lean) | [Topology.Algebra.SubmoduleClosure](AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean) |
| [Topology.Algebra.PadicInt](AdicModules/Topology/Algebra/PadicInt.lean) | [Topology.Algebra.PadicInt](AdicModulesTest/Topology/Algebra/PadicInt.lean) |
| [Topology.Algebra.Module.Span](AdicModules/Topology/Algebra/Module/Span.lean) | [Topology.Algebra.Module.Span.Real](AdicModulesTest/Topology/Algebra/Module/Span/Real.lean), [Topology.Algebra.Module.Span.Discrete](AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean), [Topology.Algebra.Module.Span.PadicInt](AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean), [Topology.Algebra.Module.Span.Boundary](AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean), [Topology.Algebra.Module.Span.Indiscrete](AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean) (independent original calculations; additional private comparison application in Real) |
| [ValuationTopology](AdicModules/ValuationTopology.lean) | [ValuationTopology](AdicModulesTest/ValuationTopology.lean) |
| [CompletedIntegers](AdicModules/CompletedIntegers.lean) | [CompletedIntegers](AdicModulesTest/CompletedIntegers.lean) |
| [CompletedLocalStructure](AdicModules/CompletedLocalStructure.lean) | [CompletedLocalStructure](AdicModulesTest/CompletedLocalStructure.lean) |
| [PrincipalAdicSpectrum](AdicModules/PrincipalAdicSpectrum.lean) | [PrincipalAdicSpectrum](AdicModulesTest/PrincipalAdicSpectrum.lean) |
| [LocalizedFiltration](AdicModules/LocalizedFiltration.lean) | [LocalizedFiltration](AdicModulesTest/LocalizedFiltration.lean) |
| [LocalizedCompletion](AdicModules/LocalizedCompletion.lean) | [LocalizedCompletion](AdicModulesTest/LocalizedCompletion.lean) |
| [LocalizedValuationSubring](AdicModules/LocalizedValuationSubring.lean) | [LocalizedValuationSubring](AdicModulesTest/LocalizedValuationSubring.lean) |
| [LocalizedResidueField](AdicModules/LocalizedResidueField.lean) | [LocalizedResidueField](AdicModulesTest/LocalizedResidueField.lean) |
| [LocalizedQuotientValuationSubring](AdicModules/LocalizedQuotientValuationSubring.lean) | [LocalizedQuotientValuationSubring](AdicModulesTest/LocalizedQuotientValuationSubring.lean) |
| [CompositeValuationSubring](AdicModules/CompositeValuationSubring.lean) | [CompositeValuationSubring](AdicModulesTest/CompositeValuationSubring.lean) |
| [CompletedValuationComposite](AdicModules/CompletedValuationComposite.lean) | [CompletedValuationComposite](AdicModulesTest/CompletedValuationComposite.lean) |
| No library leaf; aggregate root import | [Axioms](AdicModulesTest/Axioms.lean) (import-only, not an axiom census) |

The [scalar-restriction client](AdicModulesTest/AdicCompletion/RestrictScalars.lean)
also exercises the identity algebra, a polynomial algebra, level zero and
`⊥`/`⊤` ideals. At `⊤` every completion is trivial, including for nonzero
`M`; no nontriviality assumption is hidden in the equivalence.

The completion and valuation leaves also expose characteristic criteria for
inverse comparisons, residue congruence and equality in completed-field
realizations. Their canonical maps can be used through `AdicModules` or the
corresponding narrower library module. Some other test modules separately
expose named concrete results: the ideal generated by `2` remains proper in
its integer adic completion, the bottom-adic polynomial comparison distinguishes `X` from `1`,
and a composite with the whole field as first factor localizes back to that
field. Import the corresponding model module to use those results; the models
are not re-exported by `AdicModules`. In contrast, the four left-ideal model
files keep their declarations private and do not expose a new general theorem
API.

## Build and reference

Install the Lean version pinned in [`lean-toolchain`](lean-toolchain) with
elan. Retain [`lake-manifest.json`](lake-manifest.json) and its mathlib pins;
from the project root fetch the matching cache **successfully before** building:

```sh
lake exe cache get
lake build AdicModules AdicModulesTest
```

The default library targets are `AdicModules` and `AdicModulesTest`; `lake build`
also selects both. The `AdicModulesTest.+` glob includes all 28 separate
test/model/audit files; there is no `AdicModulesTest.lean` aggregate root.
Private verification fixtures may emit private-module advisories by design.
The normal build recipe above does not make warnings fatal. An optional stricter
check of an individual client is, for example,
`lake env lean -DwarningAsError=true AdicModulesTest/AdicCompletion/RestrictScalars.lean`
after the cache fetch; this optional command is not a report of a completed
strict check. Do not silently rebuild mathlib from source when the
matching cache is unavailable. The aggregate
[`Axioms.lean`](AdicModulesTest/Axioms.lean) is import-only and does not perform
an axiom census:
release checks require a successful relevant build and an actual transitive
standard-axiom audit of *all* declarations, including private/generated and
test declarations, permitting only `propext`, `Classical.choice` and
`Quot.sound`. A historical review, generated documentation or selected audit
does not replace revision-specific proof checks; no separate stored-proof replay
is required.

The [historical generated API](docs/API.md) and
[generation notes](docs/README.md) cover 13 mathematical leaves, 28 modules
and 103 display sites at their recorded source revision. They predate the
primary-component, scalar-restriction, integer-singleton-span, submodule-closure,
p-adic, left-ideal and span-comparison leaves and their model files, and are
**not** a current whole-library or complete kernel-declaration inventory. Use the
[primary-component supplement](docs/PrimaryComponent.md),
[scalar-restriction guide](docs/Guide.md#restricting-scalars-in-adic-completions),
[integer-singleton-span guide](docs/Guide.md#integer-singleton-spans-in-unital-rings),
[span-comparison guide](docs/Guide.md#closure-of-spans-over-a-dense-subsemiring),
[submodule-closure module](AdicModules/Topology/Algebra/Submodule.lean),
[left-ideal density guide](docs/Guide.md#left-ideal-density-and-integer-powers-topologies),
[matrix model guide](docs/Guide.md#matrix-left-ideal-models),
[boundary model guide](docs/Guide.md#ideal-power-boundary-models),
[p-adic guide](docs/Guide.md#p-adic-neighborhood-bases-and-integer-spans)
and current Lean files for their signatures.

The [reproduction and resources guide](docs/Guide.md#reproduction-and-resources)
records historical measurements, not a machine-size requirement: the
scalar-restriction CI sample fetched its cache in about 42.509 seconds,
verified it in 6.137 seconds, and built both targets in 41.119 seconds;
its full workflow took about 378 seconds. Lake's 2,737 jobs are not concurrent
processes or all fresh compilations. The earlier readiness sample took about
98 seconds to fetch the cache and 34.020 seconds for an affected build, with
about 12.79 GB total-container memory observed; **no peak RAM** was measured
for the newer 32-module sample. `LEAN_NUM_THREADS=2` limits workers *per Lean
runtime*, not simultaneous Lake processes or total memory. Neither sample is
a cold-machine guarantee or a benchmark of every later revision.

## Credits and scope

Developed and reviewed by Formal Frontier AI agents; **not** a claim of human
peer review, source-author endorsement or complete formalization of any
selected source. This project is distributed under [Apache-2.0](LICENSE),
with upstream Lean/mathlib acknowledgments, the mathematical bibliography and
project-contributor details in [credits and provenance](docs/CREDITS.md).
Source-specific interpretation and coverage decisions live outside this
source-independent library.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I* (2017),
  [arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5).
- [Lean](https://lean-lang.org/), the theorem prover and proof infrastructure
  used by this library.
- [mathlib4](https://github.com/leanprover-community/mathlib4), whose
  formalizations of ideals, modules, adic completions, valuation theory and
  topological algebra this library reuses.

The detailed mathematical bibliography, prior-formalization acknowledgments
and contributor credits are in [credits and provenance](docs/CREDITS.md).
