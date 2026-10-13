# adic-modules

Authors: Formal Frontier Agents

Lean results on ideal-power torsion, inverse-limit adic completions, integer
singleton spans in unital rings, submodule closure from neighborhood bases,
proper dense integer spans in p-adic integers and valuation rings.
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

The [mathematical guide](docs/Guide.md) gives the complete module map,
individual hypotheses, more formulas and import examples. General
nonseparated reduction, arbitrary-denominator localization, value-group
exact sequences, height/rational-rank additivity and whole-source coverage
are **not** claimed here.

## Imports and checks

Import `AdicModules` or, for example, the narrower
`AdicModules.AdicCompletion.RestrictScalars`, `AdicModules.Algebra.Module.Int`,
`AdicModules.Topology.Algebra.Submodule` or `AdicModules.Topology.Algebra.PadicInt`.
The public root re-exports 18 mathematical source leaves. The separate 19
ordinary-import test/audit source modules illustrate downstream use and contain
selected statement checks. Together with the public root, these are 38 maintained
source modules; this is a source-file enumeration, not a compiled-declaration or
axiom-audit census:

| Area | Ordinary-import clients |
| --- | --- |
| Torsion and primary components | [BoundedIdealPowerTorsion](AdicModulesTest/BoundedIdealPowerTorsion.lean), [PrimaryComponent](AdicModulesTest/PrimaryComponent.lean) |
| Adic inverse limits and scalar restriction | [AdicCompletion](AdicModulesTest/AdicCompletion.lean), [RestrictScalars](AdicModulesTest/AdicCompletion/RestrictScalars.lean) |
| Integer singleton spans | [IntSpan](AdicModulesTest/Algebra/Module/Int.lean) |
| Submodule closure and p-adic integer spans | [SubmoduleClosure](AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean), [PadicInt](AdicModulesTest/Topology/Algebra/PadicInt.lean) |
| Valuation completion and spectra | [ValuationTopology](AdicModulesTest/ValuationTopology.lean), [CompletedIntegers](AdicModulesTest/CompletedIntegers.lean), [CompletedLocalStructure](AdicModulesTest/CompletedLocalStructure.lean), [PrincipalAdicSpectrum](AdicModulesTest/PrincipalAdicSpectrum.lean) |
| Localization and residue | [LocalizedFiltration](AdicModulesTest/LocalizedFiltration.lean), [LocalizedCompletion](AdicModulesTest/LocalizedCompletion.lean), [LocalizedValuationSubring](AdicModulesTest/LocalizedValuationSubring.lean), [LocalizedResidueField](AdicModulesTest/LocalizedResidueField.lean), [LocalizedQuotientValuationSubring](AdicModulesTest/LocalizedQuotientValuationSubring.lean) |
| Composites and aggregate import | [CompositeValuationSubring](AdicModulesTest/CompositeValuationSubring.lean), [CompletedValuationComposite](AdicModulesTest/CompletedValuationComposite.lean), [Axioms](AdicModulesTest/Axioms.lean) |

The [scalar-restriction client](AdicModulesTest/AdicCompletion/RestrictScalars.lean)
also exercises the identity algebra, a polynomial algebra, level zero and
`⊥`/`⊤` ideals. At `⊤` every completion is trivial, including for nonzero
`M`; no nontriviality assumption is hidden in the equivalence.

The completion and valuation leaves also expose characteristic criteria for
inverse comparisons, residue congruence and equality in completed-field
realizations. Their canonical maps can be used through `AdicModules` or the
corresponding narrower library module. The model modules separately expose named
concrete results: the ideal generated by `2` remains proper in its integer adic
completion, the bottom-adic polynomial comparison distinguishes `X` from `1`,
and a composite with the whole field as first factor localizes back to that
field. Import the corresponding model module to use those results; the models
are not re-exported by `AdicModules`.

## Build and reference

Install the Lean version pinned in [`lean-toolchain`](lean-toolchain) with
elan. Retain [`lake-manifest.json`](lake-manifest.json) and its mathlib pins;
from the project root fetch the matching cache **successfully before** building:

```sh
lake exe cache get
lake --wfail build
```

The default build targets both the public library and all 19 test/audit
source modules. To check one client with warnings fatal, run, for example,
`lake env lean -DwarningAsError=true AdicModulesTest/AdicCompletion/RestrictScalars.lean`
after the cache fetch. Do not silently rebuild mathlib from source when the
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
primary-component, scalar-restriction, integer-singleton-span, submodule-closure
and p-adic leaves and are **not** a current whole-library or complete
kernel-declaration inventory. Use the
[primary-component supplement](docs/PrimaryComponent.md),
[scalar-restriction guide](docs/Guide.md#restricting-scalars-in-adic-completions),
[integer-singleton-span guide](docs/Guide.md#integer-singleton-spans-in-unital-rings),
[submodule-closure module](AdicModules/Topology/Algebra/Submodule.lean),
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
