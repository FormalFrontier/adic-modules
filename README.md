# adic-modules

Authors: Formal Frontier Agents

Lean results on ideal-power torsion, inverse-limit adic completions and valuation
rings. Import `AdicModules` for the public library or an individual module for
a narrower dependency. The library builds on Lean, mathlib's native ideals and
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
`AdicModules.AdicCompletion.RestrictScalars`. The 15 mathematical leaves above
are re-exported by the public root. The separate 16 ordinary-import test/audit
modules illustrate actual downstream use and check selected statements:

| Area | Ordinary-import clients |
| --- | --- |
| Torsion and primary components | [BoundedIdealPowerTorsion](AdicModulesTest/BoundedIdealPowerTorsion.lean), [PrimaryComponent](AdicModulesTest/PrimaryComponent.lean) |
| Adic inverse limits and scalar restriction | [AdicCompletion](AdicModulesTest/AdicCompletion.lean), [RestrictScalars](AdicModulesTest/AdicCompletion/RestrictScalars.lean) |
| Valuation completion and spectra | [ValuationTopology](AdicModulesTest/ValuationTopology.lean), [CompletedIntegers](AdicModulesTest/CompletedIntegers.lean), [CompletedLocalStructure](AdicModulesTest/CompletedLocalStructure.lean), [PrincipalAdicSpectrum](AdicModulesTest/PrincipalAdicSpectrum.lean) |
| Localization and residue | [LocalizedFiltration](AdicModulesTest/LocalizedFiltration.lean), [LocalizedCompletion](AdicModulesTest/LocalizedCompletion.lean), [LocalizedValuationSubring](AdicModulesTest/LocalizedValuationSubring.lean), [LocalizedResidueField](AdicModulesTest/LocalizedResidueField.lean), [LocalizedQuotientValuationSubring](AdicModulesTest/LocalizedQuotientValuationSubring.lean) |
| Composites and selected axioms | [CompositeValuationSubring](AdicModulesTest/CompositeValuationSubring.lean), [CompletedValuationComposite](AdicModulesTest/CompletedValuationComposite.lean), [Axioms](AdicModulesTest/Axioms.lean) |

The [scalar-restriction client](AdicModulesTest/AdicCompletion/RestrictScalars.lean)
also exercises the identity algebra, a polynomial algebra, level zero and
`⊥`/`⊤` ideals. At `⊤` every completion is trivial, including for nonzero
`M`; no nontriviality assumption is hidden in the equivalence.

## Build and reference

Install the Lean version pinned in [`lean-toolchain`](lean-toolchain) with
elan. Retain [`lake-manifest.json`](lake-manifest.json) and its mathlib pins;
from the project root fetch the matching cache **successfully before** building:

```sh
lake exe cache get
lake --wfail build
```

The default build targets both the public library and all 16 test/audit
modules. To check one client with warnings fatal, run, for example,
`lake env lean -DwarningAsError=true AdicModulesTest/AdicCompletion/RestrictScalars.lean`
after the cache fetch. Do not silently rebuild mathlib from source when the
matching cache is unavailable. The selected `#print axioms` in
[`Axioms.lean`](AdicModulesTest/Axioms.lean) is **not** a complete census:
release checks require a successful relevant build and an actual transitive
standard-axiom audit of *all* declarations, including private/generated and
test declarations, permitting only `propext`, `Classical.choice` and
`Quot.sound`. A historical review, generated documentation or selected audit
does not replace revision-specific proof checks; no separate stored-proof replay
is required.

The [historical generated API](docs/API.md) and
[generation notes](docs/README.md) cover 13 mathematical leaves, 28 modules
and 103 display sites at their recorded source revision. They predate the
primary-component and scalar-restriction leaves and are **not** a current
whole-library or complete kernel-declaration inventory. Use the
[primary-component supplement](docs/PrimaryComponent.md),
[scalar-restriction guide](docs/Guide.md#restricting-scalars-in-adic-completions)
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
